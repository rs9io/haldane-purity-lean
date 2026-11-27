// Exact __int128 Chebyshev trace enclosure engine for Spin-1 (Delta=1, D=1/4), Rx(pi) seam.
// Uses the real Cartesian basis {|x>=0, |y>=1, |z>=2}, 4 exact D2-parity blocks,
// cyclic-shift + reversal orbit reduction (exact factor 2*n), and 100% pure __int128 arithmetic.
//
// Compile: clang++ -O3 -std=c++20 -pthread scripts/chebyshev_enclose_rx.cpp -o scripts/chebyshev_enclose_rx

#include <algorithm>
#include <atomic>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>

using i128 = __int128_t;
using u128 = __uint128_t;

static inline i128 floor_div(i128 a, int64_t d) {
    i128 q = a / d;
    i128 r = a % d;
    if (r < 0) --q;
    return q;
}

static inline i128 mul_shr60(uint64_t c, i128 v) {
    const i128 mask = (((i128)1) << 60) - 1;
    i128 v_lo = v & mask;
    i128 v_hi = (v - v_lo) >> 60;
    u128 prod_lo = (u128)c * (u128)v_lo;
    return (i128)c * v_hi + (i128)(prod_lo >> 60);
}

struct U256 {
    uint64_t w[4] = {0, 0, 0, 0};
    void add_u128_prod(u128 a, u128 b) {
        uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64);
        uint64_t b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);
        u128 p00 = (u128)a0 * b0, p01 = (u128)a0 * b1, p10 = (u128)a1 * b0, p11 = (u128)a1 * b1;
        u128 c = (u128)w[0] + (uint64_t)p00;
        w[0] = (uint64_t)c;
        c = (c >> 64) + w[1] + (p00 >> 64) + (uint64_t)p01 + (uint64_t)p10;
        w[1] = (uint64_t)c;
        c = (c >> 64) + w[2] + (p01 >> 64) + (p10 >> 64) + (uint64_t)p11;
        w[2] = (uint64_t)c;
        c = (c >> 64) + w[3] + (p11 >> 64);
        w[3] = (uint64_t)c;
    }
    void add_u256(const U256& o) {
        u128 c = 0;
        for (int i = 0; i < 4; ++i) { c += (u128)w[i] + o.w[i]; w[i] = (uint64_t)c; c >>= 64; }
    }
    void add_scaled_u256(uint64_t mult, const U256& o) {
        u128 c = 0;
        for (int i = 0; i < 4; ++i) {
            u128 p = (u128)mult * o.w[i];
            u128 s = (u128)w[i] + (uint64_t)p + (uint64_t)c;
            w[i] = (uint64_t)s;
            c = (p >> 64) + (c >> 64) + (s >> 64);
        }
    }
    std::string to_dec() const {
        uint64_t tmp[4] = {w[0], w[1], w[2], w[3]};
        std::string out;
        while (tmp[0] || tmp[1] || tmp[2] || tmp[3]) {
            u128 rem = 0;
            for (int i = 3; i >= 0; --i) {
                u128 cur = (rem << 64) | tmp[i];
                tmp[i] = (uint64_t)(cur / 1000000000ULL);
                rem = cur % 1000000000ULL;
            }
            char buf[16];
            if (tmp[0] || tmp[1] || tmp[2] || tmp[3])
                std::snprintf(buf, sizeof(buf), "%09llu", (unsigned long long)rem);
            else
                std::snprintf(buf, sizeof(buf), "%llu", (unsigned long long)rem);
            out = std::string(buf) + out;
        }
        return out.empty() ? "0" : out;
    }
};

static inline u128 abs_i128(i128 x) { return x < 0 ? (u128)(-(x + 1)) + 1 : (u128)x; }

struct OrbitRep { uint32_t local_idx; uint32_t mult; };

struct BlockData {
    int sec;
    uint32_t dim;
    std::vector<uint32_t> states;
    std::vector<int32_t> diag;
    std::vector<uint32_t> row_ptr;
    std::vector<uint32_t> col_idx;
    std::vector<int8_t> hop_sign; // +1 means +16 in M_int, -1 means -16 in M_int
    std::vector<OrbitRep> reps;
};

static void encode_digits(uint32_t code, int n, uint8_t* d) {
    for (int j = 0; j < n; ++j) { d[j] = code % 3; code /= 3; }
}
static uint32_t decode_digits(const uint8_t* d, int n, const uint32_t* pw) {
    uint32_t code = 0;
    for (int j = 0; j < n; ++j) code += d[j] * pw[j];
    return code;
}

static BlockData build_block_rx(int n, int sec, int E_num, int W,
                                const uint32_t* pw, std::vector<int32_t>& global_to_local) {
    // sec in {0, 1, 2, 3}: bit0 = (#x mod 2), bit1 = (#y mod 2).
    BlockData blk;
    blk.sec = sec;
    uint32_t total = pw[n];
    uint8_t d[16];

    for (uint32_t code = 0; code < total; ++code) {
        uint32_t x = code;
        int cx = 0, cy = 0;
        for (int j = 0; j < n; ++j) {
            int dig = x % 3; x /= 3;
            if (dig == 0) cx ^= 1;
            else if (dig == 1) cy ^= 1;
        }
        if ((cx | (cy << 1)) == sec) {
            global_to_local[code] = (int32_t)blk.states.size();
            blk.states.push_back(code);
        }
    }
    blk.dim = (uint32_t)blk.states.size();
    blk.diag.resize(blk.dim);
    blk.row_ptr.resize(blk.dim + 1);
    blk.col_idx.reserve((size_t)blk.dim * (size_t)(2 * n));
    blk.hop_sign.reserve((size_t)blk.dim * (size_t)(2 * n));

    const int32_t base_shift = 16 * W - E_num * n;
    for (uint32_t i = 0; i < blk.dim; ++i) {
        uint32_t code = blk.states[i];
        encode_digits(code, n, d);
        int sz2 = 0;
        for (int j = 0; j < n; ++j) if (d[j] != 2) ++sz2;
        // Diagonal of H_n is 0.25 * sz2, so M_int = (16*W - E_num*n) - 4*sz2
        blk.diag[i] = base_shift - 4 * sz2;
        blk.row_ptr[i] = (uint32_t)blk.col_idx.size();
        for (int j = 0; j < n; ++j) {
            int k = (j + 1) % n;
            bool is_seam = (j == n - 1);
            uint8_t a = d[j], b = d[k];
            if (a == b) {
                // Two axes flip (a, a) -> (v, v) for the two letters v != a.
                // Axis is the third letter `ax = 3 - a - v`.
                // H entry is -sg(ax), so M_int = -16*H entry is +16*sg(ax).
                for (uint8_t v = 0; v < 3; ++v) {
                    if (v == a) continue;
                    int ax = 3 - (int)a - (int)v;
                    int sg = (is_seam && ax != 0) ? -1 : 1; // Rx(pi): axis 0 -> +1, axis 1,2 -> -1
                    uint32_t dst_code = code + (int)(v - a) * (int)pw[j] + (int)(v - a) * (int)pw[k];
                    int32_t dst = global_to_local[dst_code];
                    assert(dst >= 0);
                    blk.col_idx.push_back((uint32_t)dst);
                    blk.hop_sign.push_back((int8_t)sg); // +sg in M_int (since H has -sg)
                }
            } else {
                // Swap (a, b) -> (b, a): axis is the third letter `ax = 3 - a - b`.
                // H entry is +sg(ax), so M_int = -16*H entry is -16*sg(ax).
                int ax = 3 - (int)a - (int)b;
                int sg = (is_seam && ax != 0) ? -1 : 1;
                uint32_t dst_code = code + (int)(b - a) * (int)pw[j] + (int)(a - b) * (int)pw[k];
                int32_t dst = global_to_local[dst_code];
                assert(dst >= 0);
                blk.col_idx.push_back((uint32_t)dst);
                blk.hop_sign.push_back((int8_t)(-sg)); // -sg in M_int (since H has +sg)
            }
        }
    }
    blk.row_ptr[blk.dim] = (uint32_t)blk.col_idx.size();

    // Orbits under cyclic shifts + word reversal (all stay inside same D2 block!).
    std::vector<uint8_t> visited(blk.dim, 0);
    uint8_t tmp[16];
    std::vector<uint32_t> orb;
    orb.reserve(2 * n);
    for (uint32_t i = 0; i < blk.dim; ++i) {
        if (visited[i]) continue;
        encode_digits(blk.states[i], n, d);
        orb.clear();
        for (int rev = 0; rev < 2; ++rev) {
            for (int sh = 0; sh < n; ++sh) {
                for (int j = 0; j < n; ++j) {
                    int idx = rev ? ((n - 1 - j + sh) % n) : ((j + sh) % n);
                    tmp[j] = d[idx];
                }
                uint32_t c = decode_digits(tmp, n, pw);
                int32_t loc = global_to_local[c];
                assert(loc >= 0);
                if (!visited[loc]) {
                    visited[loc] = 1;
                    orb.push_back((uint32_t)loc);
                }
            }
        }
        blk.reps.push_back({i, (uint32_t)orb.size()});
    }

    for (uint32_t code : blk.states) global_to_local[code] = -1;
    return blk;
}

int main(int argc, char** argv) {
    if (argc < 8) {
        std::fprintf(stderr, "Usage: %s n E_num W K Q_bits threads coeff_file [sec_filter]\n", argv[0]);
        return 1;
    }
    int n = std::atoi(argv[1]);
    int E_num = std::atoi(argv[2]);
    int W = std::atoi(argv[3]);
    int K = std::atoi(argv[4]);
    int Q_bits = std::atoi(argv[5]);
    int nthreads = std::atoi(argv[6]);
    const char* coeff_path = argv[7];
    int sec_filter = (argc >= 9) ? std::atoi(argv[8]) : -1;

    std::vector<uint64_t> c1(K + 1), c2(K + 1);
    FILE* cf = std::fopen(coeff_path, "r");
    if (!cf) { std::perror("fopen coeff_file"); return 1; }
    for (int k = 0; k <= K; ++k) {
        unsigned long long a = 0, b = 0;
        if (std::fscanf(cf, "%llu %llu", &a, &b) != 2) return 1;
        c1[k] = a; c2[k] = b;
    }
    std::fclose(cf);

    uint32_t pw[16];
    pw[0] = 1;
    for (int j = 1; j <= n; ++j) pw[j] = pw[j - 1] * 3u;
    std::vector<int32_t> global_to_local(pw[n], -1);

    const i128 Q = ((i128)1) << Q_bits;
    const int64_t div1 = 16LL * W;
    const int64_t div2 = 8LL * W;

    U256 total_W1, total_W2;
    uint64_t total_mult = 0;

    for (int sec = 0; sec < 4; ++sec) {
        if (sec_filter >= 0 && sec != sec_filter) continue;
        BlockData blk = build_block_rx(n, sec, E_num, W, pw, global_to_local);
        uint64_t blk_mult = 0;
        for (auto& r : blk.reps) blk_mult += r.mult;
        total_mult += blk_mult;

        const uint32_t dim = blk.dim;
        const size_t nreps = blk.reps.size();
        std::atomic<size_t> next_rep{0};
        std::vector<U256> thr_W1(nthreads), thr_W2(nthreads);

        auto worker = [&](int tid) {
            std::vector<i128> v0(dim), v1(dim), v2(dim), y1(dim), y2(dim);
            while (true) {
                size_t idx = next_rep.fetch_add(1, std::memory_order_relaxed);
                if (idx >= nreps) break;
                uint32_t r = blk.reps[idx].local_idx;
                uint32_t mult = blk.reps[idx].mult;

                std::fill(v0.begin(), v0.end(), (i128)0);
                std::fill(y1.begin(), y1.end(), (i128)0);
                std::fill(y2.begin(), y2.end(), (i128)0);
                v0[r] = Q;
                y1[r] = mul_shr60(c1[0], Q);
                y2[r] = mul_shr60(c2[0], Q);

                if (K >= 1) {
                    std::fill(v1.begin(), v1.end(), (i128)0);
                    v1[r] = floor_div((i128)blk.diag[r] * Q, div1);
                    for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                        uint32_t j = blk.col_idx[e];
                        int64_t val = (blk.hop_sign[e] > 0) ? 16 : -16;
                        v1[j] = floor_div((i128)val * Q, div1);
                    }
                    if (c1[1]) {
                        y1[r] += mul_shr60(c1[1], v1[r]);
                        for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                            uint32_t j = blk.col_idx[e];
                            y1[j] += mul_shr60(c1[1], v1[j]);
                        }
                    }
                    if (c2[1]) {
                        y2[r] += mul_shr60(c2[1], v1[r]);
                        for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                            uint32_t j = blk.col_idx[e];
                            y2[j] += mul_shr60(c2[1], v1[j]);
                        }
                    }
                }

                for (int k = 2; k <= K; ++k) {
                    uint64_t ck1 = c1[k], ck2 = c2[k];
                    for (uint32_t i = 0; i < dim; ++i) {
                        i128 acc = (i128)blk.diag[i] * v1[i];
                        uint32_t start = blk.row_ptr[i], end = blk.row_ptr[i + 1];
                        for (uint32_t e = start; e < end; ++e) {
                            i128 vj = v1[blk.col_idx[e]];
                            acc += (blk.hop_sign[e] > 0) ? (vj << 4) : -(vj << 4);
                        }
                        i128 nv = floor_div(acc, div2) - v0[i];
                        v2[i] = nv;
                        if (ck1) y1[i] += mul_shr60(ck1, nv);
                        if (ck2) y2[i] += mul_shr60(ck2, nv);
                    }
                    v0.swap(v1);
                    v1.swap(v2);
                }

                U256 n1, n2;
                for (uint32_t i = 0; i < dim; ++i) {
                    u128 a1 = abs_i128(y1[i]);
                    if (a1) n1.add_u128_prod(a1, a1);
                    u128 a2 = abs_i128(y2[i]);
                    if (a2) n2.add_u128_prod(a2, a2);
                }
                thr_W1[tid].add_scaled_u256(mult, n1);
                thr_W2[tid].add_scaled_u256(mult, n2);
            }
        };

        std::vector<std::thread> threads;
        int used_threads = std::min(nthreads, (int)std::max<size_t>(1, nreps));
        for (int t = 0; t < used_threads; ++t) threads.emplace_back(worker, t);
        for (auto& th : threads) th.join();

        U256 blk_W1, blk_W2;
        for (int t = 0; t < used_threads; ++t) {
            blk_W1.add_u256(thr_W1[t]);
            blk_W2.add_u256(thr_W2[t]);
        }
        total_W1.add_u256(blk_W1);
        total_W2.add_u256(blk_W2);
        std::fprintf(stderr, "  sec=%d dim=%7u reps=%6zu mult=%8llu W1=%s\n",
                     sec, dim, nreps, (unsigned long long)blk_mult, blk_W1.to_dec().c_str());
    }

    if (sec_filter < 0) assert(total_mult == pw[n]);
    std::printf("TOTAL n=%d seam=Rx mult=%llu\nW1=%s\nW2=%s\n",
                n, (unsigned long long)total_mult,
                total_W1.to_dec().c_str(), total_W2.to_dec().c_str());
    return 0;
}
