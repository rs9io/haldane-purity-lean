// Exact __int128 Chebyshev trace enclosure engine for Spin-1 XXZ + D*(S^z)^2 (Delta=1, D=1/4).
// Supports seams: I (theta=0), Rz (theta=pi), R4 (theta=pi/2) in the S^z basis,
// computing BOTH b=31/2 and b=23 simultaneously in a single Chebyshev pass with
// 100% pure integer arithmetic (zero floating point) and exact 256-bit squared-norm totals.
//
// Compile: clang++ -O3 -std=c++20 -pthread scripts/chebyshev_enclose.cpp -o scripts/chebyshev_enclose

#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

using i128 = __int128_t;
using u128 = __uint128_t;

// Exact floor division of signed __int128 by positive int64_t d.
static inline i128 floor_div(i128 a, int64_t d) {
    i128 q = a / d;
    i128 r = a % d;
    if (r < 0) --q;
    return q;
}

// Exact floor((c * v) / 2^60) where 0 <= c <= 2^60 and |v| < 2^86, zero overflow!
static inline i128 mul_shr60(uint64_t c, i128 v) {
    const i128 mask = (((i128)1) << 60) - 1;
    i128 v_lo = v & mask;          // in [0, 2^60 - 1] (two's complement!)
    i128 v_hi = (v - v_lo) >> 60;  // exact floor(v / 2^60), |v_hi| < 2^26
    u128 prod_lo = (u128)c * (u128)v_lo; // < 2^120
    return (i128)c * v_hi + (i128)(prod_lo >> 60);
}

// Exact 256-bit unsigned integer for squared-norm accumulation W = sum nu_r * ||y_r||_2^2.
struct U256 {
    uint64_t w[4] = {0, 0, 0, 0};

    void add_u128_prod(u128 a, u128 b) {
        // Compute a * b (up to 256 bits) and add to *this.
        uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64);
        uint64_t b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);
        u128 p00 = (u128)a0 * b0;
        u128 p01 = (u128)a0 * b1;
        u128 p10 = (u128)a1 * b0;
        u128 p11 = (u128)a1 * b1;

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
        for (int i = 0; i < 4; ++i) {
            c += (u128)w[i] + o.w[i];
            w[i] = (uint64_t)c;
            c >>= 64;
        }
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

static inline u128 abs_i128(i128 x) {
    return x < 0 ? (u128)(-(x + 1)) + 1 : (u128)x;
}

struct OrbitRep {
    uint32_t local_idx;
    uint32_t mult;
};

struct BlockData {
    int M;
    uint32_t dim;
    std::vector<uint32_t> states; // base-3 code of each state
    std::vector<int32_t> diag;    // diagonal of M_int = (16*W - E_num*n) - 16*H_diag
    std::vector<uint32_t> row_ptr;
    std::vector<uint32_t> col_idx;
    std::vector<int8_t> hop_type; // 0: -16 (real), 1: +16 (real), 2: +16i, 3: -16i
    std::vector<OrbitRep> reps;
};

static void encode_digits(uint32_t code, int n, uint8_t* d) {
    for (int j = 0; j < n; ++j) {
        d[j] = code % 3;
        code /= 3;
    }
}

static uint32_t decode_digits(const uint8_t* d, int n, const uint32_t* pw) {
    uint32_t code = 0;
    for (int j = 0; j < n; ++j) code += d[j] * pw[j];
    return code;
}

static BlockData build_block(int n, int M, int seam, int E_num, int W,
                             const uint32_t* pw, std::vector<int32_t>& global_to_local) {
    // seam: 0 = I, 1 = Rz(pi), 2 = R4 = Rz(pi/2)
    BlockData blk;
    blk.M = M;
    uint32_t total = pw[n];
    uint8_t d[16];

    for (uint32_t code = 0; code < total; ++code) {
        uint32_t x = code;
        int sum = 0;
        for (int j = 0; j < n; ++j) {
            int dig = x % 3;
            x /= 3;
            sum += (dig - 1);
        }
        if (sum == M) {
            global_to_local[code] = (int32_t)blk.states.size();
            blk.states.push_back(code);
        }
    }
    blk.dim = (uint32_t)blk.states.size();
    blk.diag.resize(blk.dim);
    blk.row_ptr.resize(blk.dim + 1);
    blk.col_idx.reserve((size_t)blk.dim * (size_t)(n + 2));
    blk.hop_type.reserve((size_t)blk.dim * (size_t)(n + 2));

    const int32_t base_shift = 16 * W - E_num * n;
    for (uint32_t i = 0; i < blk.dim; ++i) {
        uint32_t code = blk.states[i];
        encode_digits(code, n, d);
        int zz = 0, sz2 = 0;
        for (int j = 0; j < n; ++j) {
            int s1 = (int)d[j] - 1;
            int s2 = (int)d[(j + 1) % n] - 1;
            zz += s1 * s2;
            sz2 += s1 * s1;
        }
        blk.diag[i] = base_shift - 16 * zz - 4 * sz2;
        blk.row_ptr[i] = (uint32_t)blk.col_idx.size();
        for (int j = 0; j < n; ++j) {
            int k = (j + 1) % n;
            bool is_seam = (j == n - 1);
            // delta = +1: d[j] -> d[j]+1 (S^+_j), d[k] -> d[k]-1 (S^-_k)
            if (d[j] < 2 && d[k] > 0) {
                uint32_t dst_code = code + pw[j] - pw[k];
                int32_t dst = global_to_local[dst_code];
                assert(dst >= 0);
                blk.col_idx.push_back((uint32_t)dst);
                // M_int = ... - 16 * H_n. For S^+_{n-1} S^-_0: H_entry = e^{-i theta}
                // theta=0: -16 (type 0); theta=pi: +16 (type 1); theta=pi/2: -16*(-i) = +16i (type 2)
                int8_t ht = 0;
                if (is_seam) {
                    if (seam == 1) ht = 1;
                    else if (seam == 2) ht = 2;
                }
                blk.hop_type.push_back(ht);
            }
            // delta = -1: d[j] -> d[j]-1 (S^-_j), d[k] -> d[k]+1 (S^+_k)
            if (d[j] > 0 && d[k] < 2) {
                uint32_t dst_code = code - pw[j] + pw[k];
                int32_t dst = global_to_local[dst_code];
                assert(dst >= 0);
                blk.col_idx.push_back((uint32_t)dst);
                int8_t ht = 0;
                if (is_seam) {
                    if (seam == 1) ht = 1;
                    else if (seam == 2) ht = 3; // -16*(+i) = -16i
                }
                blk.hop_type.push_back(ht);
            }
        }
    }
    blk.row_ptr[blk.dim] = (uint32_t)blk.col_idx.size();

    // Build orbit representatives under cyclic shift + reversal (+ negation when M == 0).
    std::vector<uint8_t> visited(blk.dim, 0);
    uint8_t tmp[16];
    std::vector<uint32_t> orb;
    orb.reserve(4 * n);
    for (uint32_t i = 0; i < blk.dim; ++i) {
        if (visited[i]) continue;
        encode_digits(blk.states[i], n, d);
        orb.clear();
        int neg_max = (M == 0) ? 2 : 1;
        for (int neg = 0; neg < neg_max; ++neg) {
            for (int rev = 0; rev < 2; ++rev) {
                for (int sh = 0; sh < n; ++sh) {
                    for (int j = 0; j < n; ++j) {
                        int idx = rev ? ((n - 1 - j + sh) % n) : ((j + sh) % n);
                        uint8_t dig = d[idx];
                        if (neg) dig = 2 - dig;
                        tmp[j] = dig;
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
        }
        uint32_t mult = (uint32_t)orb.size() * (M > 0 ? 2u : 1u);
        blk.reps.push_back({i, mult});
    }

    // Clear global_to_local entries used by this block
    for (uint32_t code : blk.states) global_to_local[code] = -1;
    return blk;
}

int main(int argc, char** argv) {
    // Usage: chebyshev_enclose <n> <seam:0=I,1=Rz,2=R4> <E_num> <W> <K> <Q_bits> <threads> <coeff_file>
    // coeff_file has K+1 lines: c_k_b1 c_k_b2 (uint64 integers scaled by 2^60).
    if (argc < 9) {
        std::fprintf(stderr, "Usage: %s n seam E_num W K Q_bits threads coeff_file [M_filter]\n", argv[0]);
        return 1;
    }
    int n = std::atoi(argv[1]);
    int seam = std::atoi(argv[2]);
    int E_num = std::atoi(argv[3]);
    int W = std::atoi(argv[4]);
    int K = std::atoi(argv[5]);
    int Q_bits = std::atoi(argv[6]);
    int nthreads = std::atoi(argv[7]);
    const char* coeff_path = argv[8];
    int M_filter = (argc >= 10) ? std::atoi(argv[9]) : -1;

    std::vector<uint64_t> c1(K + 1), c2(K + 1);
    FILE* cf = std::fopen(coeff_path, "r");
    if (!cf) { std::perror("fopen coeff_file"); return 1; }
    for (int k = 0; k <= K; ++k) {
        unsigned long long a = 0, b = 0;
        if (std::fscanf(cf, "%llu %llu", &a, &b) != 2) {
            std::fprintf(stderr, "Failed reading coeff %d\n", k);
            return 1;
        }
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
    const bool is_complex = (seam == 2);

    U256 total_W1, total_W2;
    uint64_t total_mult = 0;

    for (int M = 0; M <= n; ++M) {
        if (M_filter >= 0 && M != M_filter) continue;
        BlockData blk = build_block(n, M, seam, E_num, W, pw, global_to_local);
        uint64_t blk_mult = 0;
        for (auto& r : blk.reps) blk_mult += r.mult;
        total_mult += blk_mult;

        const uint32_t dim = blk.dim;
        const size_t nreps = blk.reps.size();
        std::atomic<size_t> next_rep{0};
        std::vector<U256> thr_W1(nthreads), thr_W2(nthreads);

        auto worker = [&](int tid) {
            if (!is_complex) {
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

                    // k = 1: v1 = floor(M_int * v0 / (16*W))
                    if (K >= 1) {
                        std::fill(v1.begin(), v1.end(), (i128)0);
                        v1[r] = floor_div((i128)blk.diag[r] * Q, div1);
                        for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                            uint32_t j = blk.col_idx[e];
                            int64_t val = (blk.hop_type[e] == 1) ? 16 : -16;
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

                    // k = 2..K: v2 = floor(M_int * v1 / (8*W)) - v0
                    for (int k = 2; k <= K; ++k) {
                        uint64_t ck1 = c1[k], ck2 = c2[k];
                        for (uint32_t i = 0; i < dim; ++i) {
                            i128 acc = (i128)blk.diag[i] * v1[i];
                            uint32_t start = blk.row_ptr[i], end = blk.row_ptr[i + 1];
                            for (uint32_t e = start; e < end; ++e) {
                                i128 vj = v1[blk.col_idx[e]];
                                acc += (blk.hop_type[e] == 1) ? (vj << 4) : -(vj << 4);
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
            } else {
                // Complex Gaussian-integer Z[i] for R4 = Rz(pi/2)
                std::vector<i128> v0r(dim), v0i(dim), v1r(dim), v1i(dim), v2r(dim), v2i(dim);
                std::vector<i128> y1r(dim), y1i(dim), y2r(dim), y2i(dim);
                while (true) {
                    size_t idx = next_rep.fetch_add(1, std::memory_order_relaxed);
                    if (idx >= nreps) break;
                    uint32_t r = blk.reps[idx].local_idx;
                    uint32_t mult = blk.reps[idx].mult;

                    std::fill(v0r.begin(), v0r.end(), (i128)0);
                    std::fill(v0i.begin(), v0i.end(), (i128)0);
                    std::fill(y1r.begin(), y1r.end(), (i128)0);
                    std::fill(y1i.begin(), y1i.end(), (i128)0);
                    std::fill(y2r.begin(), y2r.end(), (i128)0);
                    std::fill(y2i.begin(), y2i.end(), (i128)0);
                    v0r[r] = Q;
                    y1r[r] = mul_shr60(c1[0], Q);
                    y2r[r] = mul_shr60(c2[0], Q);

                    if (K >= 1) {
                        std::fill(v1r.begin(), v1r.end(), (i128)0);
                        std::fill(v1i.begin(), v1i.end(), (i128)0);
                        v1r[r] = floor_div((i128)blk.diag[r] * Q, div1);
                        for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                            uint32_t j = blk.col_idx[e];
                            int8_t ht = blk.hop_type[e];
                            // Note: M_int is Hermitian, so column r entry at row j is conj(row r entry at col j)!
                            // Row r col j has hop_type ht: 0 -> -16, 2 -> +16i (so col r row j = -16i), 3 -> -16i (so col r row j = +16i).
                            if (ht == 0) v1r[j] = floor_div(-(Q << 4), div1);
                            else if (ht == 2) v1i[j] = floor_div(-(Q << 4), div1);
                            else if (ht == 3) v1i[j] = floor_div(+(Q << 4), div1);
                        }
                        if (c1[1]) {
                            y1r[r] += mul_shr60(c1[1], v1r[r]);
                            for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                                uint32_t j = blk.col_idx[e];
                                y1r[j] += mul_shr60(c1[1], v1r[j]);
                                y1i[j] += mul_shr60(c1[1], v1i[j]);
                            }
                        }
                        if (c2[1]) {
                            y2r[r] += mul_shr60(c2[1], v1r[r]);
                            for (uint32_t e = blk.row_ptr[r]; e < blk.row_ptr[r + 1]; ++e) {
                                uint32_t j = blk.col_idx[e];
                                y2r[j] += mul_shr60(c2[1], v1r[j]);
                                y2i[j] += mul_shr60(c2[1], v1i[j]);
                            }
                        }
                    }

                    for (int k = 2; k <= K; ++k) {
                        uint64_t ck1 = c1[k], ck2 = c2[k];
                        for (uint32_t i = 0; i < dim; ++i) {
                            i128 ar = (i128)blk.diag[i] * v1r[i];
                            i128 ai = (i128)blk.diag[i] * v1i[i];
                            uint32_t start = blk.row_ptr[i], end = blk.row_ptr[i + 1];
                            for (uint32_t e = start; e < end; ++e) {
                                uint32_t j = blk.col_idx[e];
                                int8_t ht = blk.hop_type[e];
                                i128 xr = v1r[j], xi = v1i[j];
                                if (ht == 0) {
                                    ar -= (xr << 4);
                                    ai -= (xi << 4);
                                } else if (ht == 2) {
                                    // (+16i) * (xr + i xi) = -16 xi + i * 16 xr
                                    ar -= (xi << 4);
                                    ai += (xr << 4);
                                } else { // ht == 3: (-16i) * (xr + i xi) = +16 xi - i * 16 xr
                                    ar += (xi << 4);
                                    ai -= (xr << 4);
                                }
                            }
                            i128 nvr = floor_div(ar, div2) - v0r[i];
                            i128 nvi = floor_div(ai, div2) - v0i[i];
                            v2r[i] = nvr;
                            v2i[i] = nvi;
                            if (ck1) {
                                y1r[i] += mul_shr60(ck1, nvr);
                                y1i[i] += mul_shr60(ck1, nvi);
                            }
                            if (ck2) {
                                y2r[i] += mul_shr60(ck2, nvr);
                                y2i[i] += mul_shr60(ck2, nvi);
                            }
                        }
                        v0r.swap(v1r); v0i.swap(v1i);
                        v1r.swap(v2r); v1i.swap(v2i);
                    }

                    U256 n1, n2;
                    for (uint32_t i = 0; i < dim; ++i) {
                        u128 r1 = abs_i128(y1r[i]), i1 = abs_i128(y1i[i]);
                        if (r1) n1.add_u128_prod(r1, r1);
                        if (i1) n1.add_u128_prod(i1, i1);
                        u128 r2 = abs_i128(y2r[i]), i2 = abs_i128(y2i[i]);
                        if (r2) n2.add_u128_prod(r2, r2);
                        if (i2) n2.add_u128_prod(i2, i2);
                    }
                    thr_W1[tid].add_scaled_u256(mult, n1);
                    thr_W2[tid].add_scaled_u256(mult, n2);
                }
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
        std::fprintf(stderr, "  M=%2d dim=%7u reps=%6zu mult=%8llu W1=%s\n",
                     M, dim, nreps, (unsigned long long)blk_mult, blk_W1.to_dec().c_str());
    }

    if (M_filter < 0) assert(total_mult == pw[n]);
    std::printf("TOTAL n=%d seam=%d mult=%llu\nW1=%s\nW2=%s\n",
                n, seam, (unsigned long long)total_mult,
                total_W1.to_dec().c_str(), total_W2.to_dec().c_str());
    return 0;
}
