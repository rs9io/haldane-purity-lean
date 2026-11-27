// Exact 128-bit integer (I128) multi-GPU CUDA Chebyshev trace enclosure engine
// for Spin-1 XXZ + D*(S^z)^2 (Delta=1, D=1/4), covering ALL 4 seams:
//   seam=0: I (S^z basis, real)
//   seam=1: Rz(pi) (S^z basis, real)
//   seam=2: R4 = Rz(pi/2) (S^z basis, Gaussian integers Z[i])
//   seam=3: Rx(pi) (Cartesian basis, 4 D2-parity blocks, real)
//
// 100% pure integer arithmetic, bit-for-bit identical to scripts/chebyshev_enclose.cpp
// and scripts/chebyshev_enclose_rx.cpp (verified via exact 256-bit integer totals W1, W2).
//
// Compile: nvcc -O3 -std=c++17 -arch=native scripts/chebyshev_enclose_cuda.cu -o scripts/chebyshev_enclose_cuda

#include <cuda_runtime.h>
#include <algorithm>
#include <atomic>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>

#define CUDA_CHECK(call) do { \
    cudaError_t err__ = (call); \
    if (err__ != cudaSuccess) { \
        std::fprintf(stderr, "CUDA error %s at %s:%d\n", cudaGetErrorString(err__), __FILE__, __LINE__); \
        std::exit(1); \
    } \
} while (0)

// Exact 128-bit two's-complement signed integer on GPU.
struct alignas(16) I128 {
    uint64_t lo;
    int64_t hi;
};

__host__ __device__ static inline I128 i128_zero() { return {0ULL, 0LL}; }

__host__ __device__ static inline I128 i128_shl_bits(int bits) {
    if (bits < 64) return {1ULL << bits, 0LL};
    return {0ULL, 1LL << (bits - 64)};
}

__device__ static inline I128 i128_add(I128 a, I128 b) {
    I128 r;
    asm("add.cc.u64 %0, %2, %3;\n\t"
        "addc.s64 %1, %4, %5;"
        : "=l"(r.lo), "=l"(r.hi)
        : "l"(a.lo), "l"(b.lo), "l"(a.hi), "l"(b.hi));
    return r;
}

__device__ static inline I128 i128_sub(I128 a, I128 b) {
    I128 r;
    asm("sub.cc.u64 %0, %2, %3;\n\t"
        "subc.s64 %1, %4, %5;"
        : "=l"(r.lo), "=l"(r.hi)
        : "l"(a.lo), "l"(b.lo), "l"(a.hi), "l"(b.hi));
    return r;
}

__device__ static inline I128 i128_neg(I128 a) {
    return i128_sub({0ULL, 0LL}, a);
}

__device__ static inline I128 i128_shl4(I128 a) {
    I128 r;
    r.hi = (int64_t)(((uint64_t)a.hi << 4) | (a.lo >> 60));
    r.lo = a.lo << 4;
    return r;
}

// Multiply signed I128 by signed int32_t d (assuming |a * d| < 2^127).
__device__ static inline I128 i128_mul_i32(I128 a, int32_t d) {
    bool neg = false;
    I128 ua = a;
    if (ua.hi < 0) { ua = i128_neg(ua); neg = !neg; }
    uint64_t ud;
    if (d < 0) { ud = (uint64_t)(-(int64_t)d); neg = !neg; }
    else { ud = (uint64_t)d; }
    uint64_t p_lo = ua.lo * ud;
    uint64_t p_hi = __umul64hi(ua.lo, ud) + (uint64_t)ua.hi * ud;
    I128 r = {p_lo, (int64_t)p_hi};
    return neg ? i128_neg(r) : r;
}

// Exact unsigned 128-bit divided by positive uint64_t d (< 2^32):
// Given (hi, lo) and d <= 65536 (in fact d = 8*W or 16*W <= 512):
// q_hi = hi / d, r_hi = hi % d.
// Then (r_hi * 2^64 + lo) / d: since r_hi < d <= 512, split lo into (lo_hi = lo>>32, lo_lo = lo&0xffffffff):
//   t1 = (r_hi << 32) | lo_hi  (< 2^41 << 2^64) -> q1 = t1 / d, r1 = t1 % d
//   t0 = (r1 << 32) | lo_lo    (< 2^41 << 2^64) -> q0 = t0 / d, r0 = t0 % d
//   q_lo = (q1 << 32) | q0, rem = r0!
// ZERO overflow, 100% exact, 4 hardware integer divides!
__device__ static inline I128 i128_floor_div(I128 a, uint32_t d) {
    bool neg = (a.hi < 0);
    I128 ua = neg ? i128_neg(a) : a;
    uint64_t uhi = (uint64_t)ua.hi;
    uint64_t ulo = ua.lo;
    uint64_t q_hi = uhi / d;
    uint64_t r_hi = uhi % d;
    uint64_t t1 = (r_hi << 32) | (ulo >> 32);
    uint64_t q1 = t1 / d;
    uint64_t r1 = t1 % d;
    uint64_t t0 = (r1 << 32) | (ulo & 0xFFFFFFFFULL);
    uint64_t q0 = t0 / d;
    uint64_t rem = t0 % d;
    uint64_t q_lo = (q1 << 32) | q0;
    I128 q = {q_lo, (int64_t)q_hi};
    if (!neg) return q;
    q = i128_neg(q);
    if (rem != 0) q = i128_sub(q, {1ULL, 0LL});
    return q;
}

// Exact floor((c * v) / 2^60) where 0 <= c <= 2^60 and |v| < 2^86!
// Matches CPU mul_shr60 bit-for-bit!
__device__ static inline I128 i128_mul_shr60(uint64_t c, I128 v) {
    const uint64_t mask60 = (1ULL << 60) - 1ULL;
    uint64_t v_lo = v.lo & mask60; // in [0, 2^60 - 1]
    // Exact arithmetic right shift of signed 128-bit v by 60 bits:
    // Since v_lo >= 0, (v - v_lo) >> 60 has low 64 bits = (v.lo >> 60) | ((uint64_t)v.hi << 4),
    // and high 64 bits = v.hi >> 60 (arithmetic shift).
    // Notice |v| < 2^86 -> |v_hi| < 2^26, so v_hi fits completely in signed int64_t!
    int64_t v_hi = (int64_t)(((uint64_t)v.hi << 4) | (v.lo >> 60));

    // Term 1: c * v_hi (signed 128-bit)
    bool neg1 = (v_hi < 0);
    uint64_t uvh = neg1 ? (uint64_t)(-v_hi) : (uint64_t)v_hi;
    I128 t1 = {c * uvh, (int64_t)__umul64hi(c, uvh)};
    if (neg1) t1 = i128_neg(t1);

    // Term 2: floor((c * v_lo) / 2^60), both unsigned < 2^60 -> prod < 2^120
    uint64_t p_lo = c * v_lo;
    uint64_t p_hi = __umul64hi(c, v_lo);
    uint64_t t2_lo = (p_hi << 4) | (p_lo >> 60);
    uint64_t t2_hi = p_hi >> 60;
    return i128_add(t1, {t2_lo, (int64_t)t2_hi});
}

// Host exact 256-bit unsigned integer (for final W1, W2 accumulation).
using u128 = __uint128_t;
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

// GPU atomic-free per-block 256-bit norm accumulator: each column b reduces on GPU into (B, 4) uint64s?
// Even cleaner: reduce per-column U256 on GPU using warp/block reduction, or simple 1-block-per-column
// reduction kernel! Notice dim <= 1.2M and B = 32: a 32-block reduction kernel (1 block of 256 threads
// per column b, striding over i = tid..dim-1, then summing 256 U256s in shared memory) takes < 0.1 ms
// and returns ONLY B * 4 uint64s (1 KB!) to host — ZERO huge D2H transfers!!

struct alignas(32) DevU256 {
    uint64_t w[4];
};

__device__ static inline void dev_u256_add_sq(DevU256& dst, I128 x) {
    if (x.hi < 0) x = i128_neg(x);
    uint64_t a0 = x.lo, a1 = (uint64_t)x.hi;
    if ((a0 | a1) == 0ULL) return;
    // a^2 = a0^2 + 2*a0*a1*2^64 + a1^2*2^128
    uint64_t p00_lo = a0 * a0, p00_hi = __umul64hi(a0, a0);
    uint64_t p01_lo = a0 * a1, p01_hi = __umul64hi(a0, a1);
    uint64_t p11_lo = a1 * a1, p11_hi = __umul64hi(a1, a1);
    // Add p00, p01<<64, p01<<64, p11<<128 into dst.w[0..3]
    asm("add.cc.u64  %0, %0, %4;\n\t"
        "addc.cc.u64 %1, %1, %5;\n\t"
        "addc.cc.u64 %2, %2, %6;\n\t"
        "addc.u64    %3, %3, %7;"
        : "+l"(dst.w[0]), "+l"(dst.w[1]), "+l"(dst.w[2]), "+l"(dst.w[3])
        : "l"(p00_lo), "l"(p00_hi), "l"(p11_lo), "l"(p11_hi));
    asm("add.cc.u64  %0, %0, %3;\n\t"
        "addc.cc.u64 %1, %1, %4;\n\t"
        "addc.u64    %2, %2, 0;"
        : "+l"(dst.w[1]), "+l"(dst.w[2]), "+l"(dst.w[3])
        : "l"(p01_lo), "l"(p01_hi));
    asm("add.cc.u64  %0, %0, %3;\n\t"
        "addc.cc.u64 %1, %1, %4;\n\t"
        "addc.u64    %2, %2, 0;"
        : "+l"(dst.w[1]), "+l"(dst.w[2]), "+l"(dst.w[3])
        : "l"(p01_lo), "l"(p01_hi));
}

__device__ static inline void dev_u256_add(DevU256& dst, const DevU256& src) {
    asm("add.cc.u64  %0, %0, %4;\n\t"
        "addc.cc.u64 %1, %1, %5;\n\t"
        "addc.cc.u64 %2, %2, %6;\n\t"
        "addc.u64    %3, %3, %7;"
        : "+l"(dst.w[0]), "+l"(dst.w[1]), "+l"(dst.w[2]), "+l"(dst.w[3])
        : "l"(src.w[0]), "l"(src.w[1]), "l"(src.w[2]), "l"(src.w[3]));
}

// =========================================================================
// CUDA KERNELS (B = 32 columns coalesced across every warp!)
// =========================================================================
constexpr int BATCH = 32;

__global__ void init_real_kernel(
    uint32_t dim, int B_act, const uint32_t* __restrict__ rep_rows,
    const int32_t* __restrict__ diag, const uint32_t* __restrict__ row_ptr,
    const uint32_t* __restrict__ col_idx, const int8_t* __restrict__ hop_type,
    I128 Q, uint32_t div1, uint64_t c1_0, uint64_t c2_0, uint64_t c1_1, uint64_t c2_1,
    I128* __restrict__ v0, I128* __restrict__ v1, I128* __restrict__ y1, I128* __restrict__ y2)
{
    int b = threadIdx.x;
    if (b >= B_act) return;
    uint32_t r = rep_rows[b];
    v0[(size_t)r * BATCH + b] = Q;
    y1[(size_t)r * BATCH + b] = i128_mul_shr60(c1_0, Q);
    y2[(size_t)r * BATCH + b] = i128_mul_shr60(c2_0, Q);

    I128 vr = i128_floor_div(i128_mul_i32(Q, diag[r]), div1);
    v1[(size_t)r * BATCH + b] = vr;
    if (c1_1) y1[(size_t)r * BATCH + b] = i128_add(y1[(size_t)r * BATCH + b], i128_mul_shr60(c1_1, vr));
    if (c2_1) y2[(size_t)r * BATCH + b] = i128_add(y2[(size_t)r * BATCH + b], i128_mul_shr60(c2_1, vr));

    for (uint32_t e = row_ptr[r]; e < row_ptr[r + 1]; ++e) {
        uint32_t j = col_idx[e];
        // hop_type: 1 => +16, else => -16
        I128 val = (hop_type[e] == 1) ? i128_shl4(Q) : i128_neg(i128_shl4(Q));
        I128 vj = i128_floor_div(val, div1);
        v1[(size_t)j * BATCH + b] = vj;
        if (c1_1) y1[(size_t)j * BATCH + b] = i128_add(y1[(size_t)j * BATCH + b], i128_mul_shr60(c1_1, vj));
        if (c2_1) y2[(size_t)j * BATCH + b] = i128_add(y2[(size_t)j * BATCH + b], i128_mul_shr60(c2_1, vj));
    }
}

__global__ void step_real_kernel(
    uint32_t dim, const int32_t* __restrict__ diag, const uint32_t* __restrict__ row_ptr,
    const uint32_t* __restrict__ col_idx, const int8_t* __restrict__ hop_type,
    uint32_t div2, uint64_t ck1, uint64_t ck2,
    const I128* __restrict__ v0, const I128* __restrict__ v1, I128* __restrict__ v2,
    I128* __restrict__ y1, I128* __restrict__ y2)
{
    uint32_t warp_id = (blockIdx.x * blockDim.x + threadIdx.x) >> 5;
    int lane = threadIdx.x & 31;
    if (warp_id >= dim) return;
    uint32_t i = warp_id;
    size_t idx = (size_t)i * BATCH + lane;

    I128 acc = i128_mul_i32(v1[idx], diag[i]);
    uint32_t start = row_ptr[i], end = row_ptr[i + 1];
    for (uint32_t e = start; e < end; ++e) {
        uint32_t j = col_idx[e];
        I128 vj = i128_shl4(v1[(size_t)j * BATCH + lane]);
        acc = (hop_type[e] == 1) ? i128_add(acc, vj) : i128_sub(acc, vj);
    }
    I128 nv = i128_sub(i128_floor_div(acc, div2), v0[idx]);
    v2[idx] = nv;
    if (ck1) y1[idx] = i128_add(y1[idx], i128_mul_shr60(ck1, nv));
    if (ck2) y2[idx] = i128_add(y2[idx], i128_mul_shr60(ck2, nv));
}

__global__ void init_complex_kernel(
    uint32_t dim, int B_act, const uint32_t* __restrict__ rep_rows,
    const int32_t* __restrict__ diag, const uint32_t* __restrict__ row_ptr,
    const uint32_t* __restrict__ col_idx, const int8_t* __restrict__ hop_type,
    I128 Q, uint32_t div1, uint64_t c1_0, uint64_t c2_0, uint64_t c1_1, uint64_t c2_1,
    I128* __restrict__ v0r, I128* __restrict__ v1r, I128* __restrict__ v1i,
    I128* __restrict__ y1r, I128* __restrict__ y1i, I128* __restrict__ y2r, I128* __restrict__ y2i)
{
    int b = threadIdx.x;
    if (b >= B_act) return;
    uint32_t r = rep_rows[b];
    v0r[(size_t)r * BATCH + b] = Q;
    y1r[(size_t)r * BATCH + b] = i128_mul_shr60(c1_0, Q);
    y2r[(size_t)r * BATCH + b] = i128_mul_shr60(c2_0, Q);

    I128 vr = i128_floor_div(i128_mul_i32(Q, diag[r]), div1);
    v1r[(size_t)r * BATCH + b] = vr;
    if (c1_1) y1r[(size_t)r * BATCH + b] = i128_add(y1r[(size_t)r * BATCH + b], i128_mul_shr60(c1_1, vr));
    if (c2_1) y2r[(size_t)r * BATCH + b] = i128_add(y2r[(size_t)r * BATCH + b], i128_mul_shr60(c2_1, vr));

    I128 q16 = i128_shl4(Q);
    I128 nq16 = i128_neg(q16);
    for (uint32_t e = row_ptr[r]; e < row_ptr[r + 1]; ++e) {
        uint32_t j = col_idx[e];
        int8_t ht = hop_type[e];
        I128 jr = i128_zero(), ji = i128_zero();
        if (ht == 0) jr = i128_floor_div(nq16, div1);
        else if (ht == 2) ji = i128_floor_div(nq16, div1);
        else if (ht == 3) ji = i128_floor_div(q16, div1);
        v1r[(size_t)j * BATCH + b] = jr;
        v1i[(size_t)j * BATCH + b] = ji;
        if (c1_1) {
            y1r[(size_t)j * BATCH + b] = i128_add(y1r[(size_t)j * BATCH + b], i128_mul_shr60(c1_1, jr));
            y1i[(size_t)j * BATCH + b] = i128_add(y1i[(size_t)j * BATCH + b], i128_mul_shr60(c1_1, ji));
        }
        if (c2_1) {
            y2r[(size_t)j * BATCH + b] = i128_add(y2r[(size_t)j * BATCH + b], i128_mul_shr60(c2_1, jr));
            y2i[(size_t)j * BATCH + b] = i128_add(y2i[(size_t)j * BATCH + b], i128_mul_shr60(c2_1, ji));
        }
    }
}

__global__ void step_complex_kernel(
    uint32_t dim, const int32_t* __restrict__ diag, const uint32_t* __restrict__ row_ptr,
    const uint32_t* __restrict__ col_idx, const int8_t* __restrict__ hop_type,
    uint32_t div2, uint64_t ck1, uint64_t ck2,
    const I128* __restrict__ v0r, const I128* __restrict__ v0i,
    const I128* __restrict__ v1r, const I128* __restrict__ v1i,
    I128* __restrict__ v2r, I128* __restrict__ v2i,
    I128* __restrict__ y1r, I128* __restrict__ y1i,
    I128* __restrict__ y2r, I128* __restrict__ y2i)
{
    uint32_t warp_id = (blockIdx.x * blockDim.x + threadIdx.x) >> 5;
    int lane = threadIdx.x & 31;
    if (warp_id >= dim) return;
    uint32_t i = warp_id;
    size_t idx = (size_t)i * BATCH + lane;

    int32_t di = diag[i];
    I128 ar = i128_mul_i32(v1r[idx], di);
    I128 ai = i128_mul_i32(v1i[idx], di);
    uint32_t start = row_ptr[i], end = row_ptr[i + 1];
    for (uint32_t e = start; e < end; ++e) {
        uint32_t j = col_idx[e];
        int8_t ht = hop_type[e];
        I128 xr = i128_shl4(v1r[(size_t)j * BATCH + lane]);
        I128 xi = i128_shl4(v1i[(size_t)j * BATCH + lane]);
        if (ht == 0) {
            ar = i128_sub(ar, xr);
            ai = i128_sub(ai, xi);
        } else if (ht == 2) {
            ar = i128_sub(ar, xi);
            ai = i128_add(ai, xr);
        } else {
            ar = i128_add(ar, xi);
            ai = i128_sub(ai, xr);
        }
    }
    I128 nvr = i128_sub(i128_floor_div(ar, div2), v0r[idx]);
    I128 nvi = i128_sub(i128_floor_div(ai, div2), v0i[idx]);
    v2r[idx] = nvr;
    v2i[idx] = nvi;
    if (ck1) {
        y1r[idx] = i128_add(y1r[idx], i128_mul_shr60(ck1, nvr));
        y1i[idx] = i128_add(y1i[idx], i128_mul_shr60(ck1, nvi));
    }
    if (ck2) {
        y2r[idx] = i128_add(y2r[idx], i128_mul_shr60(ck2, nvr));
        y2i[idx] = i128_add(y2i[idx], i128_mul_shr60(ck2, nvi));
    }
}

__global__ void norm_reduce_kernel(
    uint32_t dim, bool is_complex,
    const I128* __restrict__ y1r, const I128* __restrict__ y1i,
    const I128* __restrict__ y2r, const I128* __restrict__ y2i,
    DevU256* __restrict__ out1, DevU256* __restrict__ out2)
{
    int b = blockIdx.x;
    int tid = threadIdx.x;
    __shared__ DevU256 s1[256], s2[256];
    DevU256 a1 = {{0, 0, 0, 0}}, a2 = {{0, 0, 0, 0}};
    for (uint32_t i = tid; i < dim; i += 256) {
        size_t idx = (size_t)i * BATCH + b;
        dev_u256_add_sq(a1, y1r[idx]);
        dev_u256_add_sq(a2, y2r[idx]);
        if (is_complex) {
            dev_u256_add_sq(a1, y1i[idx]);
            dev_u256_add_sq(a2, y2i[idx]);
        }
    }
    s1[tid] = a1; s2[tid] = a2;
    __syncthreads();
    for (int off = 128; off > 0; off >>= 1) {
        if (tid < off) {
            dev_u256_add(s1[tid], s1[tid + off]);
            dev_u256_add(s2[tid], s2[tid + off]);
        }
        __syncthreads();
    }
    if (tid == 0) { out1[b] = s1[0]; out2[b] = s2[0]; }
}

// =========================================================================
// HOST BLOCK BUILDERS (identical to CPU reference)
// =========================================================================
struct OrbitRep { uint32_t local_idx; uint32_t mult; };
struct BlockData {
    int id;
    uint32_t dim;
    std::vector<uint32_t> states;
    std::vector<int32_t> diag;
    std::vector<uint32_t> row_ptr;
    std::vector<uint32_t> col_idx;
    std::vector<int8_t> hop_type;
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

static BlockData build_block_sz(int n, int M, int seam, int E_num, int W,
                                const uint32_t* pw, std::vector<int32_t>& g2l) {
    BlockData blk; blk.id = M;
    uint32_t total = pw[n];
    uint8_t d[16];
    for (uint32_t code = 0; code < total; ++code) {
        uint32_t x = code; int sum = 0;
        for (int j = 0; j < n; ++j) { sum += (int)(x % 3) - 1; x /= 3; }
        if (sum == M) { g2l[code] = (int32_t)blk.states.size(); blk.states.push_back(code); }
    }
    blk.dim = (uint32_t)blk.states.size();
    blk.diag.resize(blk.dim); blk.row_ptr.resize(blk.dim + 1);
    blk.col_idx.reserve((size_t)blk.dim * (n + 2));
    blk.hop_type.reserve((size_t)blk.dim * (n + 2));
    const int32_t base_shift = 16 * W - E_num * n;
    for (uint32_t i = 0; i < blk.dim; ++i) {
        uint32_t code = blk.states[i]; encode_digits(code, n, d);
        int zz = 0, sz2 = 0;
        for (int j = 0; j < n; ++j) {
            int s1 = (int)d[j] - 1, s2 = (int)d[(j + 1) % n] - 1;
            zz += s1 * s2; sz2 += s1 * s1;
        }
        blk.diag[i] = base_shift - 16 * zz - 4 * sz2;
        blk.row_ptr[i] = (uint32_t)blk.col_idx.size();
        for (int j = 0; j < n; ++j) {
            int k = (j + 1) % n; bool is_seam = (j == n - 1);
            if (d[j] < 2 && d[k] > 0) {
                int32_t dst = g2l[code + pw[j] - pw[k]]; assert(dst >= 0);
                blk.col_idx.push_back((uint32_t)dst);
                int8_t ht = 0;
                if (is_seam) { if (seam == 1) ht = 1; else if (seam == 2) ht = 2; }
                blk.hop_type.push_back(ht);
            }
            if (d[j] > 0 && d[k] < 2) {
                int32_t dst = g2l[code - pw[j] + pw[k]]; assert(dst >= 0);
                blk.col_idx.push_back((uint32_t)dst);
                int8_t ht = 0;
                if (is_seam) { if (seam == 1) ht = 1; else if (seam == 2) ht = 3; }
                blk.hop_type.push_back(ht);
            }
        }
    }
    blk.row_ptr[blk.dim] = (uint32_t)blk.col_idx.size();
    std::vector<uint8_t> vis(blk.dim, 0); uint8_t tmp[16];
    std::vector<uint32_t> orb; orb.reserve(4 * n);
    for (uint32_t i = 0; i < blk.dim; ++i) {
        if (vis[i]) continue;
        encode_digits(blk.states[i], n, d); orb.clear();
        int neg_max = (M == 0) ? 2 : 1;
        for (int neg = 0; neg < neg_max; ++neg)
            for (int rev = 0; rev < 2; ++rev)
                for (int sh = 0; sh < n; ++sh) {
                    for (int j = 0; j < n; ++j) {
                        int idx = rev ? ((n - 1 - j + sh) % n) : ((j + sh) % n);
                        uint8_t dig = d[idx]; if (neg) dig = 2 - dig; tmp[j] = dig;
                    }
                    int32_t loc = g2l[decode_digits(tmp, n, pw)]; assert(loc >= 0);
                    if (!vis[loc]) { vis[loc] = 1; orb.push_back((uint32_t)loc); }
                }
        blk.reps.push_back({i, (uint32_t)orb.size() * (M > 0 ? 2u : 1u)});
    }
    for (uint32_t code : blk.states) g2l[code] = -1;
    return blk;
}

static BlockData build_block_rx(int n, int sec, int E_num, int W,
                                const uint32_t* pw, std::vector<int32_t>& g2l) {
    BlockData blk; blk.id = sec;
    uint32_t total = pw[n]; uint8_t d[16];
    for (uint32_t code = 0; code < total; ++code) {
        uint32_t x = code; int cx = 0, cy = 0;
        for (int j = 0; j < n; ++j) { int dig = x % 3; x /= 3; if (dig == 0) cx ^= 1; else if (dig == 1) cy ^= 1; }
        if ((cx | (cy << 1)) == sec) { g2l[code] = (int32_t)blk.states.size(); blk.states.push_back(code); }
    }
    blk.dim = (uint32_t)blk.states.size();
    blk.diag.resize(blk.dim); blk.row_ptr.resize(blk.dim + 1);
    blk.col_idx.reserve((size_t)blk.dim * (2 * n));
    blk.hop_type.reserve((size_t)blk.dim * (2 * n));
    const int32_t base_shift = 16 * W - E_num * n;
    for (uint32_t i = 0; i < blk.dim; ++i) {
        uint32_t code = blk.states[i]; encode_digits(code, n, d);
        int sz2 = 0; for (int j = 0; j < n; ++j) if (d[j] != 2) ++sz2;
        blk.diag[i] = base_shift - 4 * sz2;
        blk.row_ptr[i] = (uint32_t)blk.col_idx.size();
        for (int j = 0; j < n; ++j) {
            int k = (j + 1) % n; bool is_seam = (j == n - 1);
            uint8_t a = d[j], b = d[k];
            if (a == b) {
                for (uint8_t v = 0; v < 3; ++v) {
                    if (v == a) continue;
                    int ax = 3 - (int)a - (int)v;
                    int sg = (is_seam && ax != 0) ? -1 : 1;
                    int32_t dst = g2l[code + (int)(v - a) * (int)pw[j] + (int)(v - a) * (int)pw[k]];
                    assert(dst >= 0);
                    blk.col_idx.push_back((uint32_t)dst);
                    // hop_type: 1 means +16, 0 means -16
                    blk.hop_type.push_back((sg > 0) ? 1 : 0);
                }
            } else {
                int ax = 3 - (int)a - (int)b;
                int sg = (is_seam && ax != 0) ? -1 : 1;
                int32_t dst = g2l[code + (int)(b - a) * (int)pw[j] + (int)(a - b) * (int)pw[k]];
                assert(dst >= 0);
                blk.col_idx.push_back((uint32_t)dst);
                blk.hop_type.push_back(((-sg) > 0) ? 1 : 0);
            }
        }
    }
    blk.row_ptr[blk.dim] = (uint32_t)blk.col_idx.size();
    std::vector<uint8_t> vis(blk.dim, 0); uint8_t tmp[16];
    std::vector<uint32_t> orb; orb.reserve(2 * n);
    for (uint32_t i = 0; i < blk.dim; ++i) {
        if (vis[i]) continue;
        encode_digits(blk.states[i], n, d); orb.clear();
        for (int rev = 0; rev < 2; ++rev)
            for (int sh = 0; sh < n; ++sh) {
                for (int j = 0; j < n; ++j) {
                    int idx = rev ? ((n - 1 - j + sh) % n) : ((j + sh) % n);
                    tmp[j] = d[idx];
                }
                int32_t loc = g2l[decode_digits(tmp, n, pw)]; assert(loc >= 0);
                if (!vis[loc]) { vis[loc] = 1; orb.push_back((uint32_t)loc); }
            }
        blk.reps.push_back({i, (uint32_t)orb.size()});
    }
    for (uint32_t code : blk.states) g2l[code] = -1;
    return blk;
}

int main(int argc, char** argv) {
    // Usage: chebyshev_enclose_cuda n seam(0=I,1=Rz,2=R4,3=Rx) E_num W K Q_bits coeff_file [num_gpus]
    if (argc < 8) {
        std::fprintf(stderr, "Usage: %s n seam E_num W K Q_bits coeff_file [num_gpus]\n", argv[0]);
        return 1;
    }
    int n = std::atoi(argv[1]);
    int seam = std::atoi(argv[2]);
    int E_num = std::atoi(argv[3]);
    int W = std::atoi(argv[4]);
    int K = std::atoi(argv[5]);
    int Q_bits = std::atoi(argv[6]);
    const char* coeff_path = argv[7];

    int dev_count = 0;
    CUDA_CHECK(cudaGetDeviceCount(&dev_count));
    int ngpus = (argc >= 9) ? std::min(dev_count, std::atoi(argv[8])) : dev_count;
    assert(ngpus >= 1);

    std::vector<uint64_t> c1(K + 1), c2(K + 1);
    FILE* cf = std::fopen(coeff_path, "r");
    if (!cf) { std::perror("fopen"); return 1; }
    for (int k = 0; k <= K; ++k) {
        unsigned long long a = 0, b = 0;
        if (std::fscanf(cf, "%llu %llu", &a, &b) != 2) return 1;
        c1[k] = a; c2[k] = b;
    }
    std::fclose(cf);

    uint32_t pw[16]; pw[0] = 1;
    for (int j = 1; j <= n; ++j) pw[j] = pw[j - 1] * 3u;
    std::vector<int32_t> g2l(pw[n], -1);

    const bool is_complex = (seam == 2);
    const I128 Q = i128_shl_bits(Q_bits);
    const uint32_t div1 = 16u * (uint32_t)W;
    const uint32_t div2 = 8u * (uint32_t)W;

    int nblocks = (seam == 3) ? 4 : (n + 1);
    U256 total_W1, total_W2;
    uint64_t total_mult = 0;

    for (int bid = 0; bid < nblocks; ++bid) {
        BlockData blk = (seam == 3)
            ? build_block_rx(n, bid, E_num, W, pw, g2l)
            : build_block_sz(n, bid, seam, E_num, W, pw, g2l);
        uint64_t blk_mult = 0;
        for (auto& r : blk.reps) blk_mult += r.mult;
        total_mult += blk_mult;

        const uint32_t dim = blk.dim;
        const size_t nreps = blk.reps.size();
        const size_t nbatches = (nreps + BATCH - 1) / BATCH;
        std::atomic<size_t> next_batch{0};
        std::vector<U256> gpu_W1(ngpus), gpu_W2(ngpus);

        auto gpu_worker = [&](int gid) {
            CUDA_CHECK(cudaSetDevice(gid));
            int32_t* d_diag = nullptr;
            uint32_t *d_rp = nullptr, *d_ci = nullptr, *d_rep = nullptr;
            int8_t* d_ht = nullptr;
            CUDA_CHECK(cudaMalloc(&d_diag, dim * sizeof(int32_t)));
            CUDA_CHECK(cudaMalloc(&d_rp, (dim + 1) * sizeof(uint32_t)));
            CUDA_CHECK(cudaMalloc(&d_ci, std::max<size_t>(1, blk.col_idx.size()) * sizeof(uint32_t)));
            CUDA_CHECK(cudaMalloc(&d_ht, std::max<size_t>(1, blk.hop_type.size()) * sizeof(int8_t)));
            CUDA_CHECK(cudaMalloc(&d_rep, BATCH * sizeof(uint32_t)));
            CUDA_CHECK(cudaMemcpy(d_diag, blk.diag.data(), dim * sizeof(int32_t), cudaMemcpyHostToDevice));
            CUDA_CHECK(cudaMemcpy(d_rp, blk.row_ptr.data(), (dim + 1) * sizeof(uint32_t), cudaMemcpyHostToDevice));
            if (!blk.col_idx.empty()) {
                CUDA_CHECK(cudaMemcpy(d_ci, blk.col_idx.data(), blk.col_idx.size() * sizeof(uint32_t), cudaMemcpyHostToDevice));
                CUDA_CHECK(cudaMemcpy(d_ht, blk.hop_type.data(), blk.hop_type.size() * sizeof(int8_t), cudaMemcpyHostToDevice));
            }

            size_t vec_bytes = (size_t)dim * BATCH * sizeof(I128);
            I128 *d_v0r = nullptr, *d_v1r = nullptr, *d_v2r = nullptr, *d_y1r = nullptr, *d_y2r = nullptr;
            I128 *d_v0i = nullptr, *d_v1i = nullptr, *d_v2i = nullptr, *d_y1i = nullptr, *d_y2i = nullptr;
            CUDA_CHECK(cudaMalloc(&d_v0r, vec_bytes));
            CUDA_CHECK(cudaMalloc(&d_v1r, vec_bytes));
            CUDA_CHECK(cudaMalloc(&d_v2r, vec_bytes));
            CUDA_CHECK(cudaMalloc(&d_y1r, vec_bytes));
            CUDA_CHECK(cudaMalloc(&d_y2r, vec_bytes));
            if (is_complex) {
                CUDA_CHECK(cudaMalloc(&d_v0i, vec_bytes));
                CUDA_CHECK(cudaMalloc(&d_v1i, vec_bytes));
                CUDA_CHECK(cudaMalloc(&d_v2i, vec_bytes));
                CUDA_CHECK(cudaMalloc(&d_y1i, vec_bytes));
                CUDA_CHECK(cudaMalloc(&d_y2i, vec_bytes));
            }
            DevU256 *d_out1 = nullptr, *d_out2 = nullptr;
            CUDA_CHECK(cudaMalloc(&d_out1, BATCH * sizeof(DevU256)));
            CUDA_CHECK(cudaMalloc(&d_out2, BATCH * sizeof(DevU256)));
            DevU256 h_out1[BATCH], h_out2[BATCH];
            uint32_t h_rep[BATCH], h_mult[BATCH];

            const int warps_per_blk = 8; // 256 threads = 8 warps = 8 rows per block
            const int threads = warps_per_blk * 32;
            const int grid = (int)((dim + warps_per_blk - 1) / warps_per_blk);

            while (true) {
                size_t bi = next_batch.fetch_add(1, std::memory_order_relaxed);
                if (bi >= nbatches) break;
                size_t base = bi * BATCH;
                int B_act = (int)std::min<size_t>(BATCH, nreps - base);
                for (int b = 0; b < B_act; ++b) {
                    h_rep[b] = blk.reps[base + b].local_idx;
                    h_mult[b] = blk.reps[base + b].mult;
                }
                CUDA_CHECK(cudaMemcpy(d_rep, h_rep, B_act * sizeof(uint32_t), cudaMemcpyHostToDevice));
                CUDA_CHECK(cudaMemset(d_v0r, 0, vec_bytes));
                CUDA_CHECK(cudaMemset(d_v1r, 0, vec_bytes));
                CUDA_CHECK(cudaMemset(d_y1r, 0, vec_bytes));
                CUDA_CHECK(cudaMemset(d_y2r, 0, vec_bytes));
                if (is_complex) {
                    CUDA_CHECK(cudaMemset(d_v0i, 0, vec_bytes));
                    CUDA_CHECK(cudaMemset(d_v1i, 0, vec_bytes));
                    CUDA_CHECK(cudaMemset(d_y1i, 0, vec_bytes));
                    CUDA_CHECK(cudaMemset(d_y2i, 0, vec_bytes));
                }

                if (!is_complex) {
                    init_real_kernel<<<1, BATCH>>>(dim, B_act, d_rep, d_diag, d_rp, d_ci, d_ht,
                                                   Q, div1, c1[0], c2[0], c1[1], c2[1],
                                                   d_v0r, d_v1r, d_y1r, d_y2r);
                    for (int k = 2; k <= K; ++k) {
                        step_real_kernel<<<grid, threads>>>(dim, d_diag, d_rp, d_ci, d_ht,
                                                            div2, c1[k], c2[k],
                                                            d_v0r, d_v1r, d_v2r, d_y1r, d_y2r);
                        std::swap(d_v0r, d_v1r);
                        std::swap(d_v1r, d_v2r);
                    }
                } else {
                    init_complex_kernel<<<1, BATCH>>>(dim, B_act, d_rep, d_diag, d_rp, d_ci, d_ht,
                                                      Q, div1, c1[0], c2[0], c1[1], c2[1],
                                                      d_v0r, d_v1r, d_v1i, d_y1r, d_y1i, d_y2r, d_y2i);
                    for (int k = 2; k <= K; ++k) {
                        step_complex_kernel<<<grid, threads>>>(dim, d_diag, d_rp, d_ci, d_ht,
                                                               div2, c1[k], c2[k],
                                                               d_v0r, d_v0i, d_v1r, d_v1i, d_v2r, d_v2i,
                                                               d_y1r, d_y1i, d_y2r, d_y2i);
                        std::swap(d_v0r, d_v1r); std::swap(d_v0i, d_v1i);
                        std::swap(d_v1r, d_v2r); std::swap(d_v1i, d_v2i);
                    }
                }
                norm_reduce_kernel<<<B_act, 256>>>(dim, is_complex, d_y1r, d_y1i, d_y2r, d_y2i, d_out1, d_out2);
                CUDA_CHECK(cudaMemcpy(h_out1, d_out1, B_act * sizeof(DevU256), cudaMemcpyDeviceToHost));
                CUDA_CHECK(cudaMemcpy(h_out2, d_out2, B_act * sizeof(DevU256), cudaMemcpyDeviceToHost));

                for (int b = 0; b < B_act; ++b) {
                    U256 u1, u2;
                    for (int l = 0; l < 4; ++l) { u1.w[l] = h_out1[b].w[l]; u2.w[l] = h_out2[b].w[l]; }
                    gpu_W1[gid].add_scaled_u256(h_mult[b], u1);
                    gpu_W2[gid].add_scaled_u256(h_mult[b], u2);
                }
            }

            CUDA_CHECK(cudaFree(d_diag)); CUDA_CHECK(cudaFree(d_rp)); CUDA_CHECK(cudaFree(d_ci));
            CUDA_CHECK(cudaFree(d_ht)); CUDA_CHECK(cudaFree(d_rep));
            CUDA_CHECK(cudaFree(d_v0r)); CUDA_CHECK(cudaFree(d_v1r)); CUDA_CHECK(cudaFree(d_v2r));
            CUDA_CHECK(cudaFree(d_y1r)); CUDA_CHECK(cudaFree(d_y2r));
            if (is_complex) {
                CUDA_CHECK(cudaFree(d_v0i)); CUDA_CHECK(cudaFree(d_v1i)); CUDA_CHECK(cudaFree(d_v2i));
                CUDA_CHECK(cudaFree(d_y1i)); CUDA_CHECK(cudaFree(d_y2i));
            }
            CUDA_CHECK(cudaFree(d_out1)); CUDA_CHECK(cudaFree(d_out2));
        };

        int used_gpus = std::min(ngpus, (int)std::max<size_t>(1, nbatches));
        std::vector<std::thread> threads;
        for (int g = 0; g < used_gpus; ++g) threads.emplace_back(gpu_worker, g);
        for (auto& th : threads) th.join();

        U256 blk_W1, blk_W2;
        for (int g = 0; g < used_gpus; ++g) {
            blk_W1.add_u256(gpu_W1[g]);
            blk_W2.add_u256(gpu_W2[g]);
        }
        total_W1.add_u256(blk_W1);
        total_W2.add_u256(blk_W2);
        std::fprintf(stderr, "  blk=%2d dim=%7u reps=%6zu batches=%5zu mult=%8llu W1=%s\n",
                     bid, dim, nreps, nbatches, (unsigned long long)blk_mult, blk_W1.to_dec().c_str());
    }

    assert(total_mult == pw[n]);
    std::printf("TOTAL n=%d seam=%d mult=%llu\nW1=%s\nW2=%s\n",
                n, seam, (unsigned long long)total_mult,
                total_W1.to_dec().c_str(), total_W2.to_dec().c_str());
    return 0;
}
