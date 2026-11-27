#!/usr/bin/env python3
"""Standalone pure-integer / exact-rational verifier for ALL 88 Candidate A
(Delta=1, D=1/4, a=1.242818) thermal trace enclosures produced by the pure-integer
__int128 Chebyshev contraction engine (zero floating point, zero third-party deps).

Given ONLY the raw 256-bit integer totals W_int in data/candidate_a_all88_enclosures.json
and the Lean 4 table literals in PurityBootstrap/CandidateA/Data.lean:
1. Certifies all 2,744 exact integer Chebyshev coefficient floors floor(2^60 * c_k) using
   the exact Poisson-difference identity P(|X - Y| = k) = (2 - 1_{k=0}) exp(-mu) I_k(mu)
   for independent Poisson(mu/2) variables, with exact integer weights and a geometric
   tail upper bound, and checks the SHA-256 digest of the coefficient stream.
2. Encloses exp(x_n) using exact rational Taylor series sum_{j=0}^{220} x^j/j! plus its
   exact geometric tail bound (valid for 0 <= x < 221; here max x = 35.491116).
3. Encloses sqrt(W_int) via exact integer square root isqrt(W_int).
4. Recomputes the rigorous Frobenius error bound and verifies for EVERY (n, seam, b) in
   {4..14} x {I, Rz, Rx, R4} x {31/2, 23} that:
     - the recomputed exact interval [lo, hi] lies inside the archived decimal [lo, hi],
     - both endpoints lie strictly inside center +/- 10^{-5} for the Lean center.

Uses explicit runtime checks (never bare `assert`), so `python3 -O` cannot bypass any check.
"""
import ast
import hashlib
import json
import math
import re
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA_JSON = ROOT / "data" / "candidate_a_all88_enclosures.json"
LEAN_DATA = ROOT / "PurityBootstrap" / "CandidateA" / "Data.lean"

SCALE = 1 << 60
SEAMS = ("I", "Rz", "Rx", "R4")
EXPECTED_COEFF_SHA256 = "b117cdb2dfdab1b136be49ed8bd08ea24b517b69dcfc9810c00b864e6f23362e"


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def ceil_ratio(a: int, b: int) -> int:
    require(b > 0, f"ceil_ratio requires positive denominator, got {b}")
    return -(-a // b)


@lru_cache(None)
def coefficient_floors(mu: F, degree: int) -> tuple[int, ...]:
    """Certify exact floor(2^60 * P(|X - Y| = k)) for independent Poisson(mu/2) variables."""
    t = mu / 2
    p, q = t.numerator, t.denominator
    n = 380
    require(q * (n + 2) > p >= 0, f"Taylor tail condition failed for mu={mu}")
    weights = [q**n * math.factorial(n)]
    for j in range(1, n + 1):
        weight, remainder = divmod(weights[-1] * p, j * q)
        require(remainder == 0, f"Exact integer division failed at j={j}, mu={mu}")
        weights.append(weight)
    inside = sum(weights)
    tail = ceil_ratio(weights[-1] * p * (n + 2), (n + 1) * (q * (n + 2) - p))
    upper_square = (inside + tail) ** 2
    lower_square = inside**2
    outside = upper_square - lower_square
    floors = []
    for k in range(degree + 1):
        diagonal = sum(a * b for a, b in zip(weights, weights[k:]))
        numerator = diagonal if k == 0 else 2 * diagonal
        lower = (SCALE * numerator) // upper_square
        upper = (SCALE * (numerator + outside)) // lower_square
        require(lower == upper, f"Ambiguous coefficient floor at mu={mu}, k={k}: {lower} != {upper}")
        floors.append(lower)
    return tuple(floors)


@lru_cache(None)
def exp_bounds(x: F) -> tuple[F, F]:
    """Exact rational enclosure [L, U] for exp(x) valid for 0 <= x < 221."""
    require(0 <= x < 221, f"exp_bounds out of domain: x={x}")
    term = total = F(1)
    for j in range(1, 221):
        term *= x / j
        total += term
    tail_ub = term * x / 221 / (1 - x / 222)
    return total, total + tail_ub


def load_lean_centers() -> dict[tuple[int, str, str], F]:
    require(LEAN_DATA.exists(), f"Missing {LEAN_DATA}")
    source = LEAN_DATA.read_text()
    centers: dict[tuple[int, str, str], F] = {}
    for name, beta in (("caTable155", "31/2"), ("caTable23", "23")):
        match = re.search(rf"def {name} : List [^\n]+ :=\s*(\[.*?\])", source, re.S)
        require(match is not None, f"Could not parse {name} in {LEAN_DATA}")
        rows = ast.literal_eval(match.group(1))
        require(len(rows) == 11 and all(len(row) == 4 for row in rows), f"Malformed table {name}")
        for n, row in enumerate(rows, 4):
            for seam, center in zip(SEAMS, row):
                centers[(n, seam, beta)] = F(center, 10**9)
    return centers


def main() -> None:
    require(DATA_JSON.exists(), f"Missing {DATA_JSON}")
    records = json.loads(DATA_JSON.read_text())
    centers = load_lean_centers()
    require(len(records) == 44, f"Expected 44 (n, seam) records, got {len(records)}")
    require(len(centers) == 88, f"Expected 88 Lean centers, got {len(centers)}")

    digest = hashlib.sha256()
    for w, degree in sorted({(r["W"], r["K"]) for r in records.values()}):
        require(6 <= w <= 18 and 1 <= degree <= 163, f"Unexpected (W, K) = ({w}, {degree})")
        left = coefficient_floors(F(31 * w, 4), degree)
        right = coefficient_floors(F(23 * w, 2), degree)
        for a, b in zip(left, right):
            digest.update(f"{a} {b}\n".encode("ascii"))
    got_digest = digest.hexdigest()
    require(
        got_digest == EXPECTED_COEFF_SHA256,
        f"Coefficient digest mismatch: {got_digest} != {EXPECTED_COEFF_SHA256}",
    )

    eps = F(1, 100000)
    a_shift = F(1242818, 10**6)
    worst_dev = (F(0), "")
    worst_rad = (F(0), "")
    worst_n14_dev = (F(0), "")
    checked = 0

    for (n, seam, beta), center in centers.items():
        key = f"{n}_{seam}"
        require(key in records, f"Missing record {key}")
        rec = records[key]
        b = F(beta)
        en = 24 if n <= 6 else 21
        w = ceil_ratio((20 + en) * n, 32)
        degree = rec["K"]
        require(
            (rec["n"], rec["seam"], rec["E_num"], rec["W"]) == (n, seam, en, w),
            f"Parameter mismatch in {key}: {rec}",
        )
        require(rec["Q_bits"] == 84 and 1 <= degree <= 163, f"Invalid Q_bits/K in {key}")

        c = coefficient_floors(b * w / 2, degree)
        d = 3**n
        components = 2 if seam == "R4" else 1
        coordinate_bound = math.isqrt(components * d) + 1
        q = 1 << 84
        omitted = F(SCALE - sum(c), SCALE)
        require(omitted >= 0, f"Negative omitted coefficient mass at {key} b={beta}")
        amplification = F(sum(v * k * (k + 1) // 2 for k, v in enumerate(c)), SCALE)
        products = sum(v != 0 for v in c)
        error = (math.isqrt(d) + 1) * (q * omitted + coordinate_bound * (amplification + products))

        entry = rec["results"][beta]
        w_int = int(entry["W_int"])
        require(w_int >= 0, f"Negative W_int at {key} b={beta}")
        root = math.isqrt(w_int)
        require(root * root <= w_int < (root + 1) * (root + 1), f"isqrt sanity failed at {key}")

        lo_exp, hi_exp = exp_bounds(b * n * (F(en, 16) - a_shift))
        lo = lo_exp * (max(F(0), root - error) / q) ** 2
        hi = hi_exp * ((root + 1 + error) / q) ** 2

        arch_lo, arch_hi = F(entry["lo"]), F(entry["hi"])
        require(
            arch_lo <= lo <= hi <= arch_hi,
            f"Interval mismatch at {key} b={beta}: archived=[{float(arch_lo)}, {float(arch_hi)}], "
            f"recomputed=[{float(lo)}, {float(hi)}]",
        )
        deviation = max(center - lo, hi - center)
        require(
            deviation < eps,
            f"Lean box failure at {key} b={beta}: deviation={float(deviation):.6e} >= 1e-5",
        )
        rad = (hi - lo) / 2
        tag = f"n={n} {seam} b={beta}"
        worst_dev = max(worst_dev, (deviation, tag))
        worst_rad = max(worst_rad, (rad, tag))
        if n == 14:
            worst_n14_dev = max(worst_n14_dev, (deviation, tag))
        checked += 1

    require(checked == 88, f"Expected 88 checks, ran {checked}")
    min_margin = eps - worst_dev[0]
    print(f"ALL {checked}/88 CANDIDATE A RAW THERMAL ENCLOSURES RIGOROUSLY CERTIFIED (PURE INTEGER/RATIONAL)!")
    print(f"  Coefficient stream SHA-256:          {got_digest}")
    print(f"  Worst-case interval radius:          {float(worst_rad[0]):.6e}  ({worst_rad[1]})")
    print(f"  Worst-case |endpoint - Lean center|: {float(worst_dev[0]):.6e}  ({worst_dev[1]}, limit 1.000e-05)")
    print(f"  Worst-case n=14 endpoint distance:   {float(worst_n14_dev[0]):.6e}  ({worst_n14_dev[1]})")
    print(f"  Minimum strict safety margin:        {float(min_margin):.6e}  ({100 * float(min_margin / eps):.2f}% of budget unused)")


if __name__ == "__main__":
    main()
