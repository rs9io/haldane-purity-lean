#!/usr/bin/env python3
"""
Emit Lean 4 pure-kernel (`decide +kernel`) 6-block Gershgorin certificates for
all 4 corners of Candidate E: (g, h) in {(15,47), (15,48), (16,47), (16,48)} / 128.

IMPORTANT: Uses Lean's exact `sectorState 8 false i` basis ordering:
  state[i] = i + (128 if popcount(i) % 2 == 1 else 0),  for i in 0..127.
"""
from __future__ import annotations

from fractions import Fraction
import math
import os
import numpy as np


def lean_even_x_states(L: int = 8) -> list[int]:
    """Exact state ordering matching `IsingHamiltonian.sectorState L false i`."""
    half = 1 << (L - 1)
    return [i + (half if (i.bit_count() % 2 == 1) else 0) for i in range(half)]


def rot(s: int, k: int, L: int = 8) -> int:
    return ((s << k) | (s >> (L - k))) & ((1 << L) - 1)


def rev(s: int, L: int = 8) -> int:
    r = 0
    for b in range(L):
        if (s >> b) & 1:
            r |= 1 << (L - 1 - b)
    return r


def build_H8_shift_int_lean(g_num: int, h_num: int, twist: bool) -> np.ndarray:
    """Exact integer matrix matching `BlockGershgorin.H8ShiftInt g_num h_num twist`
    = 128 * (H_ising 8 (g_num/128) (h_num/128) twist false + 12 * I) on Fin 128."""
    L = 8
    states = lean_even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=np.int64)
    for i, s in enumerate(states):
        sxx = 0
        sx = 0
        for k in range(L):
            sk = -1 if ((s >> k) & 1) else 1
            sk1 = -1 if ((s >> ((k + 1) % L)) & 1) else 1
            sxx -= sk * sk1
            sx -= sk
        M[i, i] = 1536 + g_num * sxx + h_num * sx
        for k in range(L):
            k1 = (k + 1) % L
            s2 = s ^ (1 << k) ^ (1 << k1)
            j = idx[s2]
            M[i, j] += 128 if (twist and k == 7) else -128
    return M


def build_exact_int_blocks_lean(twist: bool) -> list[np.ndarray]:
    """6 exact {-1, 0, +1} orthogonal basis matrices in Lean's `sectorState` basis."""
    L = 8
    states = lean_even_x_states(L)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)

    R = np.zeros((n, n), dtype=np.int64)
    S4 = np.zeros((n, n), dtype=np.int64)
    S2 = np.zeros((n, n), dtype=np.int64)
    for i, s in enumerate(states):
        R[idx[rev(s)], i] = 1
        s4_sign = -1 if (twist and (s & 0xF).bit_count() % 2 == 1) else 1
        S4[idx[rot(s, 4)], i] = s4_sign
        s2_sign = -1 if (twist and ((s >> 6) & 0x3).bit_count() % 2 == 1) else 1
        S2[idx[rot(s, 2)], i] = s2_sign

    H_test = build_H8_shift_int_lean(16, 48, twist)
    assert np.array_equal(H_test @ R, R @ H_test)
    assert np.array_equal(H_test @ S4, S4 @ H_test)
    assert np.array_equal(H_test @ S2, S2 @ H_test)

    I = np.eye(n, dtype=np.int64)
    specs = [
        (I + S4) @ (I + R) @ (I + S2),
        (I + S4) @ (I + R) @ (I - S2),
        (I + S4) @ (I - R) @ (I + S2),
        (I + S4) @ (I - R) @ (I - S2),
        (I - S4) @ (I + R),
        (I - S4) @ (I - R),
    ]
    blocks = []
    for P in specs:
        cols = []
        seen = set()
        for j in range(n):
            col = P[:, j]
            if not np.any(col):
                continue
            g = int(np.gcd.reduce(np.abs(col)))
            col = col // g
            first_nz = int(np.flatnonzero(col)[0])
            if col[first_nz] < 0:
                col = -col
            key = tuple(col.tolist())
            if key not in seen:
                seen.add(key)
                cols.append(col)
        B = np.column_stack(cols)
        G = B.T @ B
        assert np.array_equal(G, np.diag(np.diag(G)))
        blocks.append(B)

    assert sum(B.shape[1] for B in blocks) == n
    for a in range(len(blocks)):
        for b in range(a + 1, len(blocks)):
            assert np.all(blocks[a].T @ blocks[b] == 0)
            assert np.all(blocks[a].T @ H_test @ blocks[b] == 0)
    return blocks


def rat_exp_neg_upper(x: Fraction, k: int = 6, N: int = 10) -> Fraction:
    """Matches `BlockGershgorin.ratExpNegUpper x k N` exactly."""
    y = x / (1 << k)
    s = Fraction(1)
    term = Fraction(1)
    for j in range(N):
        term = term * y / (j + 1)
        s += term
    # Repeated squaring k times
    p = s
    for _ in range(k):
        p = p * p
    return Fraction(1, p)


def fmt_int(n: int) -> str:
    """Emit raw Lean 4 `Int` constructor (zero OfNat/Neg typeclass synthesis,
    already in kernel constructor normal form for `decide +kernel`)."""
    if n >= 0:
        return f"Int.ofNat {n}"
    return f"Int.negSucc {-n - 1}"


def fmt_rat(q: Fraction) -> str:
    if q.denominator == 1:
        return f"({fmt_int(q.numerator)} : ℚ)"
    return f"(mkRat ({fmt_int(q.numerator)}) {q.denominator})"


def emit_basis_lean(out_dir: str, blocks_by_twist: dict[bool, list[np.ndarray]]) -> None:
    lines = [
        "import PurityBootstrap.BlockGershgorin",
        "",
        "/-!",
        "# Exact Sparse `{-1, 0, +1}` Symmetry Bases for `L = 8` Candidate E Blocks",
        "",
        "Generated in Lean's exact `sectorState 8 false i` basis ordering.",
        "-/",
        "",
        "namespace PurityBootstrap.CandidateE",
        "",
    ]
    for twist, name in [(False, "BcolsUntwisted"), (True, "BcolsTwisted")]:
        all_cols = []
        for B in blocks_by_twist[twist]:
            for j in range(B.shape[1]):
                col = B[:, j]
                nz = [(int(r), int(col[r])) for r in range(128) if col[r] != 0]
                all_cols.append(nz)
        assert len(all_cols) == 128
        lines.append(f"def {name} : List (List (ℕ × ℤ)) := [")
        for idx, nz in enumerate(all_cols):
            entries = ", ".join(f"Prod.mk {r} ({fmt_int(v)})" for r, v in nz)
            comma = "," if idx + 1 < len(all_cols) else ""
            lines.append(f"  [{entries}]{comma}")
        lines.append("]")
        lines.append("")
    lines.append("end PurityBootstrap.CandidateE")
    lines.append("")
    path = os.path.join(out_dir, "Basis.lean")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    print(f"Wrote {path} ({os.path.getsize(path):,} bytes)")


def compute_corner_cert(
    g_num: int, h_num: int, twist: bool, blocks: list[np.ndarray], scale_bits: int = 22
) -> dict:
    S = 1 << scale_bits
    S2 = S * S
    Hshift = build_H8_shift_int_lean(g_num, h_num, twist)

    block_data = []
    e1_max = 0
    offset = 0
    for B in blocks:
        m = B.shape[1]
        D = [int(x) for x in np.diag(B.T @ B)]
        Hb = (B.T @ Hshift @ B).tolist()
        Hb_int = [[int(x) for x in row] for row in Hb]

        inv_sqrt_D = 1.0 / np.sqrt(np.array(D, dtype=np.float64))
        H_norm = (inv_sqrt_D[:, None] * np.array(Hb_int, dtype=np.float64)) * inv_sqrt_D[None, :]
        _, evecs = np.linalg.eigh(H_norm)
        C_int = np.round((inv_sqrt_D[:, None] * evecs) * S).astype(object)

        D_obj = np.array(D, dtype=object)
        Hb_obj = np.array(Hb_int, dtype=object)
        G1 = C_int.T @ (D_obj[:, None] * C_int)
        G2 = C_int.T @ (Hb_obj @ C_int)

        for i in range(m):
            err = int(abs(G1[i, i] - S2) + sum(abs(G1[i, j]) for j in range(m) if j != i))
            if err > e1_max:
                e1_max = err

        g2_los = []
        for i in range(m):
            off = int(sum(abs(G2[i, j]) for j in range(m) if j != i))
            lo = int(G2[i, i]) - off
            assert lo >= 0, f"Negative g2_lo={lo}!"
            g2_los.append(lo)

        Ccols = [[int(C_int[r, c]) for r in range(m)] for c in range(m)]
        block_data.append({
            "offset": offset,
            "dim": m,
            "diagD": D,
            "Hb": Hb_int,
            "Ccols": Ccols,
            "g2_los": g2_los,
        })
        offset += m

    assert offset == 128
    assert e1_max < S2

    # Compute xlo using global e1_max
    tail_val = rat_exp_neg_upper(Fraction(45), 6, 10)
    total_U = Fraction(0)
    for bd in block_data:
        xlos = []
        for lo in bd["g2_los"]:
            x_exact = Fraction(6 * lo, 128 * (S2 + e1_max))
            if x_exact >= 45:
                x_lo = Fraction(45)
                total_U += tail_val
            else:
                # Round DOWN to 1/10^5 grid
                x_lo = Fraction((x_exact.numerator * 10**5) // x_exact.denominator, 10**5)
                assert x_lo * 128 * (S2 + e1_max) <= 6 * lo
                total_U += rat_exp_neg_upper(x_lo, 6, 10)
            xlos.append(x_lo)
        bd["xlo"] = xlos

    # Round total_U UP to a clean rational with denominator 10^14
    denom = 10**14
    u_num = (total_U.numerator * denom + total_U.denominator - 1) // total_U.denominator
    U_clean = Fraction(u_num, denom)
    assert total_U <= U_clean

    return {
        "S": S,
        "e1_max": e1_max,
        "blocks": block_data,
        "U_exact": total_U,
        "U_clean": U_clean,
    }


def emit_corner_lean(
    out_dir: str, g_num: int, h_num: int, cert_u: dict, cert_t: dict
) -> None:
    mod_name = f"Corner{g_num}_{h_num}"
    lines = [
        "import PurityBootstrap.BlockGershgorin",
        "import PurityBootstrap.CandidateE.Basis",
        "",
        "/-!",
        f"# Pure-Kernel `L = 8` Gershgorin Certificate for Candidate E Corner `({g_num}/128, {h_num}/128)`",
        "",
        "Both untwisted (`t = +1`) and twisted (`t = -1`) 128-dim even-`X` blocks are verified",
        "entirely inside Lean 4's kernel via `decide +kernel` (zero `native_decide`, zero `sorry`).",
        "-/",
        "",
        "namespace PurityBootstrap.CandidateE",
        "",
        "open PurityBootstrap.MatrixTools PurityBootstrap.IsingHamiltonian PurityBootstrap.BlockGershgorin",
        "",
    ]

    for tag, twist_str, basis_name, cert in [
        ("untw", "false", "BcolsUntwisted", cert_u),
        ("tw", "true", "BcolsTwisted", cert_t),
    ]:
        def_name = f"blocks_{g_num}_{h_num}_{tag}"
        bnames = []
        for bi, bd in enumerate(cert["blocks"]):
            bname = f"blk_{g_num}_{h_num}_{tag}_{bi}"
            bnames.append(bname)
            lines.append(f"private def {bname} : BlockCert :=")
            lines.append("  { offset := " + str(bd["offset"]) + ",")
            lines.append("    dim := " + str(bd["dim"]) + ",")
            lines.append("    diagD := [" + ", ".join(fmt_int(x) for x in bd["diagD"]) + "],")
            lines.append("    Hb := [")
            for ri, row in enumerate(bd["Hb"]):
                rc = "," if ri + 1 < len(bd["Hb"]) else ""
                lines.append("      [" + ", ".join(fmt_int(x) for x in row) + "]" + rc)
            lines.append("    ],")
            lines.append("    Ccols := [")
            for ci, col in enumerate(bd["Ccols"]):
                cc = "," if ci + 1 < len(bd["Ccols"]) else ""
                lines.append("      [" + ", ".join(fmt_int(x) for x in col) + "]" + cc)
            lines.append("    ],")
            lines.append("    xlo := [" + ", ".join(fmt_rat(x) for x in bd["xlo"]) + "] }")
            lines.append("")
        lines.append(f"def {def_name} : List BlockCert := [" + ", ".join(bnames) + "]")
        lines.append("")

        U = cert["U_clean"]
        lines.append(f"def U_{g_num}_{h_num}_{tag} : ℚ := {fmt_rat(U)}")
        lines.append("")
        lines.append(
            f"private theorem cert_{g_num}_{h_num}_{tag}_ok :\n"
            f"    verifyH8Cert {g_num} {h_num} {twist_str} {cert['S']} {cert['e1_max']} "
            f"{basis_name} {def_name} U_{g_num}_{h_num}_{tag} = true := by\n"
            f"  decide +kernel"
        )
        lines.append("")
        lines.append(
            f"theorem corner_{g_num}_{h_num}_{tag}_matZ_le :\n"
            f"    matZ (H_ising 8 (({g_num} : ℝ) / 128) (({h_num} : ℝ) / 128) {twist_str} false)\n"
            f"      (H_ising_isHermitian 8 _ _ {twist_str} false) 6 ≤\n"
            f"      Real.exp 72 * (U_{g_num}_{h_num}_{tag} : ℝ) :=\n"
            f"  certify_H8_matZ_upper {g_num} {h_num} {twist_str} {cert['S']} {cert['e1_max']} "
            f"{basis_name} {def_name} U_{g_num}_{h_num}_{tag} cert_{g_num}_{h_num}_{tag}_ok"
        )
        lines.append("")

    lines.append(f"def U_{g_num}_{h_num}_plus : ℚ := U_{g_num}_{h_num}_untw + U_{g_num}_{h_num}_tw")
    lines.append("")
    lines.append(
        f"theorem corner_{g_num}_{h_num}_Zplus_le :\n"
        f"    matZ (H_ising 8 (({g_num} : ℝ) / 128) (({h_num} : ℝ) / 128) false false)\n"
        f"      (H_ising_isHermitian 8 _ _ false false) 6 +\n"
        f"    matZ (H_ising 8 (({g_num} : ℝ) / 128) (({h_num} : ℝ) / 128) true false)\n"
        f"      (H_ising_isHermitian 8 _ _ true false) 6 ≤\n"
        f"      Real.exp 72 * (U_{g_num}_{h_num}_plus : ℝ) := by\n"
        f"  have h1 := corner_{g_num}_{h_num}_untw_matZ_le\n"
        f"  have h2 := corner_{g_num}_{h_num}_tw_matZ_le\n"
        f"  unfold U_{g_num}_{h_num}_plus\n"
        f"  push_cast\n"
        f"  linarith"
    )
    lines.append("")
    lines.append("end PurityBootstrap.CandidateE")
    lines.append("")

    path = os.path.join(out_dir, f"{mod_name}.lean")
    with open(path, "w") as f:
        f.write("\n".join(lines))
    print(
        f"Wrote {path} ({os.path.getsize(path):,} bytes): "
        f"U_untw={float(cert_u['U_clean']):.10e}, U_tw={float(cert_t['U_clean']):.10e}, "
        f"U_plus={float(cert_u['U_clean'] + cert_t['U_clean']):.10e}"
    )


def main() -> None:
    out_dir = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "PurityBootstrap",
        "CandidateE",
    )
    os.makedirs(out_dir, exist_ok=True)

    blocks_by_twist = {
        False: build_exact_int_blocks_lean(False),
        True: build_exact_int_blocks_lean(True),
    }
    emit_basis_lean(out_dir, blocks_by_twist)

    for g_num, h_num in [(15, 47), (15, 48), (16, 47), (16, 48)]:
        cert_u = compute_corner_cert(g_num, h_num, False, blocks_by_twist[False], scale_bits=22)
        cert_t = compute_corner_cert(g_num, h_num, True, blocks_by_twist[True], scale_bits=22)
        emit_corner_lean(out_dir, g_num, h_num, cert_u, cert_t)


if __name__ == "__main__":
    main()
