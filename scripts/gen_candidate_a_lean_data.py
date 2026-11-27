#!/usr/bin/env python3
"""Generate PurityBootstrap/CandidateA/Data.lean directly from round2_audit/round2-evidence/
so all 22 table rows and 16 degree-14 filter witnesses have zero transcription errors."""
import csv, json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EVID = ROOT / "round2_audit" / "round2-evidence"
OUT = ROOT / "PurityBootstrap" / "CandidateA" / "Data.lean"
OUT.parent.mkdir(parents=True, exist_ok=True)

def load_tsv(name):
    rows = []
    with (EVID / name).open() as f:
        for row in csv.DictReader(f, delimiter="\t"):
            rows.append((int(row["n"]), int(row["I"]), int(row["Rz"]), int(row["Rx"]), int(row["R4"])))
    assert [r[0] for r in rows] == list(range(4, 15))
    return rows

t155 = load_tsv("centers_15p5.tsv")
t23 = load_tsv("centers_23.tsv")
flts = json.loads((EVID / "filters.json").read_text())

def fmt_q(s):
    fr = F(s)
    return f"({fr.numerator} : ℚ) / {fr.denominator}"

def fmt_rays(key):
    lines = []
    for ray in flts[key]["rays"]:
        coeffs = ", ".join(str(c) for c in ray["coefficients"])
        lines.append(f"  ({ray['sign']}, {fmt_q(ray['cap'])}, [{coeffs}])")
    return "[\n" + ",\n".join(lines) + "\n]"

def fmt_tbl(rows):
    return "[\n" + ",\n".join(f"  ({I}, {Rz}, {Rx}, {R4})" for _, I, Rz, Rx, R4 in rows) + "\n]"

lean = f"""import Mathlib.Tactic
import PurityBootstrap.ExactCertificates

/-!
# Candidate A (`Δ = 1, D = 1/4` Spin-1 Haldane Chain): Exact Rational Tables & Filter Witnesses

Auto-generated from the Round 2 verified tables and degree-14 polynomial filters.
All 88 raw thermal trace centers (`n = 4..14`, seams `I, Rz, Rx, R4`, `b = 31/2, 23`) are
independently enclosed from pure-integer `__int128` Chebyshev contractions
(`scripts/chebyshev_enclose*.cpp`, `scripts/chebyshev_enclose_cuda.cu`) via exact
integer/rational scalar verification (`scripts/verify_candidate_a_all88.py`), with
worst-case endpoint distance `1.245 × 10⁻⁶ < 10⁻⁵` (at `n = 6, I, b = 23`) and
`≤ 7.94 × 10⁻⁸` at `n = 14`.
-/

namespace PurityBootstrap.CandidateA

/-- Raw centers `(I, Rz, Rx, R4)` in units of `10⁻⁹` for `n = 4..14` at `b = 31/2` (`a = 1.242818`). -/
def caTable155 : List (ℤ × ℤ × ℤ × ℤ) :=
{fmt_tbl(t155)}

/-- Raw centers `(I, Rz, Rx, R4)` in units of `10⁻⁹` for `n = 4..14` at `b = 23` (`a = 1.242818`). -/
def caTable23 : List (ℤ × ℤ × ℤ × ℤ) :=
{fmt_tbl(t23)}

/-- Raw trace enclosure radius `ε = 10⁻⁵`. -/
def caEps : ℚ := 1 / 100000

/-- Sector-projected tolerance `ε` for sectors `0, 2` and `ε/2` for sectors `1, 3`. -/
def caSectorEps (sec : Fin 4) : ℚ :=
  match sec.val with
  | 0 => caEps
  | 1 => caEps / 2
  | 2 => caEps
  | _ => caEps / 2

/-- Raw center `(I, Z, X, F)` divided by `10⁹` at length `n ∈ [4..14]`. -/
def caRawQuad (tbl : List (ℤ × ℤ × ℤ × ℤ)) (n : ℕ) : ℚ × ℚ × ℚ × ℚ :=
  if 4 ≤ n ∧ n ≤ 14 then
    match tbl[n - 4]? with
    | some (i, z, x, f) => ((i : ℚ) / 10^9, (z : ℚ) / 10^9, (x : ℚ) / 10^9, (f : ℚ) / 10^9)
    | none => (0, 0, 0, 0)
  else (0, 0, 0, 0)

/-- Projected `D₄` sector center for `sec ∈ Fin 4` at length `n ∈ [4..14]`:
- `0`: `(I + Z + 4X + 2F) / 8` (mult 1)
- `1`: `(I + Z - 2F) / 8` (mult 2)
- `2`: `(I + Z - 4X + 2F) / 8` (mult 1)
- `3`: `(I - Z) / 4` (mult 2) -/
def caMoment (tbl : List (ℤ × ℤ × ℤ × ℤ)) (sec : Fin 4) (n : ℕ) : ℚ :=
  let (i, z, x, f) := caRawQuad tbl n
  match sec.val with
  | 0 => (i + z + 4 * x + 2 * f) / 8
  | 1 => (i + z - 2 * f) / 8
  | 2 => (i + z - 4 * x + 2 * f) / 8
  | _ => (i - z) / 4

/-- Dominant lower threshold at `b = 31/2` and `b = 23`. -/
def caLo155 : ℚ := {fmt_q(flts['31/2']['lower'])}
def caLo23  : ℚ := {fmt_q(flts['23']['lower'])}

/-- Eight one-sided ray witnesses `(sign, cap, q_coeffs)` at `b = 31/2` (2 per sector `0..3`). -/
def caRays155 : List (ℤ × ℚ × List ℤ) :=
{fmt_rays('31/2')}

/-- Eight one-sided ray witnesses `(sign, cap, q_coeffs)` at `b = 23` (2 per sector `0..3`). -/
def caRays23 : List (ℤ × ℚ × List ℤ) :=
{fmt_rays('23')}

/-- Relative tail rational ceiling `R_rel` satisfying `(U_112(31/2) - 1)^46 ≤ R_rel^31`. -/
def caRelTail : ℚ := 6619827 / 10^8

/-- Initial and 4-round upward-rounded purity defect ceilings `(56, 23) → (896, 368)`. -/
def caP0 : ℚ := 1215302 / 10^7
def caQ0 : ℚ := 1203214 / 10^7
def caP1 : ℚ := 1118959 / 10^7
def caQ1 : ℚ := 1035508 / 10^7
def caP2 : ℚ := 858291 / 10^7
def caQ2 : ℚ := 652320 / 10^7
def caP3 : ℚ := 392260 / 10^7
def caQ3 : ℚ := 182716 / 10^7
def caP4 : ℚ := 53546 / 10^7
def caQ4 : ℚ := 9312 / 10^7

end PurityBootstrap.CandidateA
"""
OUT.write_text(lean)
print(f"Wrote {OUT} ({len(lean)} bytes)")
