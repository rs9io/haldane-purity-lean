#!/usr/bin/env python3
"""Rigorous 160-bit Arb verification of the chi=32 periodic two-site integer MPS
trial Rayleigh quotient for Candidate A (Delta=1, D=1/4) at L = 72, 84, 112.

Verifies strictly that the L=112 periodic trial energy per site lies below -1.242818,
providing a variational upper bound E_0(112) / 112 < -1.242818 (hence Z_112(b) > 1).
Requires `python-flint` (`flint` module). Uses explicit runtime checks (never bare `assert`).
"""
from pathlib import Path
import numpy as np
import flint as f


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(msg)


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    npz_path = root / "data" / "trial32_dyadic14.npz"
    if not npz_path.exists():
        npz_path = Path(__file__).resolve().parent / "trial32_dyadic14.npz"
    require(npz_path.exists(), f"Missing trial witness tensor: {npz_path}")

    f.ctx.prec = 160
    f.ctx.threads = 4
    d = 32
    q = np.load(npz_path)
    a, b = q["A"], q["B"]
    s = [1, 0, -1]
    K = np.zeros((9, 9), dtype="int64")
    for i in range(3):
        for j in range(3):
            K[3 * i + j, 3 * i + j] = 8 * s[i] * s[j] + s[i] ** 2 + s[j] ** 2
            if i < 2 and j > 0:
                K[3 * i + j, 3 * (i + 1) + j - 1] = 8
            if i > 0 and j < 2:
                K[3 * i + j, 3 * (i - 1) + j + 1] = 8

    def orientation(x, y):
        require(d * int(np.max(abs(x))) * int(np.max(abs(y))) < 2**63, "int64 overflow in A@B")
        C = (x.reshape(-1, d) @ y.reshape(d, -1)).reshape(d, 3, 3, d).transpose(1, 2, 0, 3).reshape(9, d, d)
        mx = int(np.max(abs(C)))
        require(9 * int(np.max(abs(K))) * mx < 2**63, "int64 overflow in K@C")
        KC = (K @ C.reshape(9, -1)).reshape(9, d, d)
        require(9 * mx * max(mx, int(np.max(abs(KC)))) < 2**63, "int64 overflow in transfer kron")

        def mat(v):
            t = sum(np.kron(u, w) for u, w in zip(v, C))
            return f.arb_mat(f.fmpz_mat(t.tolist())) * (f.arb(2) ** (-56))

        T = mat(C)
        H = mat(KC)
        out = {}
        for n in (72, 84, 112):
            P = T ** (n // 2 - 1)
            norm = (T * P).trace()
            require(bool(norm > 0), f"Non-positive MPS norm at n={n}: {norm}")
            out[n] = (H * P).trace() / (8 * norm)
            print("one bond", n, out[n], flush=True)
        return out

    left = orientation(a, b)
    right = orientation(b, a)
    threshold = -f.arb(1242818) / 1000000
    for n in left:
        e = (left[n] + right[n]) / 2
        clears = bool(e < threshold)
        print("rigorous periodic trial Rayleigh quotient per site", n, e, "clears -1.242818:", clears, flush=True)
        if n == 112:
            require(clears, f"L=112 trial energy {e} failed to clear -1.242818")


if __name__ == "__main__":
    main()
