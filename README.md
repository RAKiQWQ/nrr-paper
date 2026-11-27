# Non-Prime-Power Counterexamples to the Generalized Nandakumar–Ramana Rao Problem in Dimension at Least Three

**Authors:** GPT 6.2 Astra, GPT 6.1 Sol, Gemini 4 Neon, Claude Fable 5.2

This repository contains the English mathematical manuscript ([`paper/main.tex`](paper/main.tex)), its compiled [PDF](paper/main.pdf), and the companion exact rational arithmetic verification script ([`scripts/verify.py`](scripts/verify.py)).

> **Formalization note:** A Lean 4 formalization of the full classification (combining these counterexamples with the prime-power positive direction) is currently in progress and will be published separately once the complete classification theorem passes full verification.

## Main Results

1. **Prescribed-body, prescribed-measure counterexamples (Theorem 1.1).**
   For every dimension $d \ge 3$, every non-prime-power integer $n \ge 2$, every prescribed full-dimensional compact convex body $K \subset \mathbb{R}^d$, and every prescribed absolutely continuous probability measure $\mu$ on $K$, there exist $d - 1$ Hausdorff-continuous real-valued functionals $\varphi_1, \dots, \varphi_{d-1}$ on all nonempty compact convex subsets of $\mathbb{R}^d$ that admit no $\mu$-equipartitioned fair convex $n$-partition of $K$.
2. **Robustness & pointwise classification (Corollaries 1.2–1.3).**
   The same functionals obstruct approximate equipartitions with a uniform positive gap $\varepsilon > 0$. Combined with the prime-power existence theorem of Karasev–Hubard–Aronov and Blagojević–Ziegler, universal fairness holds for $(K, \mu)$ in dimension $d \ge 3$ if and only if $n$ is a prime power.
3. **Dimension-uniform rational polynomial obstruction on cubes (Theorem 1.4).**
   For each non-prime-power $n \ge 2$, there exists a single pair of rational polynomials $P_n, Q_n \in \mathbb{Q}[X_1, X_2, X_3, X_4]$ such that in every dimension $d \ge 3$, the functionals $P_n(M(C))$, $Q_n(M(C))$ applied to four low-order volume moments $M(C) = (\langle x_1 \rangle_C, \langle x_2 \rangle_C, \langle (1+x_1)z \rangle_C, \langle x_2 z \rangle_C)$ together with the remaining $d - 3$ coordinate first moments $\langle x_j \rangle_C$ obstruct every equal-volume convex $n$-partition of $[-1,1]^d$.

## Repository Layout

- `paper/main.tex` — Complete self-contained English LaTeX manuscript (`amsart`).
- `paper/main.pdf` — Compiled PDF manuscript, committed alongside the LaTeX source.
- `scripts/verify.py` — Self-contained Python 3 script (standard library only) performing exact rational arithmetic checks for the internal binomial gcd criterion ($n = 2, \dots, 200$), the piecewise-linear winding construction and end-winding sums ($n \in \{6, 10, 12, 15\}$), $324$ exact interpolation nodes for the four-moment slope inversion on the cube, the $3$-dimensional spherical cap bound at $1/\sqrt{2}$, and the positive-weight rebalancing on an asymmetric pyramid.
- `.github/workflows/build-paper.yml` — GitHub Actions workflow that runs `scripts/verify.py` and compiles `paper/main.tex` to PDF (available as a workflow artifact on every push).

## Building Locally

Run the exact rational arithmetic checks:

```bash
python3 scripts/verify.py
```

Compile the LaTeX manuscript (requires a TeX distribution such as TeX Live or MiKTeX with `latexmk` or `pdflatex`):

```bash
latexmk -pdf -outdir=build paper/main.tex
```
