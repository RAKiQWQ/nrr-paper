# Non-Prime-Power Counterexamples to the Generalized Nandakumar–Ramana Rao Problem in Dimension at Least Three

**Authors:** GPT 6.2 Astra, GPT 6.1 Sol, Gemini 4 Neon, Claude Fable 5.2

[Read the paper (PDF)](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Lean theorem index](formalization/docs/theorem-index.md)

The accompanying Lean 4.24.0 project proves both directions of the pointwise classification for each prescribed body and measure. Its final declaration is `NRR.fullClassification : NRR.FullClassification`. [Theorem statement](formalization/NRR/Statement.lean) · [Proof](formalization/NRR/PrimePowerTopologyConclusion.lean) · [Verification and reproduction](formalization/docs/verification.md)

## Main Results

1. **Prescribed-body, prescribed-measure counterexamples (Theorem 1.1).**
   For every dimension $d \ge 3$, every non-prime-power integer $n \ge 2$, every prescribed full-dimensional compact convex body $K \subset \mathbb{R}^d$, and every prescribed absolutely continuous probability measure $\mu$ on $K$, there exist $d - 1$ Hausdorff-continuous real-valued functionals $\varphi_1, \dots, \varphi_{d-1}$ on all nonempty compact convex subsets of $\mathbb{R}^d$ that admit no $\mu$-equipartitioned fair convex $n$-partition of $K$.
2. **Robustness & pointwise classification (Corollaries 1.2–1.3).**
   The same functionals obstruct approximate equipartitions with a uniform positive gap $\varepsilon > 0$. Combined with the prime-power existence theorem of Karasev–Hubard–Aronov and Blagojević–Ziegler, universal fairness holds for $(K, \mu)$ in dimension $d \ge 3$ if and only if $n$ is a prime power.
3. **Dimension-uniform rational polynomial obstruction on cubes (Theorem 1.4).**
   For each non-prime-power $n \ge 2$, there exists a single pair of rational polynomials $P_n, Q_n \in \mathbb{Q}[X_1, X_2, X_3, X_4]$ such that in every dimension $d \ge 3$, the functionals $P_n(M(C))$, $Q_n(M(C))$ applied to four low-order volume moments $M(C) = (\langle x_1 \rangle_C, \langle x_2 \rangle_C, \langle (1+x_1)z \rangle_C, \langle x_2 z \rangle_C)$ together with the remaining $d - 3$ coordinate first moments $\langle x_j \rangle_C$ obstruct every equal-volume convex $n$-partition of $[-1,1]^d$.

## Repository layout

| Directory | Contents |
| --- | --- |
| [paper/](paper/) | The manuscript and its PDF. The supplementary notes give the [geometric counterexample](paper/notes/geometric-proof.md) and the [planar construction](paper/notes/planar-construction.md). |
| [formalization/](formalization/) | The Lean project, its pinned dependencies, the [theorem index](formalization/docs/theorem-index.md), and the [verification record](formalization/docs/verification.md). |
| [scripts/](scripts/) | The [exact arithmetic checks](scripts/verify.py) and the [Lean build and axiom verifier](scripts/verify-formalization.ps1). |

## Building locally

From the repository root, run the exact rational arithmetic checks with Python 3.

```bash
python3 scripts/verify.py
```

To compile the paper locally, use a TeX distribution with `latexmk`. The [GitHub Actions workflow](.github/workflows/build-paper.yml) also runs the arithmetic checks and builds the PDF.

```bash
latexmk -pdf -outdir=build paper/main.tex
```
