# The planar construction for non-prime-power sizes

Identify $\mathbb C$ with $\mathbb R^2$ and take counterclockwise winding to be positive. Positive homogeneity refers to scaling by positive real numbers. The geometric proof uses the following lemma to perturb the functional on a single piece. [Geometric proof](geometric-proof.md) · [Lean construction](../../formalization/NRR/PlanarExistence.lean)

**Local lemma.** For each non-prime-power integer $n\ge 2$, there are a positively homogeneous function $f:\mathbb C\to\mathbb C$ of degree two, bounded continuous functions $\Delta_i:\mathbb C\to\mathbb C$ for $i\ne2$, and a bounded continuous function $D:\mathbb C^2\to\mathbb C$ with the following properties.

1. If $\sum_{i=1}^n w_i=0$ and all $f(w_i)$ are equal, then all $w_i=0$.
2. Given $p_0=p_n=0$ and arbitrary $p_1,\ldots,p_{n-1}\in\mathbb C$, put $w_i=p_i-p_{i-1}$. At least two of the following $n$ values differ.

$$
f(w_2)+D(p_1,-p_2),\qquad
     f(w_i)+\Delta_i(w_i)\quad(i\ne2).
$$

Only the two interfaces bounding the second piece enter its correction. The Lean declarations for these two properties are `balanced_square_rigidity` and `LocalModel.exists_planar_correction`. [Theorem index](../../formalization/docs/theorem-index.md)

## 1. Realizing the winding numbers by a rational polygonal path

Let $m=\lfloor n/2\rfloor$. The gcd of the interior binomial coefficients is $p$ when $n=p^a$ is a prime power and is $1$ otherwise. To see this, fix a prime $p$ and write $n=p^a b$ with $p\nmid b$. Over $\mathbb F_p$ we have $(1+X)^n=(1+X^{p^a})^b$. If $b>1$, the interior coefficient of $X^{p^a}$ is $b\ne0\bmod p$. If $b=1$ and $a\ge1$, all interior coefficients are divisible by $p$, and

$$
\binom{p^a}{p^{a-1}}=p\binom{p^a-1}{p^{a-1}-1}
$$

has precisely one factor of $p$, since $(1+X)^{p^a-1}=(1+X^{p^a})/(1+X)\bmod p$. For the $n$ of the lemma, symmetry and Bézout's identity therefore give integers $A_1,\ldots,A_m$ with $1+\sum_{j=1}^m A_j\binom nj=0$.

Set $d_0=d_n=1$ and $d_j=d_{n-j}=A_j$ for $1\le j<n/2$. For even $n$, set $d_{n/2}=2A_m$. Then

$$
\frac12\sum_{j=0}^n\binom nj d_j=0. \tag{1}
$$

For $0<j<n$ put $c_j=1-2j/n$, and let $r=1/(4n)$. Start in the $(s,b)$-plane at $(0,r)$. For each positive $c_j$, travel horizontally to $(c_j,r)$, make $d_j-1$ oriented turns around the diamond centered at $(c_j,0)$ with vertices at distance $r$, and retrace the horizontal segment. A positive turn is counterclockwise. Next make $k$ turns around the corresponding diamond at the origin, where $k=A_m$ for even $n$ and $k=0$ for odd $n$. Follow its right half clockwise from $(0,r)$ to $(0,-r)$. Complete the loop by traversing the negative of this first path with the same parametrization.

The path avoids every $(c_j,0)$ and satisfies $|s|<1$. The connecting segments cancel in pairs. The second half rotates each turn to the opposite puncture with the same orientation, and the diamond radius is smaller than the distance between punctures. Thus the winding number about each nonzero $c_j$ is $d_j-1$. At the origin it is $2k-1$.

Parametrizing the first path and extending it antipodally gives odd functions $s,b$ on the unit circle. An odd Lipschitz approximation preserves the strict bound on $s$ and the windings at the finitely many punctures. This is `AngularMap.approximate_loop` in Lean. For sufficiently small $\varepsilon>0$ define

$$
h(0)=0,\qquad h(\rho u)=\rho u\big(1+s(u)+i\varepsilon b(u)\big),\quad \rho>0.
$$

Oddness gives the exact identity $h(z)-h(-z)=2z$. The radial map $R(z)=(1+s(z/|z|))z$ is bi-Lipschitz, and $B(z)=b(z/|z|)z$ is globally Lipschitz, with both maps extended by zero at the origin. Choose $\varepsilon$ so that $\varepsilon\operatorname{Lip}(B)\operatorname{Lip}(R^{-1})<1$. The contraction mapping theorem applied to $h\circ R^{-1}=\mathrm{id}+i\varepsilon B\circ R^{-1}$ gives a homeomorphism. Replacing $s,b$ by $ts,tb$ for $t\in[0,1]$ admits a uniform perturbation bound and produces a continuous isotopy $h_t$ from the identity to $h$. The corresponding Lean declarations include `AngularMap.exists_isotopy`, `continuous_isotopy`, and `antipodal_difference`.

Let $g_j(u)=jh(u)+(n-j)h(-u)$. Expanding gives

$$
\frac{g_j(u)}{u}=n(s-c_j)+i n\varepsilon b .
$$

Both coordinate scale factors are positive. Deforming them to one never crosses zero, so $\operatorname{wind}g_j=1+\operatorname{ind}_{(c_j,0)}(s,b)=d_j$ for $0<j<n$. The end curves $g_0,g_n$ also avoid zero and have winding one. Set $f(w)=(h^{-1}(w))^2$. If the common value is $\zeta^2\ne0$, each $w_i$ equals $h(\zeta)$ or $h(-\zeta)$. Their sum is a value of the nonvanishing homogeneous extension of some $g_j$. If the common value is zero, every $w_i$ vanishes. This proves the first assertion of the lemma. [Angular realization](../../formalization/NRR/AngularMap.lean) · [Square rigidity](../../formalization/NRR/LocalModel.lean)

## 2. What the second piece determines

Let $I=\{1,3,\ldots,n\}$ and number its elements in order by $j(i)$ starting at zero. Take $b_i=4^{j(i)}$ and set

$$
\nu_i=h,\qquad F_i(w)=f(w)-b_i,\qquad \Delta_i(w)=-b_i.
$$

These corrections are bounded continuous constants. The choices of $b_i$ and the exact antipodal difference of $h$ will give finiteness of all multiple readings.

The configurations in which the other $n-1$ values equal $q$ form the surface

$$
S=\{(q,(z_i)_{i\in I}): z_i^2=q+b_i\},\qquad w_i=\nu_i(z_i).
$$

Away from the branch values, $q$ is a local complex coordinate. At a branch point, the unique vanishing root $z_i$ provides a coordinate. A small loop around each branch value flips just that root, so the surface is connected and oriented. The inverse image $S_T$ of a sufficiently large closed disk $|q|\le T$ is likewise a connected compact oriented surface with boundary.

Define the map recording the two interfaces by

$$
e=(L,R)=\Big(h(z_1),\ \sum_{j=3}^n\nu_j(z_j)\Big).
$$

In the variables of the lemma this is $(p_1,-p_2)$, so $w_2=-L-R$. The value $q=(h^{-1}(L))^2-b_1$ is determined by $L$. The map $e:S\to\mathbb C^2$ is proper, since bounded $L$ bounds $q$ and every root, and $S$ is closed.

If two distinct points have the same reading, they have the same $z_1$ and $q$. On the nonempty index set $J$ where their coordinates differ, $z'_i=-z_i\ne0$. Subtracting the two second coordinates and using $h(z)-h(-z)=2z$ gives $\sum_{i\in J}z_i=0$. Eliminating the radicals using $z_i^2=q+b_i$ gives a polynomial condition on $q$ (one may take the product over all sign choices). At $q=0$ the roots are $\pm2^{j(i)}$, and the largest magnitude in any nonempty subsum exceeds the sum of all smaller ones. The polynomial is therefore nonzero and has finitely many roots. There are only finitely many possible $J$ and finitely many points over each $q$, so only finitely many points belong to multiple fibers. [Lean proof of finite multiple readings](../../formalization/NRR/RootSums.lean)

## 3. Boundary winding and extension of the correction

On $S$ put $G=f(-L-R)-q$. Each boundary component over a large circle $|q|=T$ corresponds to a pair of complementary sign choices. Parametrize it by $q=Tu^2$, $|u|=1$, with $u$ counterclockwise for the positive boundary orientation. If a sign choice has $j$ positive signs, then $z_i/\sqrt T=\pm u+O(T^{-1})$ uniformly on that component. Since $\nu_i=h$, homogeneity gives

$$
G/T\ \longrightarrow\ f(U)-u^2,\qquad U=-j h(u)-(n-1-j)h(-u).
$$

The limit avoids zero. Indeed, $U=h(u)$ or $U=h(-u)$ would give a zero of $g_{j+1}$ or $g_j$. In particular the zero set of $G$ is compact. Factor the limit as $(h^{-1}(U)-u)(h^{-1}(U)+u)$. Apply the isotopy $h_t$ to both points in each difference. The differences stay nonzero and end at $-g_{j+1}$ and $-g_j$, respectively. The winding at this end is $d_j+d_{j+1}$. Summing over all $2^{n-1}$ sign choices and dividing by two counts every component once. Pascal's identity gives

$$
\frac12\sum_{j=0}^{n-1}\binom{n-1}j(d_j+d_{j+1})
 =\frac12\sum_{j=0}^n\binom njd_j=0 .
$$

Across this family of constructions the possible total windings form exactly $1+\gcd_{0<j<n}\binom nj\,\mathbb Z$. Each pair of interior degrees may be adjusted independently, as may half the central degree for even $n$.

Choose $T$ large enough that the branch values and the projections of all multiple-fiber points and all zeros of $G$ lie in the open disk. On a connected compact oriented surface a nonzero boundary function extends through nonzero values exactly when its oriented boundary windings sum to zero. In the cohomology exact sequence the map $H^1(\partial S_T;\mathbb Z)\to H^2(S_T,\partial S_T;\mathbb Z)=\mathbb Z$ sums those windings. Represent an extending class using $S^1=K(\mathbb Z,1)$ and match the actual boundary phase on a collar. Extend the logarithm of the boundary modulus as a real function and exponentiate it. This gives a nonvanishing function on $S_T$.

Set its value to one at every multiple-fiber point as follows. Choose disjoint small interior disks about the points. In each, multiply the function by the exponential of a cutoff times a logarithm of the reciprocal of its center value, with the cutoff equal to one at the center. Gluing to $G$ outside $S_T$ gives a global nonvanishing function $\widetilde G$.

Both $q$ and $G$ are constant on each fiber of $e$, and $\widetilde G$ equals one on every multiple fiber. Thus $\widetilde G-G$ descends through the proper quotient map to a bounded continuous function on the closed image $e(S)$ and vanishes outside $e(S_T)$. Apply bounded Tietze extension to its two real coordinates and multiply by a compactly supported cutoff equal to one on $e(S_T)$. The resulting $D:\mathbb C^2\to\mathbb C$ has the required property. Whenever the other $n-1$ values agree, the corrected second value differs from their common value by $\widetilde G\ne0$.

For $n=6$, take $(A_1,A_2,A_3)=(-1,-1,1)$. Then $1-6-15+20=0$, and the degree sequence is $(1,-1,-1,2,-1,-1,1)$. Among the sixteen boundary components, five have winding $-2$, ten have winding $+1$, and one has winding zero. [Exact arithmetic check](../../scripts/verify.py)
