# Geometric proof of the non-prime-power counterexamples

**Prescribed body and measure.** Let $d\ge3$ and let $n\ge2$ be an integer that is not a prime power. Fix a full-dimensional compact convex body $K\subset\mathbb R^d$ and an absolutely continuous probability measure $\mu$ on $K$. There are $d-1$ Hausdorff-continuous real-valued functionals on all nonempty compact convex sets such that every convex partition of $K$ into $n$ pieces of equal $\mu$-mass has two pieces with different vectors of functional values. The functionals may depend on $K,n,d,\mu$. This includes a prescribed unit ball with uniform probability and applies to partitions obtained by intersecting an ambient partition with $K$. A finite measure giving $K$ positive mass can first be restricted to $K$ and normalized.

**Uniform cube.** For each such $n$ there are polynomials $P_n,Q_n\in\mathbb Q[X_1,X_2,X_3,X_4]$ that work simultaneously for every $d\ge3$ on $K=[-1,1]^d$. Write $z=x_d$ and $\langle g\rangle_C=(n/2^d)\int_C g\,dx$. Put

$$
M(C)=\big(\langle x_1\rangle_C,\langle x_2\rangle_C,
             \langle(1+x_1)z\rangle_C,\langle x_2z\rangle_C\big).
$$

The functionals are $P_n(M(C)),Q_n(M(C))$ and the moments $\langle x_j\rangle_C$ with $3\le j\le d-1$. In dimension three only the first two occur. The four integrands have degree at most two. The proof establishes existence of the outer polynomials.

The functionals in both statements may depend on position and direction. Together with prime-power existence, the prescribed-body theorem gives the pointwise classification for $d\ge3$. Akopyan, Avvakumov, and Karasev proved the planar existence theorem for one absolutely continuous measure, one continuous functional, and an arbitrary number of parts. The Lean development proves the classification and the dimension-uniform cube theorem. [Generalized conjecture](https://arxiv.org/html/2305.10711v2#S1.Thmtheorem2) · [Prime-power theorem](https://arxiv.org/abs/1306.2741) · [Planar theorem 7.1](https://arxiv.org/html/1804.03057v14#S7.Thmtheorem1) · [Lean theorem index](../../formalization/docs/theorem-index.md)

## 1. Recognizing horizontal slabs inside a cylinder

Write points as $(u,z)\in\mathbb R^{d-1}\times\mathbb R$. Let $A=D\times[-h,h]$, where $D$ is a full-dimensional convex body with centroid zero. Suppose full-dimensional compact convex pieces partition $A$ and the integral of $u$ over each piece is zero. Then the pieces are horizontal slabs, possibly of different thicknesses.

Let $l_i(u)$ be the length of the vertical fiber of piece $i$, extended by zero outside its horizontal projection. Let $\nu$ be uniform probability on $D$ and put $m_i=\int l_i\,d\nu>0$. On its convex projection, $l_i$ is concave. The probability measure $l_i\,d\nu/m_i$ has centroid zero and full-dimensional support, hence zero lies in the interior of the projection. Jensen's inequality and the second-moment inequality give

$$
l_i(0)\ \ge\ m_i^{-1}\int l_i^2\,d\nu\ \ge\ m_i .
$$

Over an interior projection point, the open fiber segment lies in the interior of the piece. This follows from continuity of the two endpoint functions there. Thus $\sum_i l_i(0)\le2h=\sum_i m_i$, so equality holds in both inequalities for every $i$. It follows that $l_i=m_i$ almost everywhere on $D$. The closed projection is all of $D$, and each fiber over its interior has length $m_i$. The open intervals have positive length and disjoint interiors. Their endpoints vary continuously, so their order is constant on the connected set $\operatorname{int}D$. Adding the thicknesses from $-h$ and taking closures gives the slabs.

If $A\subset K$ and every piece of a convex partition of $K$ meets $A$ in positive volume, the slabs also determine the partition outside $A$. The common interface of two consecutive slabs contains a relatively open patch of a horizontal hyperplane. Any hyperplane weakly separating the two full pieces must contain the patch and must therefore be that horizontal plane. Each piece lies between its two adjacent separating planes, with just one constraint at either end. Since the pieces cover $K$, each open slab belongs to its assigned piece. Taking closures recovers the horizontal partition of $K$.

## 2. Making every piece meet an inner cylinder in the unit ball

Let $B$ be the unit ball. The space $\mathscr P_\mu$ of equal-$\mu$-mass convex partitions is compact in the product Hausdorff topology modulo permutations. Blaschke selection gives convergent subsequences for the individual pieces. Their limits still cover $B$. Under Hausdorff convergence of compact convex sets, the indicators converge pointwise off the boundary of the limit, so both volume and $\mu$-mass converge. Each limit piece has mass $1/n$ and therefore has interior. Since their volumes sum to the volume of their union, their interiors are pairwise disjoint. The same argument applies to the cube.

Write $F(t)=\mu(B\cap\{z\le t\})$ and $J_i=F^{-1}(i/n)\cap[-1,1]$ for $1\le i<n$. Continuity and monotonicity of $F$ make the $J_i$ nonempty compact intervals strictly ordered in $(-1,1)$ with positive distances between them. Choosing one cutting height from each interval gives the compact family $\mathscr H$ of horizontal equal-mass partitions. For the uniform ball, each interval is a singleton.

Absolute continuity gives a common lower bound $v_0>0$ for the ordinary volume of a piece of mass $1/n$. Choose $0<t<1$ so that each of the caps $z>t$ and $z<-t$ has volume less than $v_0/2$. Then the ordinary volume centroid of every such piece satisfies $|\bar z|\le(1+t)/2<1$. Choose $h<1$ larger than this bound and larger than the absolute value of every height in the $J_i$. Choose $a>0$ with $a^2+h^2<1$. Define

$$
D=\{|u|\le a\},\quad A=D\times[-h,h]\subset B,\quad
 \kappa=\int_D u_1^2\,du>0,\qquad
 W_\delta(C)=\kappa^{-1}\left(\int_{C\cap A}u\,dx+\delta\int_C u\,dx\right).
 \tag{2}
$$

Both integrals vary continuously on compact convex sets in the Hausdorff metric. For the first, integrate with the indicator of the fixed cylinder. For every partition of $B$, the sum of $W_\delta$ over its pieces is zero by the symmetry $u\mapsto-u$ of both $A$ and $B$.

**Localization lemma.** Given any open neighborhood $U$ of $\mathscr H$ in $\mathscr P_\mu$, there is $\delta_0>0$ such that for $0<\delta<\delta_0$ every partition with $W_\delta(C_i)=0$ for all $i$ belongs to $U$.

Otherwise take $\delta_k\downarrow0$ and a sequence of such partitions outside $U$, converging piecewise to a partition $(C_i)$. Every limit piece satisfies $\int_{C_i\cap A}u\,dx=0$. To show every intersection has positive volume, suppose a limit piece $C$ misses the interior of $A$. Orient a nonzero weak separating normal $(p,b)$ so that

$$
p\cdot u+bz\ \ge\ a|p|+h|b|\qquad ((u,z)\in C).
 \tag{3}
$$

The right-hand side is the maximum on $A$. If $p=0$ the whole piece lies beyond an end of the cylinder, contradicting $|\bar z|<h$. Integrating (3) over $C$ therefore gives

$$
p\cdot\bar u\ \ge\ a|p|+h|b|-b\bar z\ \ge\ a|p|>0 .
$$

Every point of $C\cap A$ satisfies $p\cdot u=a|p|$, since $p\cdot u$ and $bz$ must each attain their maximum on $A$. By compactness, all points in the approximating intersections $C_k\cap A$ have $p\cdot u>a|p|/2$ for all sufficiently large $k$. This also covers an empty intersection. Meanwhile $\int_{C_k}p\cdot u\,dx>0$ for large $k$. Pairing (2) with $p$ gives a nonnegative first term and a strictly positive second term, contradicting $W_{\delta_k}(C_k)=0$. Thus each limit piece meets the interior of $A$ and, by convexity and full dimension, intersects $A$ in positive volume. Section 1 now identifies the limit as an element of $\mathscr H$, contradicting the closedness of the complement of $U$.

**Six equal-volume parts of the three-dimensional ball.** In this case one can take $\delta=0$. Set $a=h=1/\sqrt2$. The closed cylinder lies in the unit ball and contains the concentric ball of radius $1/\sqrt2$. A convex piece missing the interior of the cylinder lies in a cap cut by a separating plane at distance at least $1/\sqrt2$ from the center. In dimension three the volume fraction of a one-sided unit ball cap above height $s$ is $(2-3s+s^3)/4$. At $s=1/\sqrt2$ this gives

$$
\frac12-\frac{5}{8\sqrt2}<\frac16 .
$$

Every piece of volume fraction $1/6$ therefore enters the cylinder, and Section 1 applies directly when $W_0=0$. The five internal horizontal sixth-quantiles lie strictly between the cylinder ends since each end cap has volume less than one piece.

## 3. Applying the planar correction to partitions of the ball

In a neighborhood of $\mathscr H$, every partition has a bottom-to-top labeling with interfaces $z=b_i+a_i\cdot u$, $1\le i<n$, of small slope and with $b_i$ close to $J_i$. To see that these charts contain every nearby partition, first observe that nonadjacent pieces of a reference horizontal partition have positive distance. They remain disjoint under small perturbations. The union of the first $j$ pieces therefore meets the union of the remaining pieces only in $C_j\cap C_{j+1}$.

Weakly separate these two adjacent pieces by a hyperplane. On each strict side, the intersection with the ball is connected. The two unions are relatively closed there, disjoint, and cover the side. Each adjacent piece has an interior point strictly on its own side, so each side is occupied by the corresponding union. Taking closures gives the two closed caps. Along any sequence tending to a reference partition, a convergent subsequence of the oriented separating planes has a limit containing an open patch of the reference interface. The limit plane must therefore be the corresponding horizontal one. Compactness of $\mathscr H$ gives a uniform chart neighborhood.

Slightly enlarge the $J_i$ to pairwise separated closed intervals within $(-h,h)$. Choose a slope bound that keeps the graphs strictly ordered over the horizontal projection of the ball and inside $(-h,h)$ over $D$. Allow intercepts and slopes to vary independently in these compact sets. Let $\mathcal D_i$ consist of all resulting individual pieces at level $i$, omitting the absent interface at each end. The $\mathcal D_i$ are compact and pairwise disjoint. The endpoints on the vertical axis distinguish the levels. The map from parameters to a piece is continuous by approximation from strict interior points and the closed half-space inequalities. Each active bounding plane contains an open patch inside the cylinder, so the piece determines its parameters uniquely. Compactness gives continuity of the inverse. Shrink $U$ so that the pieces of every partition in it belong to these families. This construction also allows quantile intervals of positive length.

Fix $\delta$ for this $U$ using Section 2. For interface $H_i=\{z=b_i+a_i\cdot u\}$, define

$$
P_i=a_i+\frac{\delta}{\kappa}\int_{B\cap\{z\le b_i+a_i\cdot u\}}u\,dx,
 \qquad P_0=P_n=0 .
$$

This vector depends only on the interface. Because $\int_D u\,du=0$ and $\int_D uu^\top du=\kappa I$, the integral of $u$ over the part of the cylinder below this plane is exactly $\kappa a_i$. The integral over each of the full cylinder and the full ball vanishes, so subtracting consecutive prefixes gives

$$
W_\delta(C_i)=P_i-P_{i-1}. \tag{4}
$$

This identity holds for the intercepts selected by any of the prescribed measures.

For the ball one can also check the direction of $P_i$. Write $s=b_i/\sqrt{1+|a_i|^2}$ and let $\omega_{d-1}$ be the volume of the unit $(d-1)$-ball. Along the unit normal $(-a_i,1)/\sqrt{1+|a_i|^2}$, the cap's axial first moment is $\omega_{d-1}\int_{-1}^s y(1-y^2)^{(d-1)/2}\,dy=-\omega_{d-1}(1-s^2)^{(d+1)/2}/(d+1)$. Hence $P_i$ is a strictly positive multiple of $a_i$. Equation (4) shows that all $W_\delta(C_i)$ vanish in this neighborhood exactly when every cut is horizontal. The localization lemma identifies the entire set of zero-moment partitions with $\mathscr H$.

Identify the first two horizontal coordinates with $\mathbb C$ by the projection $\pi$, and write $\pi'$ for the remaining coordinates (none for $d=3$). Take $f,\Delta_i,D_*$ from the planar lemma, with $D_*$ its two-variable correction. The base test is

$$
\Phi_0(C)=(f(\pi W_\delta(C)),\ \pi'W_\delta(C)).
$$

If its values agree on all pieces, the $\pi'$ coordinates vanish because their sum is zero. The first assertion of the planar lemma gives $\pi W_\delta(C_i)=0$ for every $i$. All fair solutions of this base test therefore lie in $U$. On the compact complement the diameter $\max_{i,j}\|\Phi_0(C_i)-\Phi_0(C_j)\|$ has a strictly positive minimum whenever the complement is nonempty. [Planar lemma](planar-construction.md)

For $\sigma>0$, define one complex function on the disjoint sets $\mathcal D_i$ by

$$
\begin{split}
  E_\sigma(C)&=\sigma^2\Delta_i(\pi W_\delta(C)/\sigma) &&(i\ne2),\\
  E_\sigma(C)&=\sigma^2D_*(\pi P_1/\sigma,-\pi P_2/\sigma) &&(i=2).
 \end{split}
$$

The second piece determines both interfaces, including when it occurs in another partition. The function is continuous on the finite union of compact sets. Extend its two real coordinates by bounded Tietze extension to the Hausdorff space of all nonempty compact convex sets, with $\|E_\sigma\|_\infty\le M\sigma^2$ for a constant independent of $\sigma$. Add $E_\sigma$ to the first coordinate of $\Phi_0$. Inside $U$, divide the complex value by $\sigma^2$. Equation (4) and degree-two homogeneity give exactly the tests in the second assertion of the planar lemma at parameters $\pi P_i/\sigma$, so the values cannot all agree. Outside $U$ choose $2M\sigma^2$ smaller than the positive minimum above. The same functionals now work on all partitions of the ball.

For these fixed functionals the test diameter has a strictly positive minimum on all equal-mass partitions. To use ordinary volume moments, apply the real Stone–Weierstrass theorem on the compact family of convex pieces $C\subset B$ with $\mu(C)=1/n$. Polynomial moments separate these full-dimensional convex sets. Indeed, polynomials are dense among continuous functions on $B$, and equality of the restricted volume measures determines a closed convex set with interior. The first two functionals can thus be approximated by rational polynomials in finitely many ordinary volume moments. For the remaining $d-3$ additive functionals, approximate the coordinate integrands of (2) by rational polynomials in $L^1(B)$. The integral error is uniform in $C\subset B$, preserving additivity and, for sufficiently accurate approximation, the positive gap. This argument gives no bound on the moment orders.

### 3.1 A prescribed convex body

For a general $K$ we need an interior chord crossing every horizontal quantile plane and a positive weight with total horizontal moment zero. Fix an interior point and the largest ball about it contained in $K$. Choose a contact point $y_+$. Every supporting plane of $K$ there also supports the ball, so it is the unique tangent plane. Choose $y_-$ on the opposite parallel supporting plane. If a point of the open chord lay on the boundary, a supporting plane there would contain both endpoints. This contradicts uniqueness at $y_+$, since the supporting plane at $y_+$ misses $y_-$. Choose invertible affine coordinates in which the two planes are $z=\pm1$ and the chord is $u=0$. For any $0<h<1$, the compact subsegment $|z|\le h$ has positive distance from the boundary of $K$. A cylinder of sufficiently small positive radius around this subsegment therefore lies in $\operatorname{int}K$.

In these coordinates set $M=\int_K u\,dx$. Fix a small inner cylinder $A_0=\{|u|\le r_0,\ |z|\le l_0\}$ and write $\int_{A_0}uu^\top dx=\kappa_0 I$. Take

$$
g(u,z)=1+\frac{\mathbf1_{A_0}}{\kappa_0}
                           \big(r_0|M|-M\cdot u\big).
$$

This is bounded, $g\ge1$, and $\int_K ug\,dx=M-\kappa_0^{-1}(\int_{A_0}uu^\top dx)M=0$ by $\int_{A_0}u\,dx=0$. Fix this weight before choosing the longer localization cylinder.

As in Section 2, each piece of $\mu$-mass $1/n$ has volume at least $v_0>0$, hence $\int_C g\,dx\ge v_0$. Choose $t<1$ sufficiently close to one that each cap $\{\pm z>t\}\cap K$ has $g\,dx$-mass less than $v_0/2$. The absolute height of every weighted centroid is at most $(1+t)/2$. Define the $J_i$ using the height quantiles for $K,\mu$. Choose $h<1$ above this centroid bound and the absolute heights of all interior quantiles. The chord gives an inner cylinder $A=\{|u|\le a\}\times[-h,h]$. In (2) use the whole-piece term $\delta\int_C ug\,dx$ and ordinary volume on the cylinder. Then $\sum_i W_\delta(C_i)=0$.

Inequality (3) depends only on the cylinder. Averaging it over a limit piece with $g\,dx$ gives $p\cdot\bar u_g\ge a|p|>0$, with $p=0$ again excluded by the centroid bound. Thus $\int_{C_k}p\cdot u\,g\,dx>0$ and $\int_{C_k\cap A}p\cdot u\,dx\ge0$ for large $k$. The contradiction from Section 2 rules out zero-volume limit intersections. Section 1 then gives horizontal slabs throughout $K$.

The interface argument above uses connectedness of intersections of $K$ with open half-spaces and open interface patches in the inner cylinder. Construct the same disjoint compact families of single pieces and put

$$
P_i=a_i+\frac{\delta}{\kappa}
             \int_{K\cap\{z\le b_i+a_i\cdot u\}}u g\,dx,\qquad
 P_0=P_n=0,\qquad \kappa=\int_{|u|\le a} u_1^2\,du.
$$

Taking differences of consecutive prefixes again gives (4). Each $P_i$ is continuous and determined by one plane. The local perturbation uses just (4), while localization puts all base solutions in its chart neighborhood. The same $E_\sigma$, the gap on the compact complement, and continuous extension prove the result for $K$. The affine coordinate change induces a homeomorphism on the Hausdorff space of compact convex sets, so pulling back gives the functionals in the original coordinates.

## 4. Four moments on the uniform cube

First let $d=3$ and take $K=[-1,1]^2\times[-1,1]$. Put $m=2/n$, $t_i=-1+im$, and $c_i=t_i-m/2$. On an equal-volume piece $\langle g\rangle_C=(n/8)\int_C g$ is its ordinary average. Let $u=(x_1,x_2)$ and $W=\langle u\rangle_C$. Section 1 applied to the entire cube shows that the only partition with $W=0$ on every piece is the stack of equal-thickness horizontal slabs. The separation argument of Section 3 gives a neighborhood in which all cuts are $z=t_i+a_i\cdot u$. The prescribed prefix volumes determine the intercepts $t_i$. Put $a_0=a_n=0$.

Write $p_i=a_i/(3m)$, $w=p_i-p_{i-1}$, and $V=(\langle(1+x_1)z\rangle_C,\langle x_2z\rangle_C)$. On the $i$-th layer,

$$
W=w,\quad \langle uz\rangle_C=m p_{i-1}+t_iw,\quad
 \langle z\rangle_C=c_i+3m\big(p_{i-1}\cdot w+|w|^2/2\big). \tag{5}
$$

Indeed the thickness is $m+(a_i-a_{i-1})\cdot u$, and the integral of $z$ along the fiber is half the difference of the squares of its upper and lower heights. The uniform base measure has second moment matrix $I/3$ and zero first and third moments. Substitution gives (5).

Near the horizontal stack, $V_1$ lies close to $c_i$. Choose continuous cutoffs $\chi_i(V_1)$ with disjoint supports, for example equal to one within $m/8$ of $c_i$ and zero at distance at least $m/4$, and shrink the neighborhood. The second piece's parameters $W,V$ determine its lower bounding slope parameter $p_1=B_*$ by

$$
(B_*)_2=(V_2-t_2W_2)/m,\qquad
 (B_*)_1=
 \frac{V_1-t_2W_1-c_2-3m (B_*)_2W_2-(3m/2)|W|^2}
      {\max\{m/2,\,m(1+3W_1)\}} .
$$

This solves (5), since the denominator equals $m(1+3W_1)$ throughout the chosen neighborhood. The upper parameter is $p_2=B_*+W$. On all four-dimensional inputs define

$$
\Psi_\sigma(W,V)=f(W)+\sigma^2\left[
   \sum_{i\ne2}\chi_i(V_1)\Delta_i(W/\sigma)
   +\chi_2(V_1)D_*(B_*/\sigma,-(B_*+W)/\sigma)\right].
$$

This is continuous and differs uniformly from $f(W)$ by $O(\sigma^2)$. Inside the neighborhood, division by $\sigma^2$ gives the incompatible planar tests. On the compact complement the base test $f(W)$ has strictly positive minimum diameter, so sufficiently small $\sigma$ works there as well. The resulting strict gap permits uniform approximation of the real and imaginary parts on the moment box $[-1,1]^2\times[-2,2]\times[-1,1]$ by rational polynomials $P_n,Q_n$. The moment formulas define them as functionals on all compact convex pieces.

## 5. The same polynomials in every dimension

For $d>3$, write $K=D_3\times E$, with active coordinates $(x_1,x_2,z)$ in $D_3=[-1,1]^3$ and the remaining coordinates $r$ in $E=[-1,1]^{d-3}$. If the additional first moments agree across the pieces, they vanish, since their sums are zero. Each piece thus has $r$-centroid zero.

Let $B_i(r)=\{x:(x,r)\in C_i\}$ and $A_i(r)=|B_i(r)|_3$, extended by zero outside the projection. For uniform probability $\nu$ on $E$, $M=\int A_i\,d\nu=8/n$. Brunn–Minkowski gives concavity of $A_i^{1/3}$ on its convex projection. The probability $A_i\,d\nu/M$ has centroid zero in the projection interior. Jensen's inequality gives

$$
A_i(0)^{1/3}\ge M^{-1}\int A_i^{4/3}\,d\nu\ge M^{1/3}.
$$

Over an interior projection point, a point interior to the section lies in the interior of $C_i$. Otherwise a supporting plane there has zero $x$-normal because of the section interior, and the remaining $r$-normal contradicts interiority of the projection point. Thus $\sum_i A_i(0)\le8=nM$, so equality holds throughout. Strict convexity of the power $4/3$ gives $A_i=M$ almost everywhere on $E$. Closedness of the projection and continuity of a concave function in its interior then give $A_i(r)=M$ for every $r\in\operatorname{int}E$.

Fix such an $r$. Convexity gives $(B_i(r)+B_i(-r))/2\subset B_i(0)$. The two end sections and the central section all have volume $M>0$, forcing equality in Brunn–Minkowski. Its equality case identifies the two end sections as translates, and their Minkowski average equals $B_i(0)$ since strict inclusion of full-dimensional convex bodies strictly increases volume. Thus $B_i(\pm r)=B_i(0)\pm v_i$ for some $v_i$. At $r,-r,0$ the sections partition $D_3$. Subtracting twice the central second moment from the sum at the two ends gives

$$
0=\sum_i\left(\int_{B_i(r)}|x|^2dx+\int_{B_i(-r)}|x|^2dx
                 -2\int_{B_i(0)}|x|^2dx\right)
   =2M\sum_i |v_i|^2 .
$$

It follows that every $v_i=0$, so all interior sections are identical. Closedness extends the product to the boundary of $E$, and convexity allows every boundary point of a piece to be approached along a segment from an interior point. Hence $C_i=B_i(0)\times E$. On these pieces $(n/2^d)|E|=n/8$, so the four active moments are exactly the three-dimensional ones. The same $P_n,Q_n$ from Section 4 therefore obstruct fairness in every dimension.

## 6. Related work and verification

The construction grew from a short proof for six pieces in the three-dimensional cube. That proof reserved the second piece for correction and used the first one to determine the common value. The binomial condition and the higher-dimensional product argument extend this idea. The planar path has rational vertices, and the local correction uses data from a single piece. [Planar construction](planar-construction.md)

Theorem B of Arseniy Akopyan's *Sixfold Tverberg counterexamples and convex equipartition obstructions* constructs a counterexample on the unit ball for $n=6$, $d\ge24$, with a uniform statement for sufficiently concentrated measures. At commit `d98f6f87`, the Lean theorem `convex_partition_counterexample_gt_17` gives an absolutely continuous probability measure and functionals in each $d\ge18$ for six pieces. The linked run records the build, statement comparison, and independent kernel check for that revision. [Manuscript](https://github.com/akopjan/toptverbert-nandakumar/blob/d98f6f87bb60b9e5b3a57370f393ade1397189bc/paper/manuscript.tex) · [Lean theorem](https://github.com/akopjan/toptverbert-nandakumar/blob/d98f6f87bb60b9e5b3a57370f393ade1397189bc/AkopyanResearch/Completion/DimensionEighteen.lean) · [Upstream build](https://github.com/akopjan/toptverbert-nandakumar/actions/runs/45870073497)

Akopyan's construction uses sixfold Tverberg maps and finitely many marked points. Here the two interfaces of a layer determine its correction after the measure has been prescribed. The companion script checks polygonal winding numbers, the sum over the ends, the cap bound, the layer moment identities, and the weight correction on an asymmetric pyramid. Lean proves the planar and geometric assertions, the Brunn–Minkowski equality argument, the volume-preserving coordinate change, and the dimension-uniform statement. The existence proof leaves the explicit polynomial coefficients and a numerical global gap undetermined. [Arithmetic checks](../../scripts/verify.py) · [Formal verification](../../formalization/docs/verification.md)
