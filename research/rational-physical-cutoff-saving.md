# An unconditional bound for the ordered physical cutoff trace

Use the rational principal angular character, $a=\beta=1/2$, $s=3$, $W$, $P$, and the genuine $A_R$ of the linked nuclear estimate. Put $S(R)=R^{3/5}/(\log R)^{1/5}$ for large $R$. Fix $H\in C^\infty_c(\mathbb R)$. There are $c,C>0$ such that, **uniformly in every admissible project cutoff $m$ of arbitrary module radius and transition width**, one has
$$
 \|P M_m A_R\|_1\le C e^{R/2-cS(R)},\qquad
 |\operatorname{Tr}(M_m A_R P)|\le C e^{R/2-cS(R)}. \tag{1}
$$
The nuclear inequality and the scalar trace bound also hold for the sharp indicator of any bounded log interval, uniformly in both endpoints. For complements the same conclusions follow by subtraction from the full result, using the established nuclearity of $A_RP$ for the scalar trace when the translated test is supported away from norm one. Smoothness of the actual cutoff and bounds on its derivatives are unnecessary. The exponent $c>0$ here is fixed. It comes from balancing an exponentially fine mollification against a short-support trace estimate.

This is a written bound for the physical order $M_m A_R P$ at the stage with the full genuine spectral projector. It holds on both the inside and the outside of the physical cutoff. For example, if $\alpha_R=1/2-cS(R)/(2R)$, the absolute ordered trace normalized by $e^{\alpha_R R}$ tends to zero uniformly in these cutoffs as $R\to\infty$. The same is true for the difference between the wide localized trace and the full signed local distribution on polar-free profiles. The estimate still leaves the fixed half-width comparison and the behavior of freely varying finite theta bandwidths. [Whole projected convolution](https://github.com/mlyle/riemann-masullo/blob/4ffa1ed247556cd22edba631662ca6bc57d34dee/research/rational-nuclear-theta-convolution.md) · [Actual cutoff axioms, Definition 9.3.3.1](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch09_HardySobolev/Sec3.lean#L2905) · [Physical order and full-projector nuclearity](https://github.com/sergmister/riemann-masullo/blob/394da1b3caac72bb160db3ee4007b320426a7556/RiemannMasullo/Research/TraceComparison/PhysicalThetaBands.lean#L212)

## Fourier modulation before the genuine projection

Let $M_\xi$ multiply by $e^{i\xi x}$, and write $U_R(\xi)=P M_\xi A_R$. For every $B>0$ there are $J\ge1$ and $C_{H,B}$ with
$$
 \|U_R(\xi)\|_1\le C_{H,B}(1+|\xi|)^J e^{R/2-BS(R)}. \tag{2}
$$
For $0<\gamma<1$ and $|\xi|\le1$, one also has
$$
 \|U_R(\xi)-U_R(0)\|_1
 \le C_{H,B,\gamma}(1+R)^\gamma|\xi|^\gamma e^{R/2-BS(R)}. \tag{3}
$$
Indeed
$M_\xi A_R=e^{iR\xi} A_{(e^{i\xi\cdot}H)_R}M_\xi$ by the convolution kernel. In the rank-one integral of the previous note one can therefore use exactly the same contour, denominator $D$, and uniformly bounded vectors $v_w$, with the factor
$$
 e^{iR\xi}\,\mathcal LH(w+i\xi)\,E_{w+i\xi}
$$
in place of $\mathcal LH(w)E_w$. For each integer $j$ rapid decay gives $|\mathcal LH(w+i\xi)|\le C_{H,j}(1+|\xi|)^j(1+|\operatorname{Im}w|)^{-j}$. The proof of the nuclear bound uses a single finite $j$ for each chosen $B$, proving (2). Uniformly up to both strip edges,
$$
 \|E_{w+i\xi}-E_w\|
 \ll_\gamma |\xi|^\gamma
       \left(\int_\mathbb R |x|^{2\gamma}(1+x^2)^{-3/2}\,dx\right)^{1/2}.
$$
This follows directly from $|e^{i\xi x}-1|\le2|\xi x|^\gamma$ and Cauchy–Schwarz. The integral is finite for $\gamma<1$. The analogous difference of $\mathcal LH(w+i\xi)$ has rapid vertical decay times $O_H(|\xi|)$ by differentiating the compact profile's transform. Finally $|e^{iR\xi}-1|\le2R^\gamma|\xi|^\gamma$. Integrating the differences gives (3). The same formulas give norm continuity on compact frequency intervals. The global modulation is applied to the convolution before projecting throughout.

Fix an even nonnegative $\psi\in C^\infty_c([-1,1])$ of mass one and $\psi_\delta(x)=\delta^{-1}\psi(x/\delta)$. For $I=[a,b]$, set $m_\delta=\mathbf1_I*\psi_\delta$, $0<\delta\le1$. Its ordinary Fourier transform is
$$
 \widehat m_\delta(\xi)=
 \frac{e^{-ia\xi}-e^{-ib\xi}}{i\xi}\widehat\psi(\delta\xi).
$$
Fourier inversion with the $d\xi/(2\pi)$ convention gives $P M_{m_\delta}A_R$ as the nuclear integral of $\widehat m_\delta(\xi)U_R(\xi)$. On $|\xi|\ge1$ equation (2) bounds the weighted integral by $C\delta^{-J}e^{R/2-BS(R)}$, since $\widehat\psi$ is rapidly decreasing. On $|\xi|\le1$ split off $U_R(0)$. The rest is integrable by (3) with cost $C(1+R)^\gamma e^{R/2-BS(R)}$, independently of the endpoints. For the constant term the scalar integral is uniformly bounded in $a,b$. The symmetric integral reduces to two sine integrals $\int_0^1\sin(a\xi)d\xi/\xi$ and $\int_0^1\sin(b\xi)d\xi/\xi$, uniformly bounded by a change of variable and integration by parts beyond one. Replacing $1$ by $\widehat\psi(\delta\xi)$ changes the integrals by $O(1)$ since $\widehat\psi(0)=1$ and its derivative is bounded. Thus
$$
 \|P M_{m_\delta} A_R\|_1
 \ll_{H,B,\gamma}\big((1+R)^\gamma+\delta^{-J}\big)e^{R/2-BS(R)}
 \tag{4}
$$
uniformly in the locations and separation of the endpoints.

## A short mask in physical coordinates

Let $b$ be a measurable radial multiplier of modulus at most one supported on a union of at most four intervals, each of length at most $d\le1$. Then
$$
 \|M_b A_R\|_1\ll_H e^{R/2}(1+R)^{3/2}\sqrt d . \tag{5}
$$
Here the projection is unnecessary. In Haar $L^2$ after multiplication by $\sqrt w$, principal radial convolution acts on the angular average with kernel $H(x-t-R)\sqrt{w(x)/w(t)}$ in the radial coordinate. The compact angular projection is rank one and the chosen Haar volume normalization gives no growing factor. Use unit input and output cells indexed by integers $l,k$. For every output cell meeting the support of $b$, only $O_H(1)$ input cells occur. In such a cell pair $|k-l-R|\le C_H$. On the unit square the scalar function $H(k-l-R+u-v)$ admits an absolutely summable separated Fourier expansion with coefficient sum bounded independently of $k,l,R$. One construction multiplies by fixed smooth cutoffs equal to one on $[0,1]^2$, then expands the result on a larger periodic square, integrating by parts twice in each variable. Keep the separated weight factors with each vector. The product of their $L^2$ norms is bounded by
$$
 C_H e^{R/2}(1+R)^{3/2}\,|\operatorname{supp} b\cap[k,k+1]|^{1/2}.
$$
Indeed $\sqrt{w(x)/w(t)}\ll_H e^{R/2}(1+R)^{3/2}$ throughout participating cells, by $|x-t|\le R+C_H$ and the elementary polynomial weight ratio. Finitely many cells meet each short interval, so summing the absolute rank-one norms proves (5). The same expansion proves nuclearity of $M_bA_R$ for each fixed bounded log support.

Choose $B=1$ in (4), fix its $J$, and put $\delta=e^{-\kappa S(R)}$ with $0<\kappa<1/(2J)$. The multiplier $\mathbf1_I-m_\delta$ has modulus at most one and is supported within $\delta$ of the two endpoints. By (4) and (5), absorbing the polynomial factors by reducing a positive constant $c$, we obtain
$$
 \sup_{I}\|P M_{\mathbf1_I} A_R\|_1\ll_H e^{R/2-cS(R)}
 \tag{6}
$$
over all bounded intervals. For each compact mask $M_m$, $M_m A_R P$ is nuclear by the cell argument. Relative to $P W\oplus(I-P)W$ its trace equals that of the upper-left block $P M_m A_R P$. Its absolute value is bounded by $\|P M_m A_R\|_1$. This proves the sharp interval claim.

## All module radii and transition widths of the project

Let $L=\log\Lambda>0$. At large $L$, the admissible module width satisfies $0<\varepsilon<\Lambda^{-1}$. The upper transition ends at $L$ and begins no later than $\log(\Lambda-\varepsilon)$. The positive log interval $[0,\log(\Lambda-\varepsilon)]$ is inside the plateau since $\Lambda^{-1}+\varepsilon<2/\Lambda<1$. Inversion symmetry supplies the opposite plateau as well. Therefore $m-\mathbf1_{[-L,L]}$ is supported in two intervals of length at most
$$
 -\log(1-\Lambda^{-2})=O(e^{-2L}).
$$
For $L\ge\kappa S(R)$ these widths are at most $C\delta$ for large $R$. Equation (5) and (6) give (1), covering arbitrary admissible transitions regardless of their oscillation or jumps.

For $0<L<\kappa S(R)$, the cutoff is bounded by one and supported in $|x|\le L$. On the participating input $t=x-R+O_H(1)$, $|x|-|t|\le2L-R+C_H$. The unit-cell proof of (5), now on $O(1+L)$ output cells of full length, gives
$$
 \|M_m A_R\|_1\ll_H(1+L)(1+R)^{3/2} e^{(2L-R)/2}.
$$
This is exponentially smaller than the right side of (1). These two ranges exhaust the cutoff radii; no bandwidth limit or nonuniform cutoff choice is being interchanged. This deduction controls an actual physical operator and its ordered signed trace, and makes no claim of positivity.
