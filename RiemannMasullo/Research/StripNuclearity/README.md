# The projective kernel at a single strip width

The geometric identity on p. 520 assumes a reciprocal-weight projective kernel representing $AP$, where $A$ is convolution by the Bruhat test and $P$ projects orthogonally onto the spectral subspace. The theorem `exists_projectiveKernel_iff` identifies existence of this tensor with nuclearity of its represented ambient operator. The quotient action addresses the opposite order $PA$.

## Radial result

For a unitary Hecke character, half-width `α ≥ 0` and Sobolev exponent `s > 1`, `exists_projected_hecke_resolvent` proves trace class for `R.adjoint.comp P` on the radial weighted Hilbert space. Here `P` is the orthogonal complement projection of the joint kernel of precisely the admitted Mellin jets of the completed Hecke function in the closed strip centered at $1/2$. Interior zeros retain their full multiplicities. At a boundary point the derivative order `k` must also satisfy `2k + 1 < s`. The operator `R` has Mellin symbol $1/(c^2-z^2)$, with $c=α+s+3$.

The proof keeps all zeros with ordinate at most $2^n$ in absolute value. A bounded holomorphic multiplier vanishes to the required orders at the remaining zeros. After the resolvent the cutoff error in operator norm is $O(4^{-n})$. The rank of each cutoff is bounded by the number of surviving jets, including multiplicities. Jensen's weighted zero count from #6438 then gives summability of the singular values. The proof uses no lower bound on the distance between distinct Hecke zeros.

## Passage to convolution

On the full idèle classes, `exists_local_projectiveKernel` gives the desired tensor for every admissible compact output restriction $M_ρ AP$. In the radial logarithmic coordinate $x$, the reciprocal Hilbert weight is $v=e^{-2α|x|}(1+x^2)^{-s/2}$. The cutoff may cover a neighborhood of the origin together with the propagation radius of the compact convolution kernel. On either remaining half-line, $p=v'/v$ and $q=v''/v$ are bounded. Theorems `weight_log_derivatives` and `reciprocal_interval_weight_branches` give explicit bounds and identify these branches with the actual weight.

Write $H_κg=v(g*κ)$ for one smooth reciprocal-weight branch, with $g$ locally integrable and compactly supported, and $κ$ smooth and compactly supported. The theorem `weighted_convolution_resolvent_numerator` recovers (H_κg) by applying $R$ to the test

$$
(c^2-q)H_κg-2pH_{κ'}g-H_{κ''}g .
$$

The remaining steps are the bounded-operator identification of the weighted adjoint of the actual convolution with this radial formula and transport of the scalar projection to its idèle-class character component. For an infinite family of angular characters, one must also sum the component nuclear norms.

## Relation to the manuscript

On pp. 452–454 the rectangular expansions in Theorem 10.3.2.1 use arbitrary enumerations. Bounds for individual summands do not give trace-norm convergence after summing all discarded blocks. On pp. 463–464 the ambient off-diagonal component requires a bound beyond quotient nuclearity. The author lists this estimate as unfinished in footnote 8. Pages 470–474 switch to increasing ordinate height per character. With the indicated factors, (43) represents $PA$, while (45) identifies $AP$. The height-window argument here leaves the convergence of the printed rectangular expansions in #5224 open.
