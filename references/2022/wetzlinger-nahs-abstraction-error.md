# Adaptive Reachability Algorithms for Nonlinear Systems Using Abstraction Error Analysis

M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid
Systems, vol. 46, 2022, p. 101252.

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.6 (pp. 121–150), a verbatim reprint of the Elsevier version, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable, and the journal version at https://doi.org/10.1016/j.nahs.2022.101252 is paywalled; the paper has no arXiv preprint).  
**Inventory:** confirmed

What a time step size can and cannot buy for a nonlinear system. The gain function
measures how the local abstraction error shrinks when the step does, `Thm. 2` says
that ratio converges to δ^{q+1} for the gain order q, and for most nonlinear systems
q comes out 0 — the error shrinks only linearly in the step size, so the wrapping
effect cannot be tuned away, only paid for. Beside the main result it carries the zonotope-order-reduction bounds
the adaptive algorithms use: `Thm. 1`'s ω_max is the bound the
[HSCC 2021 paper](../2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md) proved as its
`Thm. 3.2`, joined here by ω_rad and ω_cut. `Lemma 1` and all three bounds are
proved, the first over any normed space and the other three at `‖·‖₂`, the norm
the paper states them in. `ReduceBoxOrder` and `ReduceBoxAntitone` are
where a chosen reduction order would be held against one of these bounds, and
the tree still cites the CDC 2020 paper there.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Zonotopes) [cites [26, Def. 1]] Z := {x \| x = c + Σ_{i=1}^γ α_i g^(i), -1≤α_i≤1}, with order ρ := γ/n and shorthand ⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Def. 2` | (Hausdorff Distance) For compact V,W⊂R^n, d_H(V,W) := max{d^(1)_H(V,W), d^(2)_H(V,W)} with d^(1)_H(V,W) := max_{v∈V} min_{w∈W} ‖v-w‖_2 and d^(2)_H symmetrically. | n/a — Mathlib's `Metric.hausdorffDist` provides it, used in [`HausdorffDistAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistAddLe.lean) and [`HausdorffDistIntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDistIntervalLe.lean). Mathlib's is the distance of whatever metric the ambient type carries, which at `Vec ℝ n` is the supremum norm and not this definition's ‖·‖_2; [`EuclideanHausdorffDist.lean`](../../src/CORALean/Global/EuclideanHausdorffDist.lean) takes it through `toEuclidean` instead, and that composite is this definition exactly |
| `Lemma 1` | For compact S,V,W⊂R^n: d_H(S⊕V, S⊕W) ≤ d_H(V,W) — which is what lets order reduction be analyzed on the reduced part Z alone, since d_H(Z_full,Z_red) = d_H(Z'⊕Z, Z'⊕box(Z)) ≤ d_H(Z,box(Z)). | [`HausdorffDistAddLe.lean`](../../src/CORALean/ContSet/ContSet/Theorems/HausdorffDistAddLe.lean) — over any normed space, and on the exact Minkowski sum; `V` and `W` carry the compactness and nonemptiness Mathlib's real-valued distance needs to be the distance and not its junk value |
| `Thm. 1` | For a zonotope Z=⟨c,G⟩_Z and Z_box := box(Z) ⊇ Z, the Hausdorff distance d_H(Z,Z_box) is over-approximated by three bounds: ω_max(Z) := 2‖Σ_p ĝ^(p)‖_2 (with ĝ^(p) zeroed at the (first) index i* attaining ‖g^(p)‖_∞), ω_rad(Z) := Σ_p ‖g^(p)‖_2, and ω_cut(Z) := √2 Σ_p ‖g^(p)‖_2 √(1 - Σ_i (g^(p)_i)^4/‖g^(p)‖_2^4). | ω_max in [`HausdorffDist2IntervalLeMax.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeMax.lean), ω_rad in [`HausdorffDist2IntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLe.lean) and ω_cut in [`HausdorffDist2IntervalLeCut.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeCut.lean) — each at `hausdorffDist₂`, `Def. 2`'s distance rather than the supremum-norm one `Vec ℝ n` carries; see the finding below |
| `Def. 3` | (Convergence Order of Classical ODE Solvers) The order of a solver for ẋ = f(x,t) is the q∈N_0 with local truncation error ε_{Δt,loc} := \|ξ_ex(Δt;t_0,x_0) - ξ̂(Δt;t_0,x_0)\| ≤ cΔt^{q+1} for all t_0,x_0, with c independent of t_0, x_0 and Δt. | — |
| `Def. 4` | (Errors of Set-based Solvers) For a set-based approximation R = R̂ ⊕ R_abs, the local abstraction error at t_k is ε_{k,loc} := ‖d(box(R_abs(Δt;t_k,R(t_k))))‖_∞, and the global accumulated abstraction error over N steps is ε_N := ‖d(box(R(t_end) ⊖ R̂(t_end)))‖_∞. | — |
| `Lemma 2` | (Local and Global Abstraction Error) For solvers of the form (10), ε_N ≤ (c/Δt)·max_{1≤ℓ≤N} ε_{ℓ,loc}, with a constant c that may depend on t_end but not on Δt or N. | — |
| `Def. 5` | (Gain Function) The gain over the time span h with relative increment δ∈[0,1] is φ(h;δ) = max_i φ_i(h;δ), where φ_i(h;δ) = d_i(box(R^∞_abs(δh)))/d_i(box(R^∞_abs(h))). | — |
| `Prop. 1` | (Diameter of Set of Abstraction Errors) If Ψ(h) is the zonotope ⟨c(h),G(h)⟩_Z, then d_i(box(R^∞_abs(h))) = 2 Σ_{p≥0} h^{p+1}/(p+1)! ·‖A^p(h)G(h)‖_{1,i}, the 1-norm of the i-th row. | — |
| `Lemma 3` | (Expansion of Coefficients) For smooth f, A(h) and G(h) are smooth and every coefficient is either ‖A^p(h)G(h)‖_{1,i} = h^{q^(p)_i}‖a^(p)_i + b^(p)_i(h)‖_1 with q^(p)_i∈N_0, a^(p)_i ≠ 0, b^(p)_i(h)=O(h), or identically 0 (convention: q^(p)_i = ∞, a^(p)_i = 0); and Q^(p)_i(h) = ‖a^(p)_i + b^(p)_i(h)‖_1 is non-negative and piecewise smooth. | — |
| `Thm. 2` | (Limit Gain) For smooth f, lim_{h→0} φ_i(h;δ) = δ^{q_i+1}, where q_i is the index j at which the coefficient sum Σ_{p+q^(p)_i = j} ‖a^(p)_i‖_1 first fails to vanish (Eq. (40); see the finding below). | — |
| `Def. 6` | (Gain Order of Set-based Solvers) q := min_i q_i is the gain order of the method and q_i that of the i-th dimension; the method has zero abstraction error iff q = ∞. | — |
| `Prop. 2` | (Derivative of Gain) If all Q^(p)_i are differentiable at 0, then lim_{h→0} dφ_i(h;δ)/dh ≤ 0 for δ∈[0,1]; and for fixed h, if every Q^(p)_i is constant on [0,h], then φ_i(t;δ) ≤ δ^{q_i+1} for all t∈[0,h]. | — |
| `Alg. 1` | "Reachability analysis of continuous-time nonlinear systems using abstractions in the state space": the on-the-fly abstraction loop (linearization point, Taylor expansion, `linReach`, abstraction-error fixed point, addition, order reduction), stated for nonlinear differential-algebraic systems and specializing to the other system classes. | — |
| `Alg. 2` | "Adaptively-tuned reachable set computation for one step k>1": updates the finite horizon h_k from the previous gain, runs the step twice — once to compute R_abs(h) and the optimal Δt*, once to compute the reachable set with it — and returns the next abstraction order κ_{k+1}, horizon h_k and gain φ^(1)_k. | — |

## Findings

**`Thm. 1` — the norm the three bounds are proved at is not the one `Vec ℝ n` carries.**
`Vec ℝ n` is `Fin n → ℝ`, and Mathlib's `Pi` instance gives it the *supremum* norm, so
`Metric.hausdorffDist` there is the sup-norm distance and not `Def. 2`. Rather than move the
type, `hausdorffDist₂` takes Mathlib's distance through `toEuclidean : Vec ℝ n ≃L[ℝ]
EuclideanSpace ℝ (Fin n)`, which is `Def. 2` verbatim and costs two translation lemmas; all three
bounds are proved at it. The sup-norm analogue of ω_rad stands separately as
`Zonotope.hausdorffDist_interval_le` — `∑ₚ ‖g⁽ᵖ⁾‖_∞` is not `∑ₚ ‖g⁽ᵖ⁾‖₂` and neither implies the
other, so both are kept. ω_cut is proved without the Bauer maximum principle the paper's appendix
uses to restrict the coefficients to the vertices of `[-1,1]^n`: the quantity it bounds is half a
double sum of squared coefficient differences, whose diagonal vanishes, and `(νᵢ-νⱼ)² ≤ 4` off the
diagonal then gives the same estimate over the whole box.
[`HausdorffDist2IntervalLe.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLe.lean),
[`HausdorffDist2IntervalLeMax.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeMax.lean),
[`HausdorffDist2IntervalLeCut.lean`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeCut.lean)

**Eq. (40), in `Thm. 2`.** The gain order is defined as q_i = max{ j∈N_0 \| Σ_{p+q^(p)_i = j}
‖a^(p)_i‖_1 ≠ 0 }, but the maximum is a minimum. The limit h→0 is decided by the
*lowest*-order term of d_i(box(R^∞_abs(h))) = 2 Σ_j h^{j+1} Σ_{p+q^(p)_i=j} ‖a^(p)_i +
b^(p)_i(h)‖_1/(p+1)!, and for a system with infinitely many non-vanishing coefficients the
printed maximum is ∞ — which by `Def. 6` would say the method has zero abstraction error.
The note printed directly under (40) describes when the sum *vanishes* ("either there does
not exist a tuple (p,q^(p)_i) such that p + q^(p)_i = j, or ... a^(p)_i = 0"), i.e. the
negation of the condition as printed, and the proof uses only that the coefficient at q_i
is non-zero. Reading (40) as a minimum makes the theorem, its proof, and `Def. 6`'s
"q = ∞ iff zero abstraction error" agree.
