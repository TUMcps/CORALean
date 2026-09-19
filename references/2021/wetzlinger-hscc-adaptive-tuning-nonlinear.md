# Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems

M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
Analysis of Nonlinear Systems". HSCC, 2021, Article 16.

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.5 (pp. 109–120), a verbatim reprint of the ACM version, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable, and the ACM version at https://doi.org/10.1145/3447928.3456643 is paywalled; the paper has no arXiv preprint).  
**Inventory:** confirmed

The nonlinear counterpart of the [CDC 2020 tuning paper](../2020/wetzlinger-cdc-adaptive-tuning.md):
the time step size chosen by scalar optimization of an estimated reachable-set size
over a finite horizon, and the Taylor abstraction order switched whenever the
abstraction error moves by more than a fixed threshold. Its `Thm. 3.2` is the
Hausdorff bound between a zonotope and its box over-approximation that
`reduceBoxOrder` needs, in the form the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)
later sharpened into three bounds — the same file now carries both papers'
citations. `Lemma 3.1` is the minimax inequality the paper's own proof of
`Thm. 3.2` leans on; the formalization of `Thm. 3.2` takes a more direct route
and does not call it, so `Lemma 3.1` is formalized on its own, standalone terms.
`Prop. 1` is the special case of the NAHS 2022 paper's `Thm. 2` at a constant `A`
and `Ψ`, which is how this paper — not yet having re-linearized within a step —
states it; the same file cites both papers.

Its numbering runs on two schemes at once: `Def. 1` and `Prop. 1` are numbered
sequentially, `Lemma 3.1` and `Thm. 3.2` by section. The rows use the numbers as
printed.

## Results

| Result | What it says | In CORALean |
|---|---|---|
| `Def. 1` | (Zonotopes) [cites [27, Def. 1]] Z := {x \| x = c + Σ_{i=1}^γ α_i g^(i), -1≤α_i≤1}, with order ρ := γ/n and shorthand ⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly |
| `Lemma 3.1` | For continuous f: C1×C2→I and g: C1→I on compact C1,C2⊂R^n and a compact interval I⊂R^n: if min_{y∈C2} f(x,y) ≤ g(x) for every x∈C1, then max_{x∈C1} min_{y∈C2} f(x,y) ≤ max_{x∈C1} g(x). | [`CORALean.minimax_le`](../../src/CORALean/Global/Minimax.lean) |
| `Thm. 3.2` | For a zonotope Z=⟨c,G⟩_Z and its box over-approximation Z_B := box(Z)=⟨c,G_B⟩_Z ⊇ Z, the Hausdorff distance d_H(Z,Z_B) = max_{x_B∈Z_B} min_{x∈Z} ‖x_B-x‖_2 is over-approximated by ω(Z) := 2‖Σ_{k=1}^γ ĝ^(k)‖_2, where ĝ^(k) is \|g^(k)\| with the entry at the (first) index i* attaining ‖g^(k)‖_∞ set to zero. | [`Zonotope.hausdorffDist₂_interval_le_max`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeMax.lean) |
| `Prop. 1` | Scaling Δt by ζ_δ∈(0,1) shrinks the i-th entry of the diameter of box(R_abs) by ζ_δ^{λ_i} with λ_i∈N as Δt→0: lim_{Δt→0} d_i(box(R_abs(ζ_δΔt)))/d_i(box(R_abs(Δt))) = ζ_δ^{λ_i}, where λ_i = j+1 for the first non-negative j with (A^j Ψ)_i ≠ {0}. | [`CORALean.gainDim_tendsto_pow_const`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimTendstoPowConst.lean) |
| `Alg. 1` | "Reachability analysis of nonlinear systems using state-space abstraction": per step, linearize at z*(t_s) = center(R(t_s)), compute R_lin by `linReach`, enlarge the estimated abstraction error Ψ̄ until Ψ ⊆ Ψ̄, add the resulting R_abs to both the time-point and time-interval solution, and reduce the set representation size. | — |
| `Alg. 2` | "Tuning of the time step size Δt": maintains the finite horizon Δ and the gain φ_1 across steps, computes R_abs(Δ) and its scalar counterpart r_abs,1, and returns the optimal time step size Δt* by Eq. (31) — initializing by shrinking Δ with ζ_δ until φ_1 ≥ ζ_Δ in the first step. | — |

## Findings

**`Lemma 3.1`.** The shared codomain is printed as "a compact interval `I⊂R^n`". A
compact interval of `R^n` would make `f` and `g` vector-valued, leaving `min`/`max`
without an order to run in. `Thm. 3.2`'s proof applies the lemma at `f(x_B,x) =
‖x_B-x‖_2`, a scalar, and `g` constant at `2‖ẑ‖_2`, another scalar — real-valued
throughout — so `I⊂R^n` is a misprint for a compact interval `I⊂R`. Formalized
that way; `I` itself never enters the statement, since boundedness follows from
continuity on a compact domain regardless of a named enclosing interval.

**Eq. (15), in `Thm. 3.2`.** The entries of ĝ^(k) are selected by `if k ≠ i*`, comparing
the *generator* index k with i*, which the same theorem defines as a *component* index —
"the (first) index for which g^(k)_{i*} = ‖g^(k)‖_∞". The condition meant is `i ≠ i*`: the
proof zeroes the largest component of each generator, writing v^(k)_i ∈ [-2\|g^(k)_i\|,
2\|g^(k)_i\|] "if i ≠ i*, 0 otherwise" and then "rewrit[ing] using (15)". The
[NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md) prints the same definition
correctly as `i ≠ i*` in its Eq. (18). The bound is right as intended.

**Eq. (18).** The bound `Thm. 3.2` names ω(Z) is used under the name ω_max(Z), which the
paper does not introduce. The NAHS 2022 paper is where ω_max earns its subscript, beside
ω_rad and ω_cut; here there is only one bound, so the two names are the same quantity.

**`Prop. 1`.** Formalized as the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s
`Thm. 2` at a constant `A` and `Ψ` — `R_abs(Δt)` read, as that paper's own `abstrSolInf` already
is, as the un-truncated series `[1, (8)]` would sum rather than this paper's truncated `(6)`. At
constant `A`, `Ψ` the specialization is proved outright, not inherited with a hypothesis: `Thm. 2`
assumes its expansion's leading term because passing a limit inside an infinite series needs
uniform control over the index that a moving `A(h)`, `Ψ(h)` does not supply; here every summand
is already independent of `Δt`, so the same expansion is elementary and is proved here rather
than assumed.

The paper's own proof of `Prop. 1` instead substitutes its `(6)` — `Rabs` truncated at a *fixed*
`η_abs` plus a remainder of order `O(Δt^{η_abs+1})` — and the printed formula for `λ_i` never
mentions `η_abs`. It is only the value obtained when the first `j` with `(A^jΨ)_i ≠ {0}` sits at
or below `η_abs`: should every term up to `η_abs` vanish in dimension `i` while some later `AʲΨ`
does not, the remainder (which is not shaped by `Aʲ`'s individual sparsity, only by `η_abs`) sets
the true leading order at `η_abs+1` rather than `j+1`. `η_abs` is itself chosen per step by a
separate, `Δt`-dependent criterion, `(11)`, so a proof that holds it fixed across the whole
`Δt→0` limit implicitly needs the truncation to already reach the order that decides the limit.
The claim proved here is about the un-truncated `Rabs`, where the difficulty does not arise.
