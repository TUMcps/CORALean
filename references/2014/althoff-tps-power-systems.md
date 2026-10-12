# Formal and Compositional Analysis of Power Systems using Reachable Sets

M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets". IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.

**Source:** https://mediatum.ub.tum.de/doc/1281554/1281554.pdf (the author's manuscript in TUM's repository mediaTUM, node 1281554, on the journal template with volume, number and date left blank (`JOURNAL OF XX, VOL. X, NO. X, JANUARY XXXX`), 11 pages, read in full; text extracted with `pypdf`). The typeset article (doi:10.1109/TPWRS.2014.2306731, IEEE TPWRS 29(5):2270-2280, September 2014) was not reachable, so the numbers below are the manuscript's. CORA cites it as the reference of `@nonlinDASys/private/priv_linError_mixed_noInt_comp.m`, the compositional linearization error, and of the `nonlinDASys` power-system examples (`example_nonlinearDA_reach_04/05/06_powerSystem_*`, `powerSystem2cora`).  
**Inventory:** unconfirmed (against the typeset article: the manuscript prints Equations 1-19, Definition VI.1 and Algorithms 1-2, each with its own counter, and Tables I-II and Figures 1-6; the final numbering was not seen, and the manuscript's Fig. 5 and Table II placement shows it is not the layout of the article)

The compositional extension of [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) to power systems:
the same linearization of a semi-explicit index-1 DAE into a linear differential inclusion
(Eqs. 3-13, Alg. 1), and two ways to split a partitioned system, the reachable sets of the
subsystems with the interface inputs assumed (Eq. 14, Alg. 2) or only the Lagrange remainder
of the linearization error (Sec. V-B). The linearization is all restated from the earlier paper
and tracked there. The paper prints the algebraic error with the right sign, `-C F⁻¹`, in
Eqs. 7, 8, 10 and 13, where the TAC proof slips and CORA, in the compositional file too, adds. What is
new is the compositional part: the enlargement of the interface inputs (formalized with the
interface part it holds), the join of the subsystem sets (exact, a sum of mapped sets or the
product of the parts), and the loop of Alg. 2 up to what it certifies. Read as local
`C⁽ⁱ⁾F⁽ⁱ⁾⁻¹` blocks, the compositional linearization error misses the coupling of the
subsystems through `F`; see Findings.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Eq. 1` | The time-invariant, semi-explicit, index-1 DAE `ẋ = f(x(t), y(t), u(t))`, `0 = g(x(t), y(t), u(t))`, `[xᵀ(0), yᵀ(0)]ᵀ ∈ R(0)`, `u(t) ∈ U`, consistent when `g(x(0), y(0), u(0)) = 0`, with unique solutions `γ(t, x(0), y(0), u(·))` for piecewise continuous inputs, and the exact reachable set `Rᵉ([0, t_f])`. | n/a — restated; tracked as `Eq. 1` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Sec. II` | The exact reachable set cannot be computed for nonlinear DAEs (formal analysis of their dynamics is undecidable, after Platzer and Clarke), so algorithms compute `R([0, t_f]) ⊇ Rᵉ([0, t_f])`, with the projections `Rᵈ`, `Rᵃ` onto the differential and algebraic variables. | n/a — an undecidability result cited, not shown; the overapproximation is what the formalized algorithms prove | `not-a-claim` |
| `Sec. III` | One time step for the linear differential inclusion `˙x̃ ∈ Ãx̃(t) ⊕ Ũ` (Fig. 1): the affine solution `Rᵈ_a(t_{k+1}) = e^{Ãr}Rᵈ(t_k) ⊕ Γ(r)u_c`, the Taylor remainder `E_p(r) = [-W(r)r, W(r)r]`, `W(r) = e^{\|Ã\|r} - Σ_{i≤η} \|Ã\|ⁱrⁱ/i!`, the curvature set `Rᵈ_ε = F ⊗ Rᵈ(t_k) ⊕ F̃ ⊗ u_c` and the input set `Rᵈ_p(Ũ_Δ, r)`, after [23] and [36]. | n/a — restated; tracked as `Eq. 4` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 2` | `Rᵈ(t_{k+1}) = e^{Ãr}Rᵈ(t_k) ⊕ Γ(r)u_c ⊕ Rᵈ_p(Ũ_Δ, r)` and `Rᵈ(τ_k) = CH(Rᵈ(t_k), e^{Ãr}Rᵈ(t_k) ⊕ Γ(r)u_c) ⊕ Rᵈ_ε ⊕ Rᵈ_p(Ũ_Δ, r)`. | n/a — restated; tracked as `Eq. 4` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Sec. IV-A` | The linearization point: `z* = [x*; y*; u*]`, `x* = c_d + 0.5 r f(c_d, c_a, c_u)` (one Euler step of half the interval), `u* = c_u`, `y*` consistent with `0 = g(x*, y*, u*)` by Newton-Raphson; the centre of the reachable set stays the best point "although a refined technique is used" for the error. | n/a — restated; tracked as `Prop. 2` on [Althoff, Stursberg, Buss 2008](../2008/althoff-cdc-conservative-linearization.md), whose claim is for the earlier error bound; for the refined error it is asserted here without argument | `restated` |
| `Eq. 3` | The first-order Taylor expansion with Lagrange remainder, row by row: `ẋᵢ = fᵢ(z(t)) ∈ fᵢ(z*) + ∂fᵢ/∂z\|_{z*}(z(t) - z*) ⊕ {½(z(t) - z*)ᵀ ∂²fᵢ/∂z²\|_ξ (z(t) - z*) \| ξ, z(t) ∈ R^z}`, `Lᵈᵢ` its remainder, and the same for `gⱼ`, `Lᵃⱼ`. | n/a — restated; tracked as `Eq. 8` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 4` | The Jacobian blocks `∂f/∂z\|_{z*} = [A, C, B]`, `∂g/∂z\|_{z*} = [D, F, E]`. | n/a — notation | `not-a-claim` |
| `Eq. 5` | `ẋ ∈ f(z*) + AΔx + BΔu + CΔy ⊕ {½σ \| σᵢ = νᵀH^{d,(i)}(ξ)ν, ξ ∈ R^z, ν ∈ R^z_Δ}`. One Lagrange point `ξ` for all rows `i`, as in the earlier paper's Eq. 10. | n/a — restated; tracked as `Eq. 10` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md), where the shared `ξ` is refuted | `restated` |
| `Eq. 6` | `0 ∈ g(z*) + DΔx + EΔu + FΔy ⊕ {½φ \| φⱼ = νᵀH^{a,(j)}(ξ)ν, ξ ∈ R^z, ν ∈ R^z_Δ}`, one `ξ` for all rows `j`. | n/a — restated; tracked as `Eq. 11` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md), where the shared `ξ` is refuted | `restated` |
| `Eq. 7` | `F` invertible by the index-1 property: `Δy ∈ -F⁻¹(g(z*) + DΔx + EΔu) ⊕ {-½F⁻¹φ \| φⱼ = νᵀH^{a,(j)}(ξ)ν, ξ ∈ R^z, ν ∈ R^z_Δ}`. The algebraic deviation enters with a minus. | n/a — restated; tracked as `Eq. 12` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 8` | Inserting `Eq. 7` into `Eq. 5`: `ẋ ∈ f(z*) + AΔx + BΔu - CF⁻¹(g(z*) + DΔx + EΔu) ⊕ L = (w + ÃΔx + B̃Δu) ⊕ L`. | n/a — restated; tracked as `Eq. 13` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 9` | `w = f(z*) - CF⁻¹g(z*)`, `Ã = A - CF⁻¹D`, `B̃ = B - CF⁻¹E`. | n/a — restated; tracked as `Eq. 14` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 10` | `L = {½(σ - CF⁻¹φ) \| σᵢ = νᵀH^{d,(i)}(ξ)ν, φⱼ = νᵀH^{a,(j)}(ξ)ν, ξ ∈ R^z, ν ∈ R^z_Δ}`: the linearization error subtracts `CF⁻¹` times the algebraic one. | n/a — restated; tracked as `Eq. 15` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 11` | `˙x̃ ∈ Ãx̃(t) ⊕ Ũ`, `x̃ = Δx`, `Ũ = w ⊕ B̃(U ⊕ (-u*)) ⊕ L`. | n/a — restated; tracked as `Eq. 16` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 12` | The guess for the unknown `L`: the latest error `L̃` enlarged by `λ_L` about its centre, `L̄ = ĉ_L ⊕ λ_L(L̃ ⊕ (-ĉ_L))`, to be enlarged further if `L̄ ⊉ L`; the check `L ⊆ L_max`, otherwise split or reduce `r`. | n/a — a heuristic for the assumed error and a stopping rule, `Alg. 1` lines 2 and 7-8 | `not-a-claim` |
| `Eq. 13` | `R(τ_k) = [x*; y* - F⁻¹g(z*)] ⊕ [I; -F⁻¹D](Rᵈ(τ_k) - x*) ⊕ [0; -F⁻¹E](U - u*) ⊕ [0; -F⁻¹]Lᵃ`: the joint set of the differential and algebraic variables from the differential ones alone. | n/a — restated; tracked as `Prop. 2` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Sec. IV-B (complexity)` | With zonotopes, all operations of the reachability analysis but the linearization error have complexity `O(n³)`, the error `O(n⁵)`, in the number `n` of dynamic and algebraic variables. | n/a — a running time of a construction, which the tree can only assert (`Cost/`), never prove; see CONTRIBUTING.md | `not-a-claim` |
| `Alg. 1` | `reachNext(Rᵈ(t_k), L, U, Ã, B̃, w, r, L_max, λ_L)`: repeat the guess `L̄` (Eq. 12), `Ũ` (Eq. 11), `Rᵈ(τ_k)` (Eq. 2), `R(τ_k)` (Eq. 13) and `L` (Eq. 10, "according to [31]") until `L ⊆ L̄` or `L ⊈ L_max`; split if `L ⊈ L_max`, else `Rᵈ(t_{k+1})` by Eq. 2 from the computed `L`. | n/a — restated; tracked as `Alg. 1` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md), the inner loop of that algorithm; the error here is computed by [31], there by that paper's Cor. 1 | `restated` |
| `Sec. V` | The partition of the power system into subsystems is given (coherency or graph based), transmission lines are the interfaces, and the bus voltage and phase of a neighbour are an input of the subsystem. | n/a — an assumption on the partition | `not-a-claim` |
| `Eq. 14` | The interface inputs of subsystem `i` enlarged by `λ_U` about their centre, "analogously to (12)": `Û⁽ⁱ⁾ = ĉ_U⁽ⁱ⁾ ⊕ ((λ_U - 1)Λ⁽ⁱ⁾ + I)(U⁽ⁱ⁾ ⊕ (-ĉ_U⁽ⁱ⁾))`, `Λ` a diagonal matrix with ones at the interface inputs. | [`EnlargeInterfaceInput.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Operations/EnlargeInterfaceInput.lean), [`EnlargeInterfaceInputSubset.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/EnlargeInterfaceInputSubset.lean) — for `λ_U ≥ 1`, `Λ Λ = Λ` and `ĉ` the centre of `U`, `Λ U ⊆ Λ Û` (`NonlinDASys.image_subset_enlargeInterfaceInput`); that is all `Alg. 2` uses | `underspecified` — `λ_U ≥ 1`, `Λ` idempotent (a 0/1 diagonal) and `ĉ` the centre of `U` are not stated; `U ⊆ Û` is not implied, since only the interface coordinates are scaled, which decorrelates them from the others |
| `Eq. 15` | The complete reachable set from the subsystems', `R(τ_k) = Φ⁽¹⁾R⁽¹⁾(τ_k) × Φ⁽²⁾R⁽²⁾(τ_k) × … × Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾(τ_k)`, with `Φ⁽ⁱ⁾` mapping the local states to those of the full system, ones where states correspond. | [`ComposeSubsystems.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Operations/ComposeSubsystems.lean), [`ComposeSubsystemsExact.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/ComposeSubsystemsExact.lean), [`ComposeSubsystemsEqPreimage.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/ComposeSubsystemsEqPreimage.lean) — the zonotope `Φ⁽¹⁾R⁽¹⁾ ⊕ … ⊕ Φ⁽ⁿˢ⁾R⁽ⁿˢ⁾` is the sum of the mapped sets, equal, and for `Φ`, `Υ` a partition of the coordinates `{x \| ∀ i, Υ⁽ⁱ⁾x ∈ R⁽ⁱ⁾}`, equal | `underspecified` — each `Φ⁽ⁱ⁾R⁽ⁱ⁾` already lies in the states of the full system, so `×` would have dimension `n_s n`; read as the Minkowski sum, which for disjoint coordinates is the product in place |
| `Alg. 2` | `reachNextCompositional(R⁽ⁱ⁾ᵈ(t_k), λ_U, U⁽ⁱ⁾, otherInputsToReachNext)`: per subsystem with `inputEnclosure⁽ⁱ⁾ = false`, `Û⁽ⁱ⁾` by Eq. 14 and Alg. 1 on it; `R(τ_k)` by Eq. 15; `inputEnclosure⁽ⁱ⁾ := Υ⁽ⁱ⁾R(τ_k) ⊆ Λ⁽ⁱ⁾Û⁽ⁱ⁾`, `U⁽ⁱ⁾ := Λ⁽ⁱ⁾Û⁽ⁱ⁾ ⊕ (I - Λ⁽ⁱ⁾)U⁽ⁱ⁾`; until all are set; "the assumption is overapproximative and thus valid". | — partial: [`CompositionalState.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Definitions/CompositionalState.lean), [`ReachNextCompositional.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Operations/ReachNextCompositional.lean) (`NonlinDASys.reachNextCompositional`, lines 3-18; Alg. 1 an argument, `fuel` bounds the passes), [`ReachNextCompositionalSpec.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/ReachNextCompositionalSpec.lean) (the result passed the test of lines 10-15, `Υ⁽ⁱ⁾R(τ_k) ⊆ Λ⁽ⁱ⁾Û⁽ⁱ⁾`, and each subsystem's sets are Alg. 1 at its final `Û⁽ⁱ⁾`); missing: that a solution of the coupled system stays in `R(τ_k)` once the test passes, the paper's "thus valid" being an assume-guarantee argument it does not give, so the guarantee is not formalized | — |
| `Sec. V-B` | The linearization error computed compositionally: the Lagrange remainder of Eq. 10 is evaluated per subsystem, the neighbours' variables inputs from Eq. 14, and the partial remainders `L⁽ⁱ⁾` joined "as for the reachable set in (15)", `L(τ_k) = Φ⁽¹⁾L⁽¹⁾(τ_k) × … × Φ⁽ⁿˢ⁾L⁽ⁿˢ⁾(τ_k)`, while the reachable set is computed from the full model. | [`ComposeSubsystems.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Operations/ComposeSubsystems.lean), [`CompositionalLocalErrorCounterexample.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/CompositionalLocalErrorCounterexample.lean) — the join as `Eq. 15`; the counterexample `NonlinDASys.compositional_local_error_counterexample`: two coupled subsystems whose local error `ℓᵈ₁ - C₁F₁⁻¹ℓᵃ₁` of `ẋ₁` is `0` at every point while the true `ℓᵈ - CF⁻¹ℓᵃ` is `x₂²` | `underspecified` — `L⁽ⁱ⁾` is not defined: with the `C⁽ⁱ⁾F⁽ⁱ⁾⁻¹` of the subsystem's own rows and columns the product misses the error whenever `F` couples the subsystems, and the remainders `σ`, `φ` of the parts must be joined before the global `CF⁻¹` of `Eq. 10`; see Findings |
| `Sec. V-B (complexity)` | The compositional linearization error saves computation similar to the fully compositional one, the remainder costing `O(n⁵)` and every other operation `O(n³)`. | n/a — a running time of a construction, never proved in the tree; see CONTRIBUTING.md | `not-a-claim` |
| `Def. VI.1` | (Zonotope) `Z = {c + Σ βᵢg⁽ⁱ⁾ \| βᵢ ∈ [-1, 1]}`, written `(c, g⁽¹⁾, …, g⁽ᵖ⁾)`; order `p/n`. | n/a — restated; tracked as `Def. 1` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 16` | `Z₁ ⊕ Z₂ = (c + d, g⁽¹⁾, …, h⁽ᵖ²⁾)` and `M ⊗ Z₁ = (Mc, Mg⁽¹⁾, …, Mg⁽ᵖ¹⁾)`. | n/a — restated; tracked as `Sec. 2` on [Girard 2005](../2005/girard-hscc-reachability-zonotopes.md) | `restated` |
| `Eq. 17` | (After [46]) `CH(Z₁, e^{Ar}Z₁) ⊆ ½(c₁ + e^{Ar}c₁, g⁽¹⁾ + e^{Ar}g⁽¹⁾, …, c₁ - e^{Ar}c₁, g⁽¹⁾ - e^{Ar}g⁽¹⁾, …)`. | n/a — restated; tracked as `Eq. 6` on [Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) | `restated` |
| `Sec. VI (Cartesian product)` | `Z₁ × Z₂ = ([c; d], [G 0; 0 H])`. | n/a — the definition of the product of zonotopes, which `Zonotope.cartProd` is, exact by `Zonotope.cartProd_exact` | `not-a-claim` |
| `Sec. VI (interval matrix)` | The product of an interval matrix `M = M ⊕ [-S, S]` and a zonotope, overapproximated by `(Mc₁, Mg⁽¹⁾, …, h⁽¹⁾, …, h⁽ⁿ⁾)`, `h⁽ⁱ⁾ⱼ = Sⱼ(\|c\| + Σₖ\|g⁽ᵏ⁾\|)` for `i = j`, else `0`, after [23, Theorem 3.3]. | n/a — restated; tracked as `Thm. 3.3` on [Althoff 2010](../2010/althoff-thesis.md) | `restated` |
| `Sec. VI (quadratic map)` | The overapproximation `Z_Q ⊇ {φ \| φᵢ = xᵀQ⁽ⁱ⁾x, x ∈ Z₁}` with `σ = C(p+2, 2) - 1` generators, centre `dᵢ = cᵀQ⁽ⁱ⁾c + 0.5 Σₛ g⁽ˢ⁾ᵀQ⁽ⁱ⁾g⁽ˢ⁾`, after [48]; complexity `O(n⁵)`. | n/a — restated; tracked as `Lemma 1` on [Althoff, Krogh 2012](../2012/althoff-hscc-avoiding-intersection.md) | `restated` |
| `Eq. 18` | The generator model: `δ̇ᵢ = ωᵢ - ω_s`, `ω̇ᵢ = -(Dᵢ/Mᵢ)(ωᵢ - ω_s) + T_{m,i}/Mᵢ - P_{g,i}/Mᵢ`, `Ṫ_{m,i} = -(ωᵢ - ω_s)/(T_{SV,i}R_{D,i}) - T_{m,i}/T_{SV,i} + P_{c,i}/T_{SV,i}`, after [28], with the phase relative to the slack bus. | n/a — the paper's model (the same generator with power in place of torque is `Eq. 1` of [Althoff 2022](../2022/althoff-arch-power-systems.md)) | `not-a-claim` |
| `Sec. VII-A (generator power)` | The power of the generator buses `P_{g,i} = E_iV_i\|Y_{g,i}\|cos(Ψ_{g,i} + δ_i - Θ_i) - V_i²\|Y_{g,i}\|cos Ψ_{g,i}`, `Q_{g,i} = -E_iV_i\|Y_{g,i}\|sin(Ψ_{g,i} + δ_i - Θ_i) + V_i²\|Y_{g,i}\|sin Ψ_{g,i}`. | n/a — restated; tracked as `Eq. 2` on [Althoff 2022](../2022/althoff-arch-power-systems.md), whose rewritten form this is | `restated` |
| `Eq. 19` | The power-flow equations with injections `P_i = P_{g,i} + Pᵈ_{g,i} + P_{d,i} = Σⱼ V_iV_j\|Y_{ij}\|cos(Ψ_{ij} + Θ_j - Θ_i)` and `Q_i = -Σⱼ V_iV_j\|Y_{ij}\|sin(Ψ_{ij} + Θ_j - Θ_i)` (after [50]); a power drop-out sets `P_{g,i} = Q_{g,i} = 0` and replaces `E_i` by `V_i`. | n/a — restated; tracked as `Eq. 3` on [Althoff 2022](../2022/althoff-arch-power-systems.md); the injections `Pᵈ_{g,i}`, `Qᵈ_{g,i}` of renewable sources are added here | `restated` |
| `Sec. VII-A (variables)` | The assignment of dynamic, algebraic and input variables for a subsystem with `N_g` generator buses, `N_l` load buses and `N_i` cut lines: `y = (E_i, V_{N_g+i}, Θ_i)`, `x = (δ, ω, T_m)`, `u = (P_c, Pᵈ_g, Qᵈ_g, V̂_{k,j}, Θ̂_{k,j})` of the neighbours. | n/a — the numbering of variables | `not-a-claim` |
| `Table I` | Generator parameters `M = 1/(15π)`, `D = 0.04`, `\|Y_g\| = 5`, `Ψ_g = -π/2`, `T_SV = 1`, `R_D = 0.05`, `ω_s = 120π`. | n/a — data | `not-a-claim` |
| `Sec. VII-B` | Transient stability of the IEEE 14-bus and 30-bus systems: after 0.1 s the largest plant is taken off for 0.03 s; the subsystem split of Alg. 2 explodes after 0.27 s, the compositional linearization error does not and differs little from the full one; return times 4.0 s and 4.4 s (Table II); the 30-bus system with 18 dynamic variables needs `2¹⁸` simulations of about 1.5 s, 393216 s, "around 100 times longer" than the formal analysis. | n/a — an experiment; the arithmetic `2¹⁸ · 1.5 = 393216` holds | `not-a-claim` |
| `Sec. VII-C` | Critical clearing time `t_crit = 0.323 s` of the 14-bus scenario for the centre of the initial set; the reachable set computed until `t_crit` and unbounded afterwards, the sensitivity of the algebraic to the dynamic state making the error computation diverge. | n/a — an experiment | `not-a-claim` |
| `Sec. VII-D` | Uncertain renewable production at buses 13 and 14, `Pᵈ_g(t) ∈ {(t/5)P* \| P* ∈ [0.04, 0.06] p.u.}`, the 14-bus reachable sets for `[0, 5]` s against random simulations. | n/a — an experiment | `not-a-claim` |

## Findings

**The sign of the algebraic error — right in the paper, wrong in CORA.** Eq. 7 prints
`Δy ∈ -F⁻¹(g(z*) + DΔx + EΔu) ⊕ {-½F⁻¹φ | …}`, Eq. 8 inserts it as
`-CF⁻¹{g(z*) + DΔx + EΔu} ⊕ L`, Eq. 10 defines `L = {½(σ - CF⁻¹φ) | …}` and Eq. 13 carries
`[0; -F⁻¹]Lᵃ`. All four subtract `CF⁻¹` times the algebraic remainder, which is what the linearized
DAE gives ([`AlgDeviationEq.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/AlgDeviationEq.lean),
[`MemLinInclusion.lean`](../../src/CORALean/ContDynamics/NonlinDASys/Theorems/MemLinInclusion.lean)).
No equation of this paper has the `+ CF⁻¹` that the proof of Cor. 1 of
[Althoff, Krogh 2014](althoff-tac-nonlinear-dae.md) ends in. CORA's
`priv_linError_mixed_noInt_comp.m` takes the other sign, `error_mid = Z_err_x_mid +
Z_err_x_add_mid` with `Z_err_x_add_mid = [CFsub_inv*error_y_mid.c, CFsub_inv*error_y_mid.G]` and
`error_rad = error_x_rad_zono + CFsub_inv*error_y_rad_zono`, the sign bug of the other four
`nonlinDASys` linearization errors (FINDINGS.md, "`NonlinDASys` linearization error, sign of
`C F⁻¹`"), while the same file's algebraic set `R_y_cor = -F_inv*(f0_con + D*R)` has the
minus. Read from the source, not run; the file is the compositional version of the formalized
`NonlinDASys.linErrorCora`, to which it reduces for one subsystem.

**Eqs. 5, 6 — one Lagrange point for all rows.** The remainder sets of Eqs. 5, 6 and 10 take one
`ξ` for every row, which Eq. 3's mean value theorem, one `ξ` per row, does not give; this is the
error of Eqs. 10, 11 and 20 of the earlier paper, refuted there
(`NonlinDASys.shared_lagrange_point_counterexample`), and is repaired alike: every later step
holds with one `ξ` per row. The rows are tracked there.

**`Eq. 15`, `Sec. V-B` — the join and the local `CF⁻¹`.** The join `Φ⁽¹⁾R⁽¹⁾ × …` of Eq. 15
is dimensionally a sum: each `Φ⁽ⁱ⁾R⁽ⁱ⁾` is a set of the full system's states, and the
product of `n_s` of them has dimension `n_s n`. Read as the Minkowski sum, it is exactly the set
whose part in every subsystem is that subsystem's, the Cartesian product in place
(`NonlinDASys.composeSubsystems_eq_preimage`, for `Φ`, `Υ` a partition of the coordinates).
Sec. V-B joins "the partial Lagrange remainders `L⁽ⁱ⁾`" the same way, but the error of the
dynamics is `ℓᵈ - CF⁻¹ℓᵃ` with the `F⁻¹` of the full system (Eq. 10), and the interface
variables that make a subsystem's `F⁽ⁱ⁾` a diagonal block of `F` are, in the full system,
algebraic variables the rows of `g` couple through. Then `(CF⁻¹)` has blocks off the
diagonal and the subsystem's own `C⁽ⁱ⁾F⁽ⁱ⁾⁻¹` is not its block of it: for `f = y`,
`g = (y₁ - y₂, y₂ - x₂²)` with subsystems `(x₁, y₁)` and `(x₂, y₂)`, the true error of `ẋ₁`
at `x₂ = 1` is `1`, and the error subsystem 1 computes from its own rows (`C₁ = F₁ = 1`, linear
rows, remainders `0`) is `0` at every point, so no set that encloses the local errors holds the
true one (`NonlinDASys.compositional_local_error_counterexample`). The paper's text does not say
which `CF⁻¹` the parts carry, so the row is `underspecified`, not false: joining the
remainders `σ` and `φ` of the parts first, and applying the global `CF⁻¹` to the joined sets,
is sound. CORA's `priv_linError_mixed_noInt_comp.m` takes the local blocks:
`[~,~,Csub,~,~,Fsub] = options.subsystemJacobian{iSys}(…)`, `CFsub_inv = Csub*pinv(Fsub)`, and
adds `index{iSys}.X'*error{iSys}` per subsystem, which is the unsound reading whenever the
power-flow rows of a bus couple to a bus of another subsystem (a cut line); its own
`Rtotal_y` is updated with the global `F_inv`. Not run; the first witness is for the formula,
and `NonlinDASys.compLocalErrorCora_counterexample` is for CORA's per-subsystem code on the same
system (the error set of subsystem 1 is `{0}` for every `Csub`, `Fsub`).

**`Alg. 2` — the validation of the assumed inputs.** The test `Υ⁽ⁱ⁾R(τ_k) ⊆ Λ⁽ⁱ⁾Û⁽ⁱ⁾` of
the loop confirms that the computed sets stay in the assumed interface inputs; "thus valid" is
the paper's whole argument that a solution of the coupled system then stays in them. The solution
leaves a closed assumption at a first exit time, before which the computed set holds it and
after which it is not covered, so the step needs an argument that the paper does not give. What the loop certifies,
that the returned sets passed the test and are Alg. 1 at the final `Û⁽ⁱ⁾`, is proved
(`NonlinDASys.reachNextCompositional_spec`); the guarantee is the open part of the row. The
`repeat` has no bound on its passes, as in Alg. 1 of the earlier paper.

**`Table I`.** `R_D = 0.05` is printed in the column of `R_{D,i}`, while the text calls the
governor gain `1/R_{D,i}`; the benchmark paper [Althoff 2022](../2022/althoff-arch-power-systems.md)
prints `R_D = 6π` for the same generator, where `1/R_D ≈ 0.053`. The table's `0.05` is
most likely the gain `1/R_D`, or a different `R_D`; the paper does not say, and the model of
Eq. 18 is not formalized.

**Preprint.** The page is for the author's manuscript, headed with the journal template's
placeholders; the numbering of the typeset article was not seen.
