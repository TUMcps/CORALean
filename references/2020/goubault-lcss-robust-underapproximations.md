# Robust Under-Approximations and Application to Reachability of Non-Linear Control Systems With Disturbances

E. Goubault and S. Putot. "Robust Under-Approximations and Application to Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems Letters, 4(4):928-933, 2020.

**Source:** http://www.lix.polytechnique.fr/Labo/Sylvie.Putot/Publications/csl2020.pdf (the authors' preprint on Putot's page, 6 pages, read in full; text extracted with `pypdf`, the over- and underlines of Theorems 1-2 read from the vector rules with `pdfminer`). Volume, issue and pages from the published record (doi:10.1109/LCSYS.2020.2997261); the typeset article was not reachable. CORA cites the paper in `nonlinearSys/reachInner.m` and `nonlinearSys/private/priv_reachInnerParallelotope.m`, the latter for `Theorem 3` (and `Theorem 2` in a comment).  
**Inventory:** confirmed (Theorems 1-3, Remark 1, Examples 1-4 and equations (1)-(6), each with its own counter; Sections II-IV; Table I)

Inner (and outer) approximations of the range of a function from a mean-value theorem: for a
real-valued `f` the inner interval is `f(c) ± ⟨∇̲, r⟩` with `∇̲` a lower bound of `|∂ᵢf|`
(`Thm. 1`), and against disturbances the *robust* range `{z | ∀w ∃u, z = f(w, u)}` is
bracketed the same way (`Thm. 2`). For vector-valued `f` the components' inner intervals
combine into a box inside the image when each input is existential in exactly one component
(`Thm. 3`, by Brouwer's fixed-point theorem), and with the flow as `f` this gives robust inner
approximations of reachable sets (Sec. III). CORA's `reachInner` with `'parallelo'` is
`Thm. 3` with preconditioning. Formalized: all of it. `Thm. 3` and `Remark 1` are proved for the
AE extensions "built from `Thm. 2`" by Brouwer's theorem (`exists_fixedPoint_of_isCompact_convex`)
on one parameter per component, with a selection read off `Thm. 2`'s hypotheses in place of
Goldsztejn's continuous selections (Findings).

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Thm. 1` | (Mean-value AE extensions) For f: ℝᵐ → ℝ C¹, x ∈ IRᵐ, f(c(x)) ∈ f₀ = [f̲₀, f̄₀] and \|∇ᵢf(c(x₁), …, c(xᵢ₋₁), xᵢ, …, x_m)\| ∈ ∇ᵢ = [∇̲ᵢ, ∇̄ᵢ] over x: range(f, x) ⊆ [f̲₀, f̄₀] + ⟨∇̄, r(x)⟩[-1, 1] (1) and [f̄₀ - ⟨∇̲, r(x)⟩, f̲₀ + ⟨∇̲, r(x)⟩] ⊆ range(f, x) (2). | [`MeanValueAE.lean`](../../src/CORALean/Global/MeanValueAE.lean), [`CoordinatePath.lean`](../../src/CORALean/Global/CoordinatePath.lean) — `f` differentiable, the box nonempty for (2) | `proof-gap` — the printed proof of (2) takes `f` monotone on the box and uses the corners `x̲`, `x̄`, which fails for `m ≥ 2` with partials of different signs (`f = x₁ - x₂`); each coordinate moved the way its own partial points closes it; see Findings |
| `Example 1` | f(x) = x² - x on [2, 3]: [2.25, 5.25] ⊆ range(f, [2, 3]) ⊆ [1.25, 6.25]. | n/a — an illustration | `not-a-claim` |
| `Sec. II-A.2` | (Robust range) range(f, x, I_A, I_E) = {z \| ∀w ∈ x_A, ∃u ∈ x_E, z = f(w, u)}. | [`RobustMeanValueAE.lean`](../../src/CORALean/Global/RobustMeanValueAE.lean) — `robustRange`, the inputs split as two vectors | `correct` |
| `Thm. 2` | (Robust mean-value AE extensions) For f(c(x)) ∈ f₀, \|∇_w f(w, c(x_E))\| ∈ ∇w over x_A and \|∇_u f(w, u)\| ∈ ∇u over x: range(f, x, I_A, I_E) ⊆ [f̲₀ - ⟨∇̄u, r(x_E)⟩ + ⟨∇̲w, r(x_A)⟩, f̄₀ + ⟨∇̄u, r(x_E)⟩ - ⟨∇̲w, r(x_A)⟩] (3) and [f̄₀ - ⟨∇̲u, r(x_E)⟩ + ⟨∇̄w, r(x_A)⟩, f̲₀ + ⟨∇̲u, r(x_E)⟩ - ⟨∇̄w, r(x_A)⟩] ⊆ range(f, x, I_A, I_E) (4). | [`RobustMeanValueAE.lean`](../../src/CORALean/Global/RobustMeanValueAE.lean) — `robustMeanValueAE_outer`, `robustMeanValueAE_inner`; `w ↦ f(w, c(x_E))` and each `u ↦ f(w, u)` differentiable | `underspecified` — (3) needs `x_A` and (4) `x_E` nonempty, while the paper's `IR` contains the empty interval (over no disturbance every `z` is robustly reached) |
| `Example 2` | f(x₁, x₂) = x₂² - 2x₁ on [2, 3]²: [-1.75, 4.25] ⊆ range ⊆ [-2.75, 5.25] and [0.25, 2.25] ⊆ range(f, x, 1, 2) ⊆ [-0.75, 3.25]. | n/a — an illustration | `not-a-claim` |
| `Thm. 3` | For f: ℝᵐ → ℝⁿ elementary and π: {1, …, m} → {1, …, n}, the AE extensions (5) ∀zᵢ ∈ zᵢ, (∀xⱼ)_{j ∈ J_A^{(zᵢ)}}, (∃xⱼ)_{j ∈ J_E^{(zᵢ)}}, zᵢ = fᵢ(x), J_E^{(zᵢ)} = π⁻¹(i), give z = z₁ × … × z_n ⊆ range(f, x) if nonempty. | [`UnderApproxRangeBox.lean`](../../src/CORALean/Global/UnderApproxRangeBox.lean) — `meanValueBox_subset_image`: the extensions (5) are `Thm. 2`'s inner intervals, so the hypotheses are `Thm. 2`'s for each component (`f₀ᵢ ∋ fᵢ(c(x))`, `\|∂ⱼfᵢ\| ≥ ∇̲ᵢⱼ` on `x` for `π j = i`, `\|∂ⱼfᵢ\| ≤ ∇̄ᵢⱼ` for the other `j` where the inputs of `π⁻¹(i)` are at the center); [`RobustUnderApproxBox.lean`](../../src/CORALean/Global/RobustUnderApproxBox.lean) — `exists_eq_of_mean_value_box`, Brouwer on `[0, 1]ⁿ` over [`CoordinateGain.lean`](../../src/CORALean/Global/CoordinateGain.lean) (and `abs_sub_le_sum_filter_of_abs_partial_le` of `CoordinatePathOff.lean` for the disturbance bound); not through Goldsztejn's selections | `underspecified` — "elementary" is not defined (here `C¹`, the standing assumption of `Thm. 1`), and the box must be nonempty: over an empty `x` with `∇̲ = 0` and a point `f₀` the printed `z` is nonempty and `range(f, x)` empty; see Findings |
| `Remark 1` | `Thm. 3` with π: {1, …, m} → ({1, …, n} \ I_A) under-approximates the robust range. | [`MeanValueBoxSubsetRobustRange.lean`](../../src/CORALean/Global/MeanValueBoxSubsetRobustRange.lean) — `meanValueBox_subset_robustRangeVec`, the robust range of a vector-valued `f` (`robustRangeVec`, in `RobustRangeVec.lean`); `π` read as defined on the non-disturbance inputs, the disturbances `I_A` universal in every component; the same proof as `Thm. 3`, [`RobustUnderApproxBox.lean`](../../src/CORALean/Global/RobustUnderApproxBox.lean) | `underspecified` — the codomain `{1, …, n} \ I_A` removes input indices from the output indices, and `π` is read as defined on `{1, …, m} \ I_A`; and `Thm. 3`'s `C¹` and nonempty box, see Findings |
| `Example 3` | f = (5x₁² + x₂² - 2x₁x₂ - 4, x₁² + 5x₂² - 2x₁x₂ - 4) on [0.9, 1.1]²: π = (1 → 2, 2 → 1) gives an empty box, π = id gives [-0.64, 0.64]². | n/a — an illustration | `not-a-claim` |
| `Sec. II-B` | (Preconditioning) For C nonsingular and z ⊆ range(Cf, x), the skewed box {C⁻¹z \| z ∈ z} ⊆ range(f, x). | [`PreconditionInner.lean`](../../src/CORALean/Global/PreconditionInner.lean) — for any set `z` | `correct` |
| `Example 4` | f = (2x₁² - x₁x₂ - 1, x₁² + x₂² - 2) on [0.9, 1.1]²: empty inner boxes, a nonempty preconditioned parallelotope (Fig. 1). | n/a — an illustration | `not-a-claim` |
| `Sec. III` | (Maximal, minimal and robust reachability) R_E = {z \| ∃u ∈ U, ∃z₀ ∈ Z₀, z = φ(t; z₀, u)}, R_A = {z \| ∀u ∈ U, ∃z₀ ∈ Z₀, …}, R_AE = {z \| ∀u_A ∈ U_A, ∃u_E ∈ U_E, ∃z₀ ∈ Z₀, z = φ(t; z₀, u)}. | [`RobustReachSetExact.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Definitions/RobustReachSetExact.lean) — `NonlinearSys.robustReachSetExact`, the solution map and the admissible signals as arguments; R_E and R_A as one-signal cases | `correct` |
| `Sec. IV` | RINO on the Dubbins vehicle, a 10D quadrotor and other benchmarks (Figs. 2-3, Table I). | n/a — experiments | `not-a-claim` |

## Findings

**`Thm. 1` (2) — the corners do not reach the inner bounds.** The printed proof argues that
`∇̲ ≠ 0` makes `f` "either strictly increasing or decreasing over `x`" and takes
`f(x̲) - f(c(x)) ≤ -⟨∇̲, r(x)⟩`. For `m ≥ 2` the partials can have different signs: `f(x) =
x₁ - x₂` on `[-1, 1]²` has `|∂ᵢf| = 1`, `∇̲ = (1, 1)`, and `f(x̲) = 0 > f(c) - ⟨∇̲, r⟩ = -2`.
The statement still holds: `∂ᵢf` keeps one sign along each coordinate line of its path set
(Darboux), so moving coordinate `i` towards the bound its own sign points to gains at least
`∇̲ᵢrᵢ`, and the intermediate value theorem on the connected box fills the interval
(`exists_ge_add_sum_of_abs_partial_ge`, `meanValueAE_inner`).

**`Thm. 3` and `Remark 1` — the selection comes from `Thm. 2`'s hypotheses.** The printed proof
takes, for each AE proposition (5), Goldsztejn's continuous selections `g_k(zᵢ, (xⱼ)_{j ∈ J_A})`
("since `f` is elementary", [3]) and a fixed point of the map they form. (5) is built from
`Thm. 2`, and then no general selection theorem is needed. Where `∇̲ⱼ > 0` for an input of
`π⁻¹(i)`, `\|∂ⱼfᵢ\| ≥ ∇̲ⱼ` on the connected box and continuity of `∂ⱼfᵢ` give it one sign, so
moving `xⱼ` from the center to the end its sign points to gains at least `∇̲ⱼ rⱼ` from wherever the
others are (`exists_coord_ends_gain`), the end not depending on them. Put the inputs of `π⁻¹(i)` on
the segment between the two opposite corners, parametrized by `τᵢ ∈ [0, 1]`: by `Thm. 2`'s own
estimate `fᵢ` is at least the upper end of the interval at `τᵢ = 1` and at most its lower end at
`τᵢ = 0`, for every `τ_{-i}` and every position of the inputs outside `π⁻¹(i)`, the disturbances
included. Then `τ ↦ clamp₀¹(τ + z - f(x(τ)))` is a continuous self-map of `[0, 1]ⁿ`, and a fixed
point cannot sit on a clamp (it would need `fᵢ < zᵢ` where `fᵢ ≥ zᵢ`, or the reverse), so
`f(x(τ)) = z`. This is Brouwer once, on `n` parameters instead of `m` inputs. It uses `Thm. 2`'s
data, not an arbitrary AE proposition, so it does not give Goldsztejn's selection theorem. A `π`
that is not surjective needs no case of its own, and the inputs outside `π`'s domain stay at
whatever `w` the robust range quantifies.

**`Thm. 3` and `Remark 1` — what the printed statements leave open.** "Elementary" is not defined;
the proof uses a `C¹` function whose partial derivatives are bounded as in `Thm. 2`. As in `Thm. 2`,
the box must be nonempty (`lo ≤ hi`): for an empty `x` the radii are negative, `∇̲ = 0` and a point
`f₀` make `z = {f(c(x))}` nonempty, and `range(f, x) = ∅`. `Remark 1` writes
`π : {1, …, m} → ({1, …, n} \ I_A)`, which subtracts the input set `I_A` from the set of output
indices; it is read as `π : {1, …, m} \ I_A → {1, …, n}`, as the sentence after it says. The
requirement that `π` be a map — each input existential in one component only — is what CORA's
`'parallelo'` loses ([`nonlinearSys` `reachInner`](../coverage/contDynamics/nonlinearSys.md);
`prod_inner_ranges_not_subset_image`).
