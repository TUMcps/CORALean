module

public import CORALean.Global.RobustInvariant
public import CORALean.Global.RegionOfAttraction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-!
# The region-of-attraction criterion without limits

[1, Sec. 3.1.2] verifies a region of attraction by `∃ t > 0 : R(t) ⊆ S` for `R(0) = D`, with
`D = {[x(0); y(0)] | ∀ u(·) : lim_{t→∞} γ(t, x(0), y(0), u(·)) ∈ S}` (`regionOfAttraction`). A
solution circling inside `S` has no limit, so the criterion does not place its initial state in
`D` as printed. The harmonic oscillator `ẋ₁ = x₂`, `ẋ₂ = -x₁`, no input, is a counterexample: the
closed unit disc `S` is robust positively invariant, `R(1) ⊆ S` for `R(0) = S`, and from `(1, 0)`
the solution `(cos t, -sin t)` does not converge, so `S ⊄ D`. What the criterion does give is that
every solution from `R(0)` is in `S` from `t` on (`RobustInvariant.mem_of_reach_subset`), and
`R(0) ⊆ D` where the limits exist (`subset_regionOfAttraction_of_reach_subset`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the invariant unit disc is not contained in the region of attraction as printed

## References

* [1] M. Althoff. "Benchmarks for the Formal Verification of Power Systems". In Proc. of the
      9th International Workshop on Applied Verification of Continuous and Hybrid Systems
      (ARCH22), EPiC Series in Computing, vol. 90, pp. 26-43, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology


-- =======================================  MAIN THEOREM  ======================================= --

theorem regionOfAttraction_counterexample : -- --- CONCL ---
    let γ : ℝ → ℝ × ℝ → (ℝ → Unit) → ℝ × ℝ := fun t x _ =>
      (x.1 * Real.cos t + x.2 * Real.sin t, -(x.1 * Real.sin t) + x.2 * Real.cos t)
    let S : Set (ℝ × ℝ) := {x | x.1 ^ 2 + x.2 ^ 2 ≤ 1}
    (∀ x u t, HasDerivAt (fun r => γ r x u) ((γ t x u).2, -(γ t x u).1) t) ∧
      (∀ x u, γ 0 x u = x) ∧
      (∀ t s x u, γ (t + s) x u = γ s (γ t x u) (fun r => u (t + r))) ∧
      RobustInvariant γ Set.univ S ∧ IsClosed S ∧
      (∀ x₀ ∈ S, ∀ u ∈ (Set.univ : Set (ℝ → Unit)), γ 1 x₀ u ∈ S) ∧
      ¬ S ⊆ regionOfAttraction γ Set.univ S := by -- --- PROOF ---
  intro γ S
  -- a rotation keeps `x₁² + x₂²`
  have hnorm : ∀ t x u, (γ t x u).1 ^ 2 + (γ t x u).2 ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    intro t x u
    simp only [γ]
    linear_combination (x.1 ^ 2 + x.2 ^ 2) * Real.sin_sq_add_cos_sq t
  have hinv : RobustInvariant γ Set.univ S := by
    intro t _ u _ x₀ hx₀
    simp only [S, Set.mem_setOf_eq] at hx₀ ⊢
    rw [hnorm t x₀ u]
    exact hx₀
  refine ⟨fun x u t => ?_, fun x u => ?_, fun t s x u => ?_, hinv, ?_,
    fun x₀ hx₀ u hu => hinv 1 one_pos u hu x₀ hx₀, ?_⟩
  · -- `γ` solves `ẋ₁ = x₂`, `ẋ₂ = -x₁`
    have h1 := ((Real.hasDerivAt_cos t).const_mul x.1).add ((Real.hasDerivAt_sin t).const_mul x.2)
    have h2 := ((Real.hasDerivAt_sin t).const_mul x.1).neg.add
      ((Real.hasDerivAt_cos t).const_mul x.2)
    convert h1.prodMk h2 using 1
    · funext r
      simp only [γ, Pi.add_apply, Pi.neg_apply]
    · ext <;> simp only [γ] <;> ring
  · simp [γ]
  · -- time-invariance: rotations compose
    ext <;> simp only [γ, Real.cos_add, Real.sin_add] <;> ring
  · exact isClosed_le (by fun_prop) continuous_const
  · -- from `(1, 0)` the solution is `(cos t, -sin t)`, which does not converge
    intro hsub
    obtain ⟨L, -, hL⟩ := hsub (show ((1 : ℝ), (0 : ℝ)) ∈ S by norm_num [S])
      (fun _ => ()) (Set.mem_univ _)
    have hcos : Tendsto Real.cos atTop (𝓝 L.1) := by
      have := (continuous_fst.tendsto L).comp hL
      simpa [γ, Function.comp_def] using this
    have hseq : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have hseq' : Tendsto (fun k : ℕ => (k : ℝ) * (2 * Real.pi) + Real.pi) atTop atTop :=
      tendsto_atTop_add_const_right _ _ hseq
    have c1 : Real.cos ∘ (fun k : ℕ => (k : ℝ) * (2 * Real.pi)) = fun _ => 1 := by
      funext k; simp [Real.cos_nat_mul_two_pi]
    have c2 : Real.cos ∘ (fun k : ℕ => (k : ℝ) * (2 * Real.pi) + Real.pi) = fun _ => -1 := by
      funext k; simp [Real.cos_add_pi, Real.cos_nat_mul_two_pi]
    have e1 := hcos.comp hseq
    have e2 := hcos.comp hseq'
    rw [c1, tendsto_const_nhds_iff] at e1
    rw [c2, tendsto_const_nhds_iff] at e2
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
