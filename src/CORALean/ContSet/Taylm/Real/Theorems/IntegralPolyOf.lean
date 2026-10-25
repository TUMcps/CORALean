module

public import CORALean.ContSet.Taylm.Real.Operations.IntegrateTerms
public import CORALean.ContSet.Taylm.Real.Theorems.ContinuousPolyOf
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Integrating a term list in one variable

`∫₀^{tᵢ} P(t with tᵢ := s) ds` is `integrateTerms i P` at `t`: a monomial with `tᵢ` replaced by `s`
is the other coordinates' product times `s^{eᵢ}`, whose integral is `tᵢ^{eᵢ+1}/(eᵢ+1)`. The
polynomial half of [1, Def. 3 (antiderivation)].

## Inputs
* `i` – variable index
* `L` – terms of the polynomial
* `t` – point

## Hypotheses
* none

## Conclusion
* integrating the polynomial in that variable equals evaluating the integrated terms

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A monomial at `t` with `tᵢ := s` splits off the power of `s`. -/
theorem Taylm.aux_monomial_update (e : Fin n → ℕ) (t : Vec ℝ n) (i : Fin n)
    (s : ℝ) : -- --- CONCL ---
    Taylm.monomial e (Function.update t i s) =
      (∏ k ∈ Finset.univ.erase i, t k ^ e k) * s ^ e i := by -- --- PROOF ---
  rw [Taylm.monomial, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.integral_polyOf (i : Fin n) (L : List (ℝ × (Fin n → ℕ)))
    (t : Vec ℝ n) : -- --- CONCL ---
    ∫ s in (0 : ℝ)..t i, Taylm.polyOf L (Function.update t i s)
      = Taylm.polyOf (Taylm.integrateTerms i L) t := by -- --- PROOF ---
  have hc : ∀ L' : List (ℝ × (Fin n → ℕ)),
      Continuous fun s : ℝ => Taylm.polyOf L' (Function.update t i s) := fun L' =>
    (Taylm.continuous_polyOf L').comp (continuous_const.update i continuous_id)
  induction L with
  | nil => simp [Taylm.integrateTerms]
  | cons a L ih =>
    simp only [Taylm.polyOf_cons]
    rw [intervalIntegral.integral_add ?_ ((hc L).intervalIntegrable _ _), ih]
    · simp only [Taylm.integrateTerms, List.map_cons, Taylm.polyOf_cons]
      congr 1
      simp only [Taylm.aux_monomial_update, intervalIntegral.integral_const_mul,
        integral_pow]
      -- the monomial with `eᵢ + 1` at `t`
      have hm : Taylm.monomial (a.2 + Pi.single i 1) t
          = (∏ k ∈ Finset.univ.erase i, t k ^ a.2 k) * t i ^ (a.2 i + 1) := by
        have := Taylm.aux_monomial_update (a.2 + Pi.single i 1) t i (t i)
        rw [Function.update_eq_self] at this
        rw [this]
        congr 1
        · refine Finset.prod_congr rfl fun k hk => ?_
          simp [Finset.ne_of_mem_erase hk]
        · simp
      rw [hm]
      have h1 : ((a.2 i : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    · exact (continuous_const.mul ((by
        simp only [Taylm.aux_monomial_update]
        exact continuous_const.mul (continuous_pow _)) : Continuous fun s : ℝ =>
          Taylm.monomial a.2 (Function.update t i s))).intervalIntegrable _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
