import CORALean.HybridDynamics.Definitions.SdcInput
import CORALean.HybridDynamics.Operations.SdcInputFloat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.InvFactorialBoundsFloat
import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint
import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
import CORALean.ContSet.Interval.Float.Theorems.SumTermsMatMem

/-!
# The float box holds the constant flow

For `t ≥ 0`, `b = Θ(t)x₀ + Γ*(t)u_c` of the floats read as reals is in `GuardMap.sdcInputFloat`:
each coefficient `tᵖ/q!` lies between its corner products (`powDown_le`, `le_powUp`,
`invFactorialBounds_mem`), each `Aⁱ` in `matPow` (`matPow_outer`), each term in its `smul`, the
sums in `sumTermsMat` (`Θ`'s indices `i = k + 2`), and the products and their sum in
`mtimesIntervalMat` and `plus`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: `b` is in the box, for `t ≥ 0`. -/
theorem GuardMap.sdcInput_mem_sdcInputFloat (A : Mat 𝕋 n n) (uc : Vec 𝕋 n) {t : 𝕋} (η : ℕ)
    (x₀ : Vec 𝕋 n) (ht : 0 ≤ toReal t) :
    GuardMap.sdcInput (toRealMat A) (toRealVec uc) (toReal t) η (toRealVec x₀)
      ∈ (GuardMap.sdcInputFloat A uc t η x₀).construct := by -- --- PROOF ---
  -- `tᵖ/q!` between the corner products
  have hcoef : ∀ p q : ℕ, toReal (Interval.mulLo (powDown t p) (powUp t p)
      (MatExp.invFactorialBounds q).1 (MatExp.invFactorialBounds q).2) ≤ toReal t ^ p / q.factorial
      ∧ toReal t ^ p / q.factorial ≤ toReal (Interval.mulHi (powDown t p) (powUp t p)
        (MatExp.invFactorialBounds q).1 (MatExp.invFactorialBounds q).2) := fun p q => by
    rw [div_eq_mul_inv]
    exact Interval.mul_between_corners (powDown_le ht le_rfl p) (le_powUp ht le_rfl p)
      (MatExp.invFactorialBounds_mem q).1 (MatExp.invFactorialBounds_mem q).2
  have hpow : ∀ i, toRealMat A ^ i ∈ (Interval.matPow (Interval.point A) i).construct := fun i =>
    Interval.matPow_outer _ (Interval.mem_point A) i
  -- `Θ`, reindexed by `i = k + 2`
  have hΘ : (∑ i ∈ Finset.Ico 2 (η + 1), (toReal t ^ (i - 1) / (i.factorial : ℝ)) •
      toRealMat A ^ i) ∈ (Interval.sumTermsMat (fun k => Interval.smul
        (Interval.mulLo (powDown t (k + 1)) (powUp t (k + 1)) (MatExp.invFactorialBounds (k + 2)).1
          (MatExp.invFactorialBounds (k + 2)).2)
        (Interval.mulHi (powDown t (k + 1)) (powUp t (k + 1)) (MatExp.invFactorialBounds (k + 2)).1
          (MatExp.invFactorialBounds (k + 2)).2)
        (Interval.matPow (Interval.point A) (k + 2))) (η - 1)).construct := by
    rw [Finset.sum_Ico_eq_sum_range, show η + 1 - 2 = η - 1 by omega]
    refine Interval.sum_mem_sumTermsMat _ _ _ fun k _ => ?_
    rw [show 2 + k = k + 2 by ring, show k + 2 - 1 = k + 1 by omega]
    exact Interval.smul_outer (hcoef (k + 1) (k + 2)).1 (hcoef (k + 1) (k + 2)).2 _ (hpow (k + 2))
  -- `Γ*`, term by term
  have hΓ : (∑ i ∈ Finset.range (η + 1), (toReal t ^ i / ((i + 1).factorial : ℝ)) •
      toRealMat A ^ i) ∈ (Interval.sumTermsMat (fun k => Interval.smul
        (Interval.mulLo (powDown t k) (powUp t k) (MatExp.invFactorialBounds (k + 1)).1
          (MatExp.invFactorialBounds (k + 1)).2)
        (Interval.mulHi (powDown t k) (powUp t k) (MatExp.invFactorialBounds (k + 1)).1
          (MatExp.invFactorialBounds (k + 1)).2)
        (Interval.matPow (Interval.point A) k)) (η + 1)).construct :=
    Interval.sum_mem_sumTermsMat _ _ _ fun k _ =>
      Interval.smul_outer (hcoef k (k + 1)).1 (hcoef k (k + 1)).2 _ (hpow k)
  -- the products with `x₀` and `u_c`, and their sum
  exact Interval.plus_outer _ _ (Set.add_mem_add
    (Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hΘ ⟨_, Interval.mem_point x₀, rfl⟩))
    (Interval.mtimesIntervalMat_outer _ _ (Set.mem_biUnion hΓ ⟨_, Interval.mem_point uc, rfl⟩)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
