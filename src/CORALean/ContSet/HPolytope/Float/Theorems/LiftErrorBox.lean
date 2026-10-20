module

public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# The error box of `HPolytope.lift_`

The lifted box is the original carried by `Function.extend`, zero in the coordinates `dims`
misses, which is what lets a lifted polytope with a box still be a lift of the sum.

## Inputs
* `P` – H-polytope
* `dims` – indices indexed by `Fin n`

## Hypotheses
* `hdims` – `dims` is injective

## Conclusion
* the error box of the lift is the zero-extended error box of `P`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.lift_errorBox (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) : -- --- CONCL ---
    (P.lift_ dims).I_error.construct
      = Function.ExtendByZero.hom ℝ dims '' P.I_error.construct := by -- --- PROOF ---
  -- a lifted bound at a selected coordinate is the bound there, and `0` elsewhere
  have hon : ∀ (v : Vec 𝕋 n) (k : Fin n), HPolytope.liftCols dims (fun _ : Fin 1 => v) 0 (dims k)
      = v k := by
    intro v k
    have hsome : ((List.finRange n).find? (fun k' => dims k' = dims k)).isSome = true := by
      rw [List.find?_isSome]
      exact ⟨k, List.mem_finRange k, by simp⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsome
    have hak : a = k := hdims (by simpa using List.find?_some ha)
    simp [HPolytope.liftCols, ha, hak]
  -- and the zero `liftCols` writes elsewhere
  have hoff : ∀ (v : Vec 𝕋 n) (j : Fin N), (∀ k, dims k ≠ j) →
      HPolytope.liftCols dims (fun _ : Fin 1 => v) 0 j = zero := by
    intro v j hj
    have hnone : (List.finRange n).find? (fun k => dims k = j) = none := by
      rw [List.find?_eq_none]
      intro k _ hk
      exact hj k (by simpa using hk)
    simp [HPolytope.liftCols, hnone]
  ext y
  constructor
  -- a point of the lifted box is the lift of its selected coordinates
  · intro hy
    have hy' := Interval.mem_vec_iff.mp hy
    refine ⟨fun k => y (dims k), Interval.mem_vec_iff.mpr fun k => ?_, funext fun j => ?_⟩
    · have h := hy' (dims k)
      simp only [HPolytope.lift_, hon] at h
      exact h
    · by_cases hj : ∃ k, dims k = j
      · obtain ⟨k, rfl⟩ := hj
        simp [hdims.extend_apply]
      · have hj' : ∀ k, dims k ≠ j := fun k hk => hj ⟨k, hk⟩
        have h := hy' j
        simp only [HPolytope.lift_, hoff _ j hj', toReal_zero] at h
        rw [Function.ExtendByZero.hom_apply, Function.extend_apply' _ _ _ (by simpa using hj)]
        exact (le_antisymm h.2 h.1).symm
  -- and the lift of a point of the box is in the lifted one
  · rintro ⟨e, he, rfl⟩
    refine Interval.mem_vec_iff.mpr fun j => ?_
    by_cases hj : ∃ k, dims k = j
    · obtain ⟨k, rfl⟩ := hj
      simp only [HPolytope.lift_, hon, Function.ExtendByZero.hom_apply, hdims.extend_apply]
      exact Interval.mem_vec_iff.mp he k
    · have hj' : ∀ k, dims k ≠ j := fun k hk => hj ⟨k, hk⟩
      simp only [HPolytope.lift_, hoff _ j hj', toReal_zero, Function.ExtendByZero.hom_apply]
      rw [Function.extend_apply' _ _ _ (by simpa using hj)]
      exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
