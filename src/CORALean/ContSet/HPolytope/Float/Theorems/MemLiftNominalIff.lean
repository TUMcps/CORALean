module

public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.HPolytope.Float.Operations.LiftCols
public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in the nominal part of `HPolytope.lift_`

A point is in the lifted nominal part iff its selected coordinates are in the original one.

## Inputs
* `P` – H-polytope
* `dims` – indices indexed by `Fin n`
* `y` – vector of length `N`

## Hypotheses
* `hdims` – `dims` is injective

## Conclusion
* `y` lies in the nominal part of the lift iff its selected coordinates lie in that of `P`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Matrix
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N m : ℕ}

/-- `HPolytope.liftCols` acts on the lifted point as `M` on the selected coordinates. -/
theorem HPolytope.aux_mulVec_liftCols {dims : Fin n → Fin N} (hdims : Function.Injective dims)
    (M : Mat 𝕋 m n) (x : Vec ℝ N) : -- --- CONCL ---
    toRealMat (HPolytope.liftCols dims M) *ᵥ x =
      toRealMat M *ᵥ fun k => x (dims k) := by -- --- PROOF ---
  funext i
  simp only [Matrix.mulVec, dotProduct, toRealMat]
  -- the summand of the lifted row at a column off the range of `dims` is `0`
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      j ∉ Finset.univ.image dims →
        toReal (HPolytope.liftCols dims M i j) * x j = 0 := by
    intro j _ hj
    have hnone : (List.finRange n).find? (fun k => dims k = j) = none := by
      rw [List.find?_eq_none]
      intro k _ hk
      exact hj (Finset.mem_image.2 ⟨k, Finset.mem_univ _, by simpa using hk⟩)
    simp [HPolytope.liftCols, hnone, toReal_zero]
  -- at the image of `k` the stored column is column `k`
  have hval : ∀ k : Fin n, HPolytope.liftCols dims M i (dims k) = M i k := by
    intro k
    have hsome : ((List.finRange n).find? (fun k' => dims k' = dims k)).isSome = true := by
      rw [List.find?_isSome]
      exact ⟨k, List.mem_finRange k, by simp⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsome
    have hak : a = k := hdims (by simpa using List.find?_some ha)
    simp [HPolytope.liftCols, ha, hak]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image dims)) hzero,
    Finset.sum_image (fun a _ b _ h => hdims h)]
  exact Finset.sum_congr rfl fun k _ => by rw [hval k]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_lift_nominal_iff (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) {y : Vec ℝ N} :
    y ∈ (P.lift_ dims).nominal.construct ↔ (fun k => y (dims k)) ∈ P.nominal.construct := by
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  simp only [HPolytope.lift_, HPolytope.aux_mulVec_liftCols hdims]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
