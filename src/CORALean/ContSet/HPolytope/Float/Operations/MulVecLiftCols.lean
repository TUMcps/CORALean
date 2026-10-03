import CORALean.ContSet.HPolytope.Float.Operations.LiftCols
import Mathlib.Data.Matrix.Mul

/-!
# `HPolytope.liftCols` acts on the lifted point as `M` on the selected coordinates

For an injective `dims`, a row of the lifted matrix against `x` is the row of `M` against
`x ∘ dims`: each stored column is read once, and the columns off the range of `dims` are `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mulVec_liftCols {dims : Fin n → Fin N} (hdims : Function.Injective dims)
    (M : Mat 𝕋 m n) (x : Vec ℝ N) :
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
