module

public import CORALean.ContSet.HPolytope.Float.Operations.Origin
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.origin` denotes exactly the origin, over a floating-point scalar

The stored identity reads as ℝ's, so the equality rows pin every coordinate to `[0, 0]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.origin_exact (n : ℕ) :
    (HPolytope.origin n : HPolytope 𝕋 (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  -- the stored identity reads as ℝ's
  have hA : toRealMat (HPolytope.origin n : HPolytope 𝕋 (Vec 𝕋 n)).Ae = (1 : Mat ℝ n n) := by
    refine Matrix.ext fun (i : Fin n) (j : Fin n) => ?_
    show toReal (if i = j then (one : 𝕋) else zero) = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    rw [Matrix.one_apply]
    split_ifs
    · exact toReal_one
    · exact toReal_zero
  ext x
  rw [HPolytope.mem_construct_iff, Set.mem_singleton_iff, hA]
  simp only [HPolytope.origin, Interval.origin, toReal_zero, Matrix.one_mulVec]
  constructor
  · rintro ⟨-, h⟩
    funext i
    exact le_antisymm (h i).2 (h i).1
  · rintro rfl
    exact ⟨fun i => i.elim0, fun i => ⟨le_rfl, le_rfl⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
