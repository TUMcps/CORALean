import CORALean.ContSet.Zoo.Float.Operations.OfInterval
import CORALean.ContSet.Zoo.Float.Theorems.DiagonalBlockSum
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `Zoo.ofInterval` reaches the box

Every value the box takes at coordinate `i` is a value of the zoo's function on `[-1, 1]ⁿ`, so the
function is the box's coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.ofInterval_attains (I : Interval (Vec 𝕋 n)) (i : Fin n) {x : Vec ℝ n}
    (hx : x ∈ I.construct) :
    ∃ t ∈ Real.Taylm.box n,
      x i = toReal (I.center i) + toReal (I.radiusFrom i) * t i := by -- --- PROOF ---
  obtain ⟨β, hβ, hxβ⟩ := Zonotope.mem_nominalSet_iff.mp (I.subset_nominal_zonotope hx)
  refine ⟨β, hβ, ?_⟩
  have hs : ∑ j, toReal (I.zonotope.G j i) * β j = toReal (I.radiusFrom i) * β i :=
    Zoo.diagonalBlock_sum I i β
  rw [hxβ i, hs]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
