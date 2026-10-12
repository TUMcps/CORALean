import CORALean.ContSet.Polygon.Float.Operations.Subtract
import CORALean.ContSet.Polygon.Float.Theorems.PieceSubsetSound

/-!
# `Polygon.subtract` encloses the set difference and stays in the minuend

A point of `P \ Q` lies in a piece `p` of `P`; if a piece of `Q` certainly covered `p`, the
point would be in `Q`, so `p` is kept. Outer for the set difference, and a subset of `P`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.subtract_outer (P Q : Polygon 𝕋) :
    ContSet.construct P \ ContSet.construct Q ⊆ ContSet.construct (Polygon.subtract P Q) ∧
      ContSet.construct (Polygon.subtract P Q) ⊆ ContSet.construct P := by -- --- PROOF ---
  constructor
  · rintro x ⟨hP, hQ⟩
    obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hP
    refine SetUnion.mem_construct.mpr ⟨p, List.mem_filter.mpr ⟨hp, ?_⟩, hxp⟩
    -- a covering piece of `Q` would hold `x`
    simp only [Bool.not_eq_true', List.any_eq_false]
    intro q hq hpq
    exact hQ (SetUnion.mem_construct.mpr ⟨q, hq, Polygon.pieceSubset_sound hpq hxp⟩)
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := SetUnion.mem_construct.mp hx
    exact SetUnion.mem_construct.mpr ⟨p, (List.mem_filter.mp hp).1, hxp⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
