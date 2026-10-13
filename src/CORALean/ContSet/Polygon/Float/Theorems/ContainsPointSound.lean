import CORALean.ContSet.Polygon.Float.Operations.ContainsPoint
import CORALean.ContSet.Polygon.Float.Theorems.PieceHoldsSound

/-!
# A `true` from `Polygon.containsPoint` proves membership

The point is in the nominal piece (`Polygon.pieceHolds_sound`), plus the origin, which the
piece's error box holds; so it is in the piece, and the piece is in the region.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.containsPoint_sound {P : Polygon 𝕋} {x : Vec 𝕋 2}
    (h : Polygon.containsPoint P x = true) :
    toRealVec x ∈ ContSet.construct P := by -- --- PROOF ---
  simp only [Polygon.containsPoint, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨p, hp, hbox, hx⟩ := h
  -- the origin is in the box
  have h0 : (0 : Vec ℝ 2) ∈ p.E.construct := fun i =>
    ⟨(toReal_le_of_le (hbox i).1).trans_eq toReal_zero,
      toReal_zero.symm.trans_le (toReal_le_of_le (hbox i).2)⟩
  exact SetUnion.mem_construct.mpr
    ⟨p, hp, ⟨_, Polygon.pieceHolds_sound hx, 0, h0, add_zero _⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
