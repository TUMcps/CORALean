module

public import CORALean.ContSet.Polygon.Float.Operations.IsConvex
public import CORALean.ContSet.Polygon.Float.Theorems.PieceSubsetSound
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Theorems.Basic

@[expose] public section

/-!
# A `true` from `Polygon.isConvex` proves the region convex

With no piece the region is empty. Otherwise the piece that holds every piece
(`Polygon.pieceSubset_sound`) is the whole region, and a float piece is convex
(`VPolytope.convex_construct`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isConvex_sound {P : Polygon 𝕋} (h : Polygon.isConvex P = true) :
    Convex ℝ (ContSet.construct P) := by -- --- PROOF ---
  simp only [Polygon.isConvex, Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true,
    List.all_eq_true] at h
  rcases h with h | ⟨p, hp, hall⟩
  · -- no piece: the empty region
    have : ContSet.construct P = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨q, hq, -⟩ := SetUnion.mem_construct.mp hx
      rw [h] at hq
      exact List.not_mem_nil hq
    rw [this]
    exact convex_empty
  · -- the region is the piece that holds every piece
    have : ContSet.construct P = p.construct := by
      ext x
      constructor
      · intro hx
        obtain ⟨q, hq, hxq⟩ := SetUnion.mem_construct.mp hx
        exact Polygon.pieceSubset_sound (hall q hq) hxq
      · intro hx
        exact SetUnion.mem_construct.mpr ⟨p, hp, hx⟩
    rw [this]
    exact p.convex_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
