module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid
public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Operations.Cell
public import CORALean.Specification.PointSegmentSignal.Theorems.CellGeIff
public import CORALean.Specification.PointSegmentSignal.Theorems.CellLt
public import CORALean.Specification.PointSegmentSignal.Theorems.CellRel
public import Mathlib.Order.Basic

@[expose] public section

/-!
# The stored value a time reads moves forward

`cell` is monotone on the times `≥ 0`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A later time reads a later value. -/
theorem PointSegmentSignal.cell_mono {T : Type} [LinearOrder T] [Zero T] (s : PointSegmentSignal T)
    (hs : s.IsValid) (t t' : T) (ht : 0 ≤ t) (htt : t ≤ t') :
    s.cell t ≤ s.cell t' := by -- --- PROOF ---
  -- the lower end of the value `t` reads is passed by `t`, hence by `t'`
  have ht' : 0 ≤ t' := ht.trans htt
  have hlt := s.cell_lt hs t ht
  have h1 := (s.cell_ge_iff hs t ht (s.cell t) hlt).1 le_rfl
  refine (s.cell_ge_iff hs t' ht' (s.cell t) hlt).2 ?_
  rcases h1 with h | ⟨h, h'⟩
  · exact Or.inl (h.trans_le htt)
  · rcases htt.eq_or_lt with e | e
    · exact Or.inr ⟨h, e.symm.trans h'⟩
    · exact Or.inl (by rw [h'] at e; exact e)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
