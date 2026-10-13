module

public import CORALean.ContSet.HPolytope.Real.Operations.Translate
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.translate` is exactly the shift

A constraint reads a sum as the sum of what it reads, so moving the bound by
what it reads off `t` says the same thing about `x` that the original said about
`x - t`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.translate_exact (t : α) (P : HPolytope α) :
    (t + ·) '' P.construct = (HPolytope.translate t P).construct := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hey⟩, rfl⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · show P.A i (t + y) ≤ P.b i + P.A i t
      rw [map_add]
      linarith [hy i]
    · show P.Ae i (t + y) = P.be i + P.Ae i t
      rw [map_add, hey i]
      ring
  -- back: subtracting `t` again, each shifted bound returning to its own
  · rintro ⟨hle, heq⟩
    refine ⟨x - t, ⟨fun i => ?_, fun i => ?_⟩, ?_⟩
    · have h : P.A i x ≤ P.b i + P.A i t := hle i
      show P.A i (x - t) ≤ P.b i
      rw [map_sub]
      linarith
    · have h : P.Ae i x = P.be i + P.Ae i t := heq i
      show P.Ae i (x - t) = P.be i
      rw [map_sub, h]
      ring
    · show t + (x - t) = x
      abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
