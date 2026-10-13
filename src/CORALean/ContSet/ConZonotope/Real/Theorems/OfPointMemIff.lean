module

public import CORALean.ContSet.ConZonotope.Real.Operations.OfPoint
public import CORALean.ContSet.ConZonotope.Real.Theorems.OfPointMem

@[expose] public section

/-!
# `ConZonotope.ofPoint` denotes exactly one point

The converse to `mem_ofPoint`: no generator leaves no coefficient to spend.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mem_ofPoint_iff (v x : α) :
    x ∈ (ConZonotope.ofPoint v).construct ↔ x = v := by -- --- PROOF ---
  constructor
  · rintro ⟨β, _, _, h⟩
    simpa [ConZonotope.ofPoint] using h
  · rintro rfl
    exact ConZonotope.mem_ofPoint _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
