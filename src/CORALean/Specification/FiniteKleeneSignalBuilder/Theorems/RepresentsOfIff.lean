module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Represents

@[expose] public section

/-!
# What a builder says depends on the predicates only up to equivalence

If a builder represents `PT` and `PF` and these are equivalent to `PT'` and `PF'`, it represents
those.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteKleeneSignalBuilder.represents_of_iff (b : FiniteKleeneSignalBuilder) (d : ℝ)
    {PT PF PT' PF' : ℝ → Prop} (h : b.Represents d PT PF) (hT : ∀ t, PT t ↔ PT' t)
    (hF : ∀ t, PF t ↔ PF' t) : b.Represents d PT' PF' := by
  obtain ⟨hv, hd, hts⟩ := h
  refine ⟨hv, hd, fun t h0 h1 => ?_⟩
  obtain ⟨⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩⟩ := hts t h0 h1
  exact ⟨⟨x, hx, hxi.trans (hT t)⟩, ⟨y, hy, hyi.trans (hF t)⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
