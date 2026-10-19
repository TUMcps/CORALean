module

public import CORALean.ContSet.Capsule.Real.Operations.SegDist

@[expose] public section

/-!
# The axis distance is attained

## Inputs
* `C₁` – first capsule
* `C₂` – second capsule

## Hypotheses
* none

## Conclusion
* `segDist` is attained at parameters in `[-1, 1]`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Some pair of parameters in `[-1, 1]²` realises `segDist`: a continuous function on a compact
set, so CORA's quadratic programme has a minimiser. -/
theorem Capsule.segDist_mem (C₁ C₂ : Capsule n) :
    ∃ t₁ ∈ Set.Icc (-1 : ℝ) 1, ∃ t₂ ∈ Set.Icc (-1 : ℝ) 1,
      ‖(C₁.c + t₁ • C₁.g) - (C₂.c + t₂ • C₂.g)‖₂ = Capsule.segDist C₁ C₂ := by -- --- PROOF ---
  have hc : Continuous fun t : ℝ × ℝ => ‖(C₁.c + t.1 • C₁.g) - (C₂.c + t.2 • C₂.g)‖₂ :=
    continuous_norm₂.comp (by fun_prop)
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1).Nonempty :=
    ⟨(0, 0), by norm_num, by norm_num⟩
  obtain ⟨⟨t₁, t₂⟩, ⟨h₁, h₂⟩, h⟩ := (hK.image hc).sInf_mem (hne.image _)
  exact ⟨t₁, h₁, t₂, h₂, h⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
