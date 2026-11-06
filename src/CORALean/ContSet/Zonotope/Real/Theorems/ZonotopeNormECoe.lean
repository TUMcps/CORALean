module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm

@[expose] public section

/-!
# The extended zonotope norm is the real one on the range of the generators

`Zonotope.zonotopeNormE` is `Zonotope.zonotopeNorm` for every point some coefficient vector reaches.
The real-valued `zonotopeNorm` reads `0` off the range (`coeffNorm`'s `sInf ∅`), a convention; only
there do the two differ (`zonotopeNormE_eq_top`).

## Inputs
* `Z` – zonotope
* `p` – point

## Hypotheses
* `hp` – a coefficient vector reaches the point

## Conclusion
* `zonotopeNormE` is the real-valued `zonotopeNorm`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       03-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where a coefficient vector reaches the point, the extended norm is the real one. -/
theorem Zonotope.zonotopeNormE_eq_coe (Z : Zonotope α) {p : α}
    (hp : ∃ γ, Z.genMap γ = p) : -- --- CONCL ---
    Z.zonotopeNormE p = ((Z.zonotopeNorm p : ℝ) : EReal) := by -- --- PROOF ---
  obtain ⟨γ, hγ, hmin⟩ := exists_coeffNorm_eq Z.genMap hp
  unfold Zonotope.zonotopeNormE
  have hmem : (((‖γ‖ : ℝ)) : EReal) ∈
      ((fun γ : Vec ℝ Z.h => ((‖γ‖ : ℝ) : EReal)) '' {γ | Z.genMap γ = p}) := ⟨γ, hγ, rfl⟩
  refine le_antisymm ((sInf_le hmem).trans_eq ?_) (le_sInf ?_)
  · rw [hmin]; rfl
  · rintro _ ⟨β, hβ, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hβ ▸ coeffNorm_le Z.genMap β)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
