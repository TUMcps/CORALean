module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.ShiftZero

@[expose] public section

/-!
# Lemma 4: `U[0,0]`

[1, Lemma 4]: `φ₁ U[0,0] φ₂ ≡ φ₂`, the equivalence it uses beside Table 1.

## Inputs
* `φ₁` – left formula
* `φ₂` – right formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* an until on the zero interval is the right formula

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and Hybrid
      Systems". Automated Technology for Verification and Analysis, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.until_zero_equiv (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (STL.Formula.until 0 0 φ₁ φ₂).Satisfies ξ ↔ φ₂.Satisfies ξ := by -- --- PROOF ---
  simp only [STL.Formula.Satisfies]
  constructor
  · rintro ⟨t, h₁, h₂, h₃, -⟩
    obtain rfl : t = 0 := le_antisymm h₂ h₁
    rwa [Time.shift_zero] at h₃
  · exact fun h => ⟨0, le_rfl, le_rfl, by rwa [Time.shift_zero], fun t ht => absurd ht not_lt_zero⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
