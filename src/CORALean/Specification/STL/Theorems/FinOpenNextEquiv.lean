module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatNext
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# Lemma 4: `F_I X₁`

[1, Lemma 4]: `F_I X₁ φ ≡ X₁ F_I φ`, the equivalence it uses beside Table 1.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* eventually over an open interval commutes with next

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

theorem STL.finOpen_next_equiv (φ : STL.Formula X) (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (STL.Formula.finOpen 1 (STL.Formula.next 1 φ)).Satisfies ξ ↔
      (STL.Formula.next 1 (STL.Formula.finOpen 1 φ)).Satisfies ξ := by -- --- PROOF ---
  simp only [STL.Formula.sat_next, STL.Formula.Satisfies, Time.shift_shift]
  constructor
  · rintro ⟨t, h₀, h₁, h⟩
    exact ⟨t, h₀, h₁, by rwa [add_comm]⟩
  · rintro ⟨t, h₀, h₁, h⟩
    exact ⟨t, h₀, h₁, by rwa [add_comm]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
