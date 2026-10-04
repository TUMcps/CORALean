import CORALean.Specification.STL.STL
import CORALean.Specification.STL.Theorems.SatNext
import CORALean.Specification.STL.Theorems.ShiftShift

/-!
# Lemma 4: `F_I X₁`

[1, Lemma 4]: `F_I X₁ φ ≡ X₁ F_I φ`, the equivalence it uses beside Table 1.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.finOpen_next_equiv (φ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.finOpen 1 (STL.Formula.next 1 φ)).Sat ξ ↔
      (STL.Formula.next 1 (STL.Formula.finOpen 1 φ)).Sat ξ := by -- --- PROOF ---
  simp only [STL.Formula.sat_next, STL.Formula.Sat, Time.shift_shift]
  constructor
  · rintro ⟨t, h₀, h₁, h⟩
    exact ⟨t, h₀, h₁, by rwa [add_comm]⟩
  · rintro ⟨t, h₀, h₁, h⟩
    exact ⟨t, h₀, h₁, by rwa [add_comm]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
