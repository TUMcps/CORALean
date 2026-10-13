module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Theorems.SatRelease
public import CORALean.Specification.STL.Theorems.ShiftZero

@[expose] public section

/-!
# Lemma 4: `R[0,0]`

[1, Lemma 4]: `φ₁ R[0,0] φ₂ ≡ φ₂`, the equivalence it uses beside Table 1.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
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

theorem STL.release_zero_equiv (φ₁ φ₂ : STL.Formula X) (ξ : ℝ≥0 → X) :
    (STL.Formula.release 0 0 φ₁ φ₂).Sat ξ ↔ φ₂.Sat ξ := by -- --- PROOF ---
  rw [STL.Formula.sat_release]
  constructor
  · intro h
    rcases h 0 le_rfl le_rfl with h | ⟨i, hi, -⟩
    · rwa [Time.shift_zero] at h
    · exact absurd hi not_lt_zero
  · intro h t h₁ h₂
    obtain rfl : t = 0 := le_antisymm h₂ h₁
    exact Or.inl (by rwa [Time.shift_zero])

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
