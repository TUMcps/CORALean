module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# The next-operator in STL

`ξ ⊨ₜ Xₐ φ ⇔ ⟨ξ⟩ₐ ⊨ₜ φ`, the first equivalence of [1, Sec. 2.2]'s definition of `Xₐ`.

## Inputs
* `a` – time shift
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* next holds iff the formula holds on the shifted trace

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

theorem STL.Formula.sat_next (a : ℝ≥0) (φ : STL.Formula X) (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (STL.Formula.next a φ).Sat ξ ↔ φ.Sat (Time.shift ξ a) := by -- --- PROOF ---
  unfold STL.Formula.next
  constructor
  · rintro ⟨t, h₁, h₂, h₃, -⟩
    -- the interval `[a,a]` leaves `t = a`
    obtain rfl : t = a := le_antisymm h₂ h₁
    exact h₃
  · exact fun h => ⟨a, le_rfl, le_rfl, h, fun _ _ => trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
