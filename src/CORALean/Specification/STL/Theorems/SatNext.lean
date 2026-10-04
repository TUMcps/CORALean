import CORALean.Specification.STL.STL

/-!
# The next-operator in STL

`ξ ⊨ₜ Xₐ φ ⇔ ⟨ξ⟩ₐ ⊨ₜ φ`, the first equivalence of [1, Sec. 2.2]'s definition of `Xₐ`.

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

theorem STL.Formula.sat_next (a : ℝ≥0) (φ : STL.Formula X) (ξ : ℝ≥0 → X) :
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
