module

public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# Release in STL

`φ R[a,b] ψ` is `¬(¬φ U[a,b] ¬ψ)`: the dual of the RTL semantics [1, Def. 2].

## Inputs
* `a` – interval lower bound
* `b` – interval upper bound
* `φ` – releasing formula
* `ψ` – released formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the release holds iff the released formula holds until released

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

theorem STL.Formula.sat_release (a b : ℝ≥0) (φ ψ : STL.Formula X) (ξ : ℝ≥0 → X) : -- --- CONCL ---
    (STL.Formula.release a b φ ψ).Sat ξ ↔ ∀ t, a ≤ t → t ≤ b →
      ψ.Sat (Time.shift ξ t) ∨ ∃ i < t, φ.Sat (Time.shift ξ i) := by -- --- PROOF ---
  simp only [STL.Formula.release, STL.Formula.Sat, not_exists, not_and, not_not, not_forall]
  refine forall_congr' fun t => forall_congr' fun h₁ => forall_congr' fun h₂ => ?_
  -- `¬(¬ψ ∧ ∀ i < t, ¬¬φ)`... unfolds to the stated disjunction
  constructor
  · intro h
    by_cases hψ : ψ.Sat (Time.shift ξ t)
    · exact Or.inl hψ
    · obtain ⟨i, hi, hφ⟩ := h hψ
      exact Or.inr ⟨i, hi, hφ⟩
  · rintro (h | ⟨i, hi, h⟩) hψ
    · exact absurd h hψ
    · exact ⟨i, hi, h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
