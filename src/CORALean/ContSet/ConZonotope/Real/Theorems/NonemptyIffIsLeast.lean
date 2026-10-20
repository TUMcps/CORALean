module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsFeasibleIffIsLeast

@[expose] public section

/-!
# Emptiness by one linear program

[1, Prop. 2, eq. 19]: `Z ≠ ∅` iff `min{‖ξ‖∞ : Aξ = b} ≤ 1`. `Z` is `ofMat c G A b`, whose
constraint is the polytope `Aξ = b` on the coefficients, and `‖·‖` on `Vec` is the sup norm. The
minimum is an `IsLeast`: an infeasible program has none, which is the paper's empty `min`.

## Inputs
* `α` – ambient space
* `q` – number of constraints
* `h` – number of generators
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset

## Hypotheses
* none

## Conclusion
* nonempty iff a linear program has minimum norm at most one

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2, eq. 19]: `Z ≠ ∅` iff the minimum of `‖ξ‖∞` over `Aξ = b` exists and is `≤ 1`. -/
theorem ConZonotope.nonempty_iff_isLeast {α : Type} [AddCommGroup α] [Module ℝ α] {q h : ℕ}
    (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) :
    (ConZonotope.ofMat c G A b).construct.Nonempty ↔
      ∃ m, IsLeast {t | ∃ ξ : Vec ℝ h, A *ᵥ ξ = b ∧ t = ‖ξ‖} m ∧ m ≤ 1 := by -- --- PROOF ---
  rw [← ConZonotope.exists_feasible_iff_isLeast A b]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨β, hβ, hAβ, _⟩ := ConZonotope.mem_ofMat_iff.mp hx
    exact ⟨β, funext hAβ, hβ⟩
  · rintro ⟨β, hAβ, hβ⟩
    exact ⟨_, ConZonotope.mem_ofMat_iff.mpr ⟨β, hβ, fun i => congrFun hAβ i, rfl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
