module

public import CORALean.ContSet.ContSet.Definitions.HyperplanePolyhedron
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The sum of two `S`-band intersections lies in the band of the summed bounds

[1, Sec. 4.2] prints `[m₁, M₁]_S ⊕ [m₂, M₂]_S = [m₁ + m₂, M₁ + M₂]_S`. The inclusion
proved here is the half that holds: `s·(x₁ + x₂) = s·x₁ + s·x₂` lies between the summed
bounds. The equality fails when a bound is not attained
(`ContSet.exists_hyperplanePolyhedron_add_ne`). The inclusion is what [1, Alg. 2] with
`S`-bands needs, and there the bounds are attained ([1, Prop. 2]).

## Inputs
* `S` – directions
* `m₁` – first lower bounds
* `M₁` – first upper bounds
* `m₂` – second lower bounds
* `M₂` – second upper bounds

## Hypotheses
* none

## Conclusion
* the sum of the two polyhedra lies in the polyhedron of the summed bounds

## References

* [1] [A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of Linear
      Time-Invariant Systems with Inputs". Hybrid Systems: Computation and Control,
      2006.](../../../../../references/2006/girard-hscc-lti-inputs.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2], corrected: `[m₁, M₁]_S ⊕ [m₂, M₂]_S ⊆ [m₁ + m₂, M₁ + M₂]_S`. -/
theorem ContSet.hyperplanePolyhedron_add_subset (S : Finset (Vec ℝ n))
    (m₁ M₁ m₂ M₂ : Vec ℝ n → ℝ) : -- --- CONCL ---
    ContSet.hyperplanePolyhedron S m₁ M₁ + ContSet.hyperplanePolyhedron S m₂ M₂
      ⊆ ContSet.hyperplanePolyhedron S (m₁ + m₂) (M₁ + M₂) := by -- --- PROOF ---
  -- the value of a sum along `s` is the sum of the values
  rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ s hs
  rw [add_dotProduct, Pi.add_apply, Pi.add_apply]
  obtain ⟨h₁, h₂⟩ := hx₁ s hs
  obtain ⟨h₃, h₄⟩ := hx₂ s hs
  exact ⟨add_le_add h₁ h₃, add_le_add h₂ h₄⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
