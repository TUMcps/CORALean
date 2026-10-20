module

public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompact
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Eq. (45)'s linear programs really do have optima

[1, Prop. 7] writes `max` for each `νᵢ` and leaves it there. It is earned: the feasible region
`α ∈ [−1,1]`, `Aα = b` is the constrained zonotope, which is compact, and `C(i,·)x − d(i)` is
continuous on it, so a nonempty `CZ` attains each of the `a` maxima.

This is what turns `ConZonotope.ineqs_contains_iff`'s `IsGreatest` hypothesis from an assumption
into a fact, for the one objective the proposition is about. Nonemptiness is the whole of what is
left to ask: an infeasible program has no optimum, and a `CZ` with inconsistent constraints is
contained in every polytope without any `νᵢ` existing to say so.

## Inputs
* `cZ` – constrained zonotope
* `C` – halfspace normals
* `d` – halfspace offsets

## Hypotheses
* `hne` – the set is nonempty

## Conclusion
* each halfspace violation attains a maximum over the set

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A halfspace's slack is continuous: a row of `C` is a sum of scaled coordinates. -/
theorem aux_continuous_mulVec_sub (C : Mat ℝ q n) (d : Vec ℝ q) (i : Fin q) :
    Continuous fun x : Vec ℝ n => (C *ᵥ x) i - d i := by
  simp only [Matrix.mulVec_apply_eq_sum]
  exact (continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_apply j)).sub continuous_const


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 7]: each `νᵢ` of eq. (45) exists, as soon as the program is feasible. -/
theorem ConZonotope.exists_isGreatest_ineqs (cZ : ConZonotope (Vec ℝ n))
    (hne : cZ.construct.Nonempty) (C : Mat ℝ q n) (d : Vec ℝ q) :
    ∃ ν : Fin q → ℝ,
      ∀ i, IsGreatest ((fun x => (C *ᵥ x) i - d i) '' cZ.construct) (ν i) := by -- --- PROOF ---
  -- one compactness argument per halfspace, then the choices collected
  have key : ∀ i, ∃ v, IsGreatest ((fun x => (C *ᵥ x) i - d i) '' cZ.construct) v := fun i => by
    obtain ⟨x, hx, hmax⟩ := IsCompact.exists_isMaxOn cZ.isCompact_construct hne
      (aux_continuous_mulVec_sub C d i).continuousOn
    exact ⟨_, Set.mem_image_of_mem _ hx, by rintro _ ⟨y, hy, rfl⟩; exact hmax hy⟩
  choose ν hν using key
  exact ⟨ν, hν⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
