module

public import CORALean.ContSet.Zonotope.Real.Operations.HalfspaceRange
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# What `[ω̲, ω̄]` says about a zonotope and a halfspace

[1, Sec. 5.2]: "If `ω̲ ≥ 0`, no intersection occurs and if `ω̄ ≤ 0`, the reachable set is
completely in the guard set." The second holds as printed. The first needs `ω̲ > 0`: the
halfspace `{x | nᵀx ≤ d}` is closed, and at `ω̲ = 0` the zonotope touches its boundary —
`halfspaceRange_nonneg_not_disjoint` is the one-point example. Both halves rest on
`|Σᵢ βᵢω⁽ⁱ⁾| ≤ Σᵢ |ω⁽ⁱ⁾|` for `|βᵢ| ≤ 1`.

## Inputs
* `nv` – halfspace normal
* `d` – halfspace offset
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* a positive lower bound excludes `Z` and a nonpositive upper bound includes it

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.2], corrected: `ω̲ > 0` keeps `Z` out of `{x | nᵀx ≤ d}`, and `ω̄ ≤ 0` puts
it inside. -/
theorem Zonotope.halfspaceRange_sound (nv : Vec ℝ n) (d : ℝ)
    (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (0 < (Z.halfspaceRange nv d).inf → ∀ x ∈ Z.construct, d < nv ⬝ᵥ x) ∧
      ((Z.halfspaceRange nv d).sup ≤ 0 → ∀ x ∈ Z.construct, nv ⬝ᵥ x ≤ d) := by -- --- PROOF ---
  -- `nᵀx - d = ω_c + Σᵢ βᵢω⁽ⁱ⁾`, the sum within `Σᵢ |ω⁽ⁱ⁾|`
  have hbound : ∀ x ∈ Z.construct, |nv ⬝ᵥ x - d - (nv ⬝ᵥ Z.c - d)| ≤ ∑ i, |nv ⬝ᵥ Z.G i| := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [dotProduct_add, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    rw [show nv ⬝ᵥ Z.c + ∑ i, β i * nv ⬝ᵥ Z.G i - d - (nv ⬝ᵥ Z.c - d)
      = ∑ i, β i * nv ⬝ᵥ Z.G i by ring]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ i)
  refine ⟨fun hlo x hx => ?_, fun hhi x hx => ?_⟩
  · have := (abs_le.mp (hbound x hx)).1
    simp only [Zonotope.halfspaceRange] at hlo
    linarith
  · have := (abs_le.mp (hbound x hx)).2
    simp only [Zonotope.halfspaceRange] at hhi
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
