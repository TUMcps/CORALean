module

public import CORALean.ContSet.Zonotope.Real.Operations.PointUp

@[expose] public section

/-!
# Turning generators upward does not change the zonogon

[1, Alg. 3]: "replacing a generator `g` by its opposite `-g` does not modify the shape of a
zonogon". Each generator of `pointUp` is `±g`, so the coefficient `β` of a point becomes `±β`.

## Inputs
* `Z` – planar zonotope

## Hypotheses
* none

## Conclusion
* turning generators upward leaves the set unchanged

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Each generator of `pointUp` is a unit multiple of the original. -/
private theorem Zonotope.aux_pointUp_smul (Z : Zonotope (Vec ℝ 2)) (i : Fin Z.h) :
    ∃ e : ℝ, |e| = 1 ∧ Z.pointUp.G i = e • Z.G i := by
  by_cases h : Z.G i 1 < 0 ∨ (Z.G i 1 = 0 ∧ Z.G i 0 < 0)
  · exact ⟨-1, by simp, by simp [Zonotope.pointUp, h]⟩
  · exact ⟨1, by simp, by simp [Zonotope.pointUp, h]⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_pointUp (Z : Zonotope (Vec ℝ 2)) : -- --- CONCL ---
    Z.pointUp.construct = Z.construct := by -- --- PROOF ---
  choose e he hG using Zonotope.aux_pointUp_smul Z
  ext x
  constructor
  -- a point of the turned zonogon has the same coefficients up to sign
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => β j * e j, fun j => ?_, ?_⟩
    · rw [abs_mul, he j, mul_one]
      exact hβ j
    · show Z.c + ∑ j, β j • Z.pointUp.G j = _
      simp only [hG, smul_smul]
      rfl
  -- and conversely
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => β j * e j, fun j => ?_, ?_⟩
    · rw [abs_mul, he j, mul_one]
      exact hβ j
    · show _ = Z.c + ∑ j, (β j * e j) • Z.pointUp.G j
      simp only [hG, smul_smul]
      refine congrArg (Z.c + ·) (Finset.sum_congr rfl fun j _ => ?_)
      have : e j * e j = 1 := by
        rcases abs_eq (zero_le_one' ℝ) |>.mp (he j) with h | h <;> rw [h] <;> norm_num
      rw [mul_assoc, this, mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
