import CORALean.ContSet.Zonotope.Real.Operations.Shear
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import CORALean.ContSet.Zonotope.Real.Theorems.ShearComb

/-!
# A point of the sheared zonogon is the sheared point of the zonogon

`p ∈ (Z.shear κ).construct ↔ (p₀ + κ p₁, p₁) ∈ Z.construct`: the same coefficients serve, since
the shear is linear. A line `x - κ y = γ` through `Z` is therefore a vertical line through the
sheared zonogon, and a vertical section theorem for zonogons in the upper half-plane ([1, Alg. 3])
is one for every direction but the horizontal.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_shear_construct (Z : Zonotope (Vec ℝ 2)) (κ : ℝ) (p : Vec ℝ 2) :
    p ∈ (Z.shear κ).construct ↔
      (![p 0 + κ * p 1, p 1] : Vec ℝ 2) ∈ Z.construct := by -- --- PROOF ---
  -- the unshear undoes the shear
  have inv1 : ∀ z : Vec ℝ 2, (![(![z 0 - κ * z 1, z 1] : Vec ℝ 2) 0 +
      κ * (![z 0 - κ * z 1, z 1] : Vec ℝ 2) 1, (![z 0 - κ * z 1, z 1] : Vec ℝ 2) 1] : Vec ℝ 2)
      = z := fun z => by ext k; fin_cases k <;> simp
  have inv2 : ∀ p : Vec ℝ 2, (![(![p 0 + κ * p 1, p 1] : Vec ℝ 2) 0 -
      κ * (![p 0 + κ * p 1, p 1] : Vec ℝ 2) 1, (![p 0 + κ * p 1, p 1] : Vec ℝ 2) 1] : Vec ℝ 2)
      = p := fun p => by ext k; fin_cases k <;> simp
  -- a point of the sheared zonogon has the same coefficients, and conversely
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β, hβ, ?_⟩
    have e : ((Z.shear κ).c + ∑ j : Fin (Z.shear κ).h, β j • (Z.shear κ).G j)
        = ![(Z.c + ∑ j, β j • Z.G j) 0 - κ * (Z.c + ∑ j, β j • Z.G j) 1,
          (Z.c + ∑ j, β j • Z.G j) 1] := Zonotope.shear_comb Z κ β
    rw [e]
    exact (inv1 _)
  -- conversely, the unsheared point has coefficients `β`
  · rintro ⟨β, hβ, h⟩
    refine ⟨β, hβ, ?_⟩
    have e : ((Z.shear κ).c + ∑ j : Fin (Z.shear κ).h, β j • (Z.shear κ).G j)
        = ![(Z.c + ∑ j, β j • Z.G j) 0 - κ * (Z.c + ∑ j, β j • Z.G j) 1,
          (Z.c + ∑ j, β j • Z.G j) 1] := Zonotope.shear_comb Z κ β
    rw [e, ← h]
    exact (inv2 p).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
