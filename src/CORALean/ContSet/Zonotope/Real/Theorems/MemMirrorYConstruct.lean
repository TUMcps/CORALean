import CORALean.ContSet.Zonotope.Real.Operations.MirrorY
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring

/-!
# A point of the mirrored zonogon is the mirror image of a point of the original

`p ∈ Z.mirrorY.construct ↔ (p₀, -p₁) ∈ Z.construct`: the same coefficients serve, since
negating `y` commutes with the sum. So the section of the mirror image at `x = γ` is the
negative of the original's, which [1, Alg. 4] uses to get `M` from a search for `m`.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The mirrored combination is the mirror image of the combination. -/
theorem Zonotope.aux_mirrorY_comb (Z : Zonotope (Vec ℝ 2)) (β : Fin Z.h → ℝ) :
    Z.mirrorY.c + ∑ j, β j • Z.mirrorY.G j
      = ![(Z.c + ∑ j, β j • Z.G j) 0, -(Z.c + ∑ j, β j • Z.G j) 1] := by -- --- PROOF ---
  ext k
  fin_cases k
  · simp [Zonotope.mirrorY, Finset.sum_apply]
  · simp [Zonotope.mirrorY, Finset.sum_apply, Finset.sum_neg_distrib]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mem_mirrorY_construct (Z : Zonotope (Vec ℝ 2)) (p : Vec ℝ 2) :
    p ∈ Z.mirrorY.construct ↔ (![p 0, -p 1] : Vec ℝ 2) ∈ Z.construct := by -- --- PROOF ---
  have inv : ∀ q : Vec ℝ 2, (![(![q 0, -q 1] : Vec ℝ 2) 0, -(![q 0, -q 1] : Vec ℝ 2) 1] : Vec ℝ 2)
      = q := fun q => by ext k; fin_cases k <;> simp
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨β, hβ, ?_⟩
    have e : (Z.mirrorY.c + ∑ j : Fin Z.mirrorY.h, β j • Z.mirrorY.G j)
        = ![(Z.c + ∑ j, β j • Z.G j) 0, -(Z.c + ∑ j, β j • Z.G j) 1] :=
      Zonotope.aux_mirrorY_comb Z β
    rw [e]
    exact inv _
  · rintro ⟨β, hβ, h⟩
    refine ⟨β, hβ, ?_⟩
    have e : (Z.mirrorY.c + ∑ j : Fin Z.mirrorY.h, β j • Z.mirrorY.G j)
        = ![(Z.c + ∑ j, β j • Z.G j) 0, -(Z.c + ∑ j, β j • Z.G j) 1] :=
      Zonotope.aux_mirrorY_comb Z β
    rw [e, ← h]
    exact (inv p).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
