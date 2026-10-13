import CORALean.ContSet.ConZonotope.Real.Operations.CubMap
import CORALean.ContSet.Zonotope.Real.Theorems.CubMapCoeff
import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact

/-!
# The cubic map of a constrained zonotope is enclosed by `ConZonotope.cubMap`

The coefficients of `Zonotope.cubMap_coeff` are `βⱼ` on the linear generators `(0, 0, j)`, so the
point's own coefficient vector meets the constraints there, and every other monomial factor is
unconstrained. Outer only, as for the zonotope.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outer only: the monomial factors are free. -/
theorem ConZonotope.cubMap_outer (T : Fin m → Fin n → Mat ℝ n n) (cZ : ConZonotope (Vec ℝ n)) :
    PolyZonotope.cubEval T '' cZ.construct ⊆ (cZ.cubMap T).construct := by -- --- PROOF ---
  rintro _ ⟨x, ⟨p, hp, hP, rfl⟩, rfl⟩
  obtain ⟨γ, hγ, hlin, hx⟩ := Zonotope.cubMap_coeff T (⟨cZ.h, cZ.c, cZ.G⟩ : Zonotope (Vec ℝ n)) p hp
  refine ⟨γ, hγ, ?_, hx⟩
  -- the linear block of the new coefficients is the point's own
  have h1 : ConZonotope.cubLinearAt (cZ.h + 1) (cZ.h + 1) (cZ.h + 1)
      (fun j : Fin cZ.h => ((0, 0), j.succ)) γ = p := funext hlin
  show ConZonotope.cubLinearAt (cZ.h + 1) (cZ.h + 1) (cZ.h + 1)
    (fun j : Fin cZ.h => ((0, 0), j.succ)) γ ∈ cZ.P.construct
  rw [h1]
  exact hP

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
