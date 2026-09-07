import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepPoint

/-!
# `precompStatError`'s point is the second-order term at that point

The whole content of step one: at the factor vector `a`, the set
`precompStatError` computes takes the value the Taylor expansion's second-order
term takes at the state `a` names. Not an enclosure of the term over a set — the
term itself, as a function of the factors, which is what makes the abstraction
error dependency-preserving.

`quadMapDep_point` does the work; all this adds is the shift by the linearization
point, which moves the centre and leaves every monomial alone.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The value at `a` is the second-order term at the state `a` names. -/
theorem precompStatError_point (Q : Fin n → Mat ℝ n n) (xs : Vec ℝ n)
    (pZ : PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ) :
    (precompStatError Q xs pZ).point a = quadEval Q (pZ.point a - xs) := by -- --- PROOF ---
  -- the shifted set has `pZ`'s monomials and generators, so only the centre moves
  have hshift : ({ pZ with c := pZ.c - xs } : PolyZonotope (Vec ℝ n)).point a
      = pZ.point a - xs := by
    show pZ.c - xs + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
        = pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i - xs
    abel
  have h := PolyZonotope.quadMapDep_point Q ({ pZ with c := pZ.c - xs } : PolyZonotope _) a
  rw [hshift] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
