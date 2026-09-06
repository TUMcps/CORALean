import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyStep
import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint

/-!
# `evalPolyStep`'s point, generically

Split out of `EvalPolyExact.lean` (issue #62): read again by the float layer's
own `Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `evalPolyStep`'s point, generically: a coordinate `a₀ + R ⊙ S`, `R` read at
`S`'s factors through `hR`. -/
theorem PolyZonotope.evalPolyStep_point (R S : PolyZonotope (Vec ℝ n)) (hR : R.p = S.p)
    (a0 : Vec ℝ n) (b : Fin R.p → ℝ) :
    (PolyZonotope.evalPolyStep R S hR a0).point b
      = fun i => a0 i
        + R.point b i * S.point (fun k => b (Fin.cast hR.symm k)) i := by -- --- PROOF ---
  have hpt : (PolyZonotope.evalPolyStep R S hR a0).point b
      = (PolyZonotope.mul R S hR).c + a0
        + ∑ l, PolyZonotope.monomial (PolyZonotope.mul R S hR).E b l
            • (PolyZonotope.mul R S hR).G l := rfl
  have hmul : (PolyZonotope.mul R S hR).c
        + ∑ l, PolyZonotope.monomial (PolyZonotope.mul R S hR).E b l
            • (PolyZonotope.mul R S hR).G l
      = (PolyZonotope.mul R S hR).point b := rfl
  rw [hpt, add_right_comm, hmul, PolyZonotope.mul_point R S hR b]
  funext i
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
