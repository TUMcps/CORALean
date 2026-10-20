module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPolyStep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MulPoint

@[expose] public section

/-!
# `evalPolyStep`'s point, generically

Split out of `EvalPolyExact.lean` (issue #62): read again by the float layer's
own `Theorems/EvalPolyOuter.lean`, outside this file.

## Inputs
* `R` – running Horner result
* `pZ` – polynomial zonotope
* `a0` – next coefficient vector
* `b` – factor values

## Hypotheses
* `hR` – both have the same factor count

## Conclusion
* the point is the coefficient plus the running point times the set's point
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `evalPolyStep`'s point, generically: a coordinate `a₀ + R ⊙ pZ`, `R` read at
`pZ`'s factors through `hR`. -/
theorem PolyZonotope.evalPolyStep_point (R pZ : PolyZonotope (Vec ℝ n)) (hR : R.p = pZ.p)
    (a0 : Vec ℝ n) (b : Fin R.p → ℝ) : -- --- CONCL ---
    (PolyZonotope.evalPolyStep R pZ hR a0).point b
      = fun i => a0 i
        + R.point b i * pZ.point (fun k => b (Fin.cast hR.symm k)) i := by -- --- PROOF ---
  have hpt : (PolyZonotope.evalPolyStep R pZ hR a0).point b
      = (PolyZonotope.mul R pZ hR).c + a0
        + ∑ l, PolyZonotope.monomial (PolyZonotope.mul R pZ hR).E b l
            • (PolyZonotope.mul R pZ hR).G l := rfl
  have hmul : (PolyZonotope.mul R pZ hR).c
        + ∑ l, PolyZonotope.monomial (PolyZonotope.mul R pZ hR).E b l
            • (PolyZonotope.mul R pZ hR).G l
      = (PolyZonotope.mul R pZ hR).point b := rfl
  rw [hpt, add_right_comm, hmul, PolyZonotope.mul_point R pZ hR b]
  funext i
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
