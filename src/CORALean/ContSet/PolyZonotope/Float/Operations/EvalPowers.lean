module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.ErrorBound
public import CORALean.ContSet.PolyZonotope.Real.Definitions.PowerOps
public import CORALean.Global.Float.MidRad
public import CORALean.Global.StepOf
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.EvalPowersList
public import CORALean.ContSet.PolyZonotope.Real.Operations.PowerOut

@[expose] public section

/-!
# `PolyZonotope.evalPowers`

CORA's `evaluatePolyZonotopeNeuron` after the fit: the polynomial of every neuron on its row by
the powers of the row (`Real.PolyZonotope.evalPowersList`), all neurons at once in midpoint-radius
floats (`PolyZonotope.step_midRadOps`). The stored generators are the midpoints, CORA.cpp's
`priv_eval_poly` bit for bit at the dtype `nearest`, and the error box the radii summed. The input
box enters as the radius of the center. The exponents are CORA's `[E, E^2, …, E^k]`
(`Real.PolyZonotope.powerOut`), no column merged: `compact` does that. Unlike `evalPoly` (Horner's
rule), the independent generators stay independent, their products new independent generators.

## Inputs
* `pZ` – polynomial zonotope
* `coeffs` – coefficient vectors, one entry per neuron, lowest degree first

## Output
* polynomial zonotope of the polynomials on the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Column vectors of midpoint-radius floats, entry by entry: the values are CORA's doubles (at
`nearest`), the radii bound their distance from the exact powers; `2 = 1 + 1`, `1/2 = half 1`. -/
@[step_of PolyZonotope.evalPowers]
def PolyZonotope.step_midRadOps : Real.PowerOps (Vec (MidRad 𝕋) n) where
  add a b i := (a i).add (b i)
  mul a b i := (a i).mul (b i)
  zero _ := MidRad.exact zero
  two _ := (MidRad.exact one).add (MidRad.exact one)
  half _ := MidRad.exact (half one)


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.evalPowers (pZ : PolyZonotope (Vec 𝕋 n)) (coeffs : List (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 n) :=
  -- 1. the rows as midpoint-radius columns, the input box the radius of the center
  let x : Real.PowerRow (Vec (MidRad 𝕋) n) :=
    ⟨fun i => ⟨pZ.c i, PolyZonotope.errorBound pZ.I_error i⟩,
      List.ofFn fun l i => MidRad.exact (pZ.G l i), List.ofFn fun j i => MidRad.exact (pZ.GI j i)⟩
  -- 2. the powers, weighted and folded
  let run := Real.PolyZonotope.evalPowersList PolyZonotope.step_midRadOps
    (coeffs.map fun v i => MidRad.exact (v i)) x
  -- 3. the exponents of the powers
  let E := Real.PolyZonotope.powerOut (· + ·) (List.ofFn fun l k => pZ.E k l)
    (max 1 (coeffs.length - 1))
  -- 4. the midpoints stored, the radii summed into the box
  { p := pZ.p
    h := run.G.length
    q := run.GI.length
    c := fun i => (run.c i).v
    G := fun l i => (run.G.get l i).v
    E := fun k l => E.getD l 0 k
    GI := fun j i => (run.GI.get j i).v
    I_error := Interval.symmetric fun i => addUp (run.c i).r
      (addUp (sumUp fun l => (run.G.get l i).r) (sumUp fun j => (run.GI.get j i).r)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
