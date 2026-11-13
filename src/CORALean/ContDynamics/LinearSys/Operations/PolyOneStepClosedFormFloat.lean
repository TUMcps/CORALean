module

public import CORALean.ContDynamics.LinearSys.Operations.ClosedFormMatricesFloat
public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedFormFloat
public import CORALean.ContSet.PolyZonotope.Float.Operations.Construct
public import CORALean.ContSet.PolyZonotope.Float.Operations.EncloseShared
public import CORALean.ContSet.PolyZonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Float.Operations.OfZonotope
public import CORALean.ContSet.PolyZonotope.Float.Instances

@[expose] public section

/-!
# One step of a linear system from a polynomial zonotope, in closed form, in floats

`LinearSys.oneStepClosedFormFloat` from a polynomial zonotope, in CORA's order for `linReach`:
`[e^{AΔt}] X` is the exact map on the factors (an interval matrix times the dependent part, its
width as independent generators), the enclosure of `X` and `[e^{AΔt}] X ⊕ Pu` is CORA's `enclose`
(the factors kept, the constructor run again), and `[F] X` and the input solutions, all
zonotopes, are added as independent generators. The matrices are `closedFormMatricesFloat`'s.
`polyOneStepClosedFormFloat_timePoint_outer` and `_timeInterval_outer` show they enclose.

## Inputs
* `sys` – linear system
* `M` – the matrices of the step
* `X` – start polynomial zonotope
* `U` – input zonotope
* `u` – float constant input
* `Δt` – float step length
* `order` – the order of equal exponent columns (CORA's hash order)

## Output
* float time-point and time-interval sets of the step
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `oneStep` in closed form from a polynomial zonotope, in floats. -/
def LinearSys.polyOneStepClosedFormFloat (sys : LinearSys 𝕋 n)
    (M : LinearSys.ClosedFormMatrices 𝕋 n) (X : PolyZonotope (Vec 𝕋 n))
    (U : Zonotope (Vec 𝕋 n)) (u : Vec 𝕋 n) (Δt : 𝕋) (order : ℕ → Array (Array ℕ) → Array ℕ) :
    LinearSys.StepSets (PolyZonotope (Vec 𝕋 n)) :=
  let PU := (sys.inputSolutionEntrywiseFloat Δt M.ηe M.W U).materialise.ofIndep  -- time-varying
  let Pu := (sys.inputSolutionEntrywiseFloat Δt M.ηe M.W (Zonotope.point u)).materialise.ofIndep
  let C_input := (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (ContSet := 𝒵[𝕋]) M.G  -- `[G] u`
    (Zonotope.point u)).materialise.ofIndep
  let Htp := PolyZonotope.mtimesIntervalMat M.eAdt X ⊞ Pu                 -- `[e^{AΔt}] X ⊕ Pu`
  let C_state := PolyZonotope.mtimesIntervalMat M.F X                     -- `[F] X`
  let Hti := ((X.encloseShared Htp rfl).construct order).materialise ⊞    -- `CH(X, Htp)`
    C_state                                                               -- `⊕ C_state`
  ⟨Htp ⊞ PU, (Hti ⊞ PU) ⊞ C_input⟩                                       -- `Rtp`, `Rti`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
