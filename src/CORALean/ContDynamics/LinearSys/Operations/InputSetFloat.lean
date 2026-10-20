module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# The input set in state coordinates, in floats

The state part of CORA's `canonicalForm` [1] at float zonotopes, as the float reaches with
inputs read it: `B U ⊕ c`, with `B` and `c` the system's and `U` in input coordinates. CORA's
`canonicalForm` also adds `B uTrans` and `E W`; the reaches here take neither (`uTrans = 0`, and
`W = {0}`, CORA's default `params.W`), so `B U ⊕ c` is the whole input. `c` enters as a point
without generators, so the order of `B U` is kept. Soundness is `inputSetFloat_outer`.

## Inputs
* `sys` – linear system
* `U` – input float zonotope

## Output
* float zonotope of the input in state coordinates

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B U ⊕ c`, the input set the reach runs on, in the state space. -/
def LinearSys.inputSetFloat (sys : LinearSys 𝕋 n) (U : Zonotope (Vec 𝕋 sys.m)) :
    Zonotope (Vec 𝕋 n) :=
  Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) sys.B U ⊞ Zonotope.point sys.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
