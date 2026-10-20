module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalTaylorFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat

@[expose] public section

/-!
# `MatExp.expIntervalEnclosure`, over a floating-point scalar

`Real.MatExp.expIntervalEnclosure` rounded: the float Taylor box, `expUp`ended
by the remainder bound taken at `normUpperBound`, exactly as the exact layer
widens by `expRemainderBound` at `A.absMax`. Both are bound once, outside the
entries, so reading every entry evaluates the Taylor sum once, not per entry.

## Inputs
* `A` – float interval matrix
* `η` – Taylor order

## Output
* float interval matrix enclosing the exponential of every member
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.expIntervalEnclosure (A : Interval (Mat 𝕋 n n)) (η : ℕ) : Interval (Mat 𝕋 n n) :=
  let T := MatExp.expIntervalTaylor A η                                -- the Taylor box
  let E := MatExp.expRemainderBound (MatExp.normUpperBound A) η       -- its tail, entrywise
  ⟨fun i j => subDown (T.inf i j) E, fun i j => addUp (T.sup i j) E⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
