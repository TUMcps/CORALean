module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MatPow
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.expIntervalTaylor`, over a floating-point scalar

`Real.MatExp.expIntervalTaylor` rounded: `i = 0 … η` matching that recursion term by term, each
term `Interval.smul` at `invFactorialBounds i`, the float layer's only handle on `1/i!`. Each
partial sum is `materialiseMat`d before the next term is added to it, for the reason
`Interval.matPow`'s own recursion is: left as a closure, `η` nested `matPlus`es would rebuild
the whole sum on every entry read. What runs carries the power along instead of rebuilding `Aⁱ`
at every order, by `@[csimp]`: the same products in the same order, so the same values.

## Inputs
* `A` – float interval matrix

## Output
* float interval matrix of the Taylor truncation up to the given order
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The power and the partial sum at order `k`, the power carried from one order
to the next by `matPow`'s own step. -/
@[step_of MatExp.expIntervalTaylor]
def MatExp.step_expIntervalTaylorPair (A : Interval (Mat 𝕋 n n)) :
    ℕ → Interval (Mat 𝕋 n n) × Interval (Mat 𝕋 n n)
  | 0 => (Interval.matPow A 0, Interval.smul (MatExp.invFactorialBounds 0).inf
      (MatExp.invFactorialBounds 0).sup (Interval.matPow A 0))
  | k + 1 =>
    let PS := MatExp.step_expIntervalTaylorPair A k
    let P := (Interval.matMul A PS.1).materialiseMat
    (P, (Interval.matPlus (Interval.smul (MatExp.invFactorialBounds (k + 1)).inf
      (MatExp.invFactorialBounds (k + 1)).sup P) PS.2).materialiseMat)

/-- The same sum, `η` products rather than `η²/2`. -/
@[step_of MatExp.expIntervalTaylor]
def MatExp.step_expIntervalTaylorImpl (A : Interval (Mat 𝕋 n n)) (k : ℕ) : Interval (Mat 𝕋 n n) :=
  (MatExp.step_expIntervalTaylorPair A k).2


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.expIntervalTaylor (A : Interval (Mat 𝕋 n n)) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.smul (MatExp.invFactorialBounds 0).inf (MatExp.invFactorialBounds 0).sup
      (Interval.matPow A 0)
  | k + 1 => (Interval.matPlus
      (Interval.smul (MatExp.invFactorialBounds (k + 1)).inf (MatExp.invFactorialBounds (k + 1)).sup
        (Interval.matPow A (k + 1)))
      (MatExp.expIntervalTaylor A k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
