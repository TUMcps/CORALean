module

public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.RowLin
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# `HPolytope.ofBounds`, over a floating-point scalar

The same shape as the exact layer's: rows the caller names, right-hand sides
that certificates supply. What changes is that a right-hand side is now a float,
which is why the certificates are `FloatBound`s.

No equality rows, so `be` stays empty, and the error box is the origin. An enclosure has no
equalities to state: it is slack by construction.

## Inputs
* `Aq` – `q × n` matrix

## Hypotheses
* `u` – a float bound of `S` along each row

## Output
* the polytope with rows `Aq` and right-hand sides the certified bounds `u`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ} {S : Set (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S (rowLin Aq i)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ineqs Aq fun i => (u i).val

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
