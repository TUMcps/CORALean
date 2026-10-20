module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo

@[expose] public section

/-!
# `Interval.smul`, over a floating-point scalar

Scaling a float box by a scalar known only to lie in `[cLo, cHi]` — the float
layer has no exact real to scale by, so every use, `expIntervalTaylor`'s
`1/k!` included, hands two bounds rather than one. Entrywise, the same corner
hull `mulLo`/`mulHi` already computes for two interval matrices, with `[cLo,
cHi]` standing in for the second factor at every entry.

At `cLo = cHi` this is a rounded `Real.Interval.smul` at an exact scalar; the extra bound is what
a scalar known only approximately needs otherwise.

## Inputs
* `cLo` – lower end of the scalar
* `cHi` – upper end of the scalar
* `I` – interval matrix

## Output
* interval matrix scaled by the scalar interval `[cLo, cHi]`
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Scaling a box by a scalar bounded within `[cLo, cHi]`, entrywise: the same
corner hull two interval matrices give a product, with `[cLo, cHi]` standing in
for the second factor. -/
def Interval.smul (cLo cHi : 𝕋) (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) where
  inf := fun i j => Interval.mulLo cLo cHi (I.inf i j) (I.sup i j)
  sup := fun i j => Interval.mulHi cLo cHi (I.inf i j) (I.sup i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
