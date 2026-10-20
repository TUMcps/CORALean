module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# `PolyZonotope.plus`

CORA's `@polyZonotope/plus`: centers add, and all three generator blocks concatenate. The
exponent matrices do *not*: each set's dependent factors range freely and independently of the
other's, so identifying them would tie the sets together and shrink the sum. `plusE` lays the
two matrices out block-diagonally, so a generator from one set carries exponent zero on every
factor of the other. This is where positional factor identity costs something: CORA's `id`
vector lets `plus` *keep* a shared factor shared; here `plus` always separates, which is sound
and never tighter.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Output
* polynomial zonotope of the Minkowski sum
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.plus (pZ₁ pZ₂ : PolyZonotope α) : PolyZonotope α where
  p := pZ₁.p + pZ₂.p
  h := pZ₁.h + pZ₂.h
  q := pZ₁.q + pZ₂.q
  c := pZ₁.c + pZ₂.c
  G := Fin.append pZ₁.G pZ₂.G
  E := PolyZonotope.plusE pZ₁.E pZ₂.E
  GI := Fin.append pZ₁.GI pZ₂.GI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
