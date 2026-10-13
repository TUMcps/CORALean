import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

/-!
# `PolyZonotope.plus`

CORA's `@polyZonotope/plus`: centres add, and all three generator blocks
concatenate.

The exponent matrices do *not*. Each set's dependent factors range freely and
independently of the other's, so identifying them would tie the two sets
together and shrink the sum. `plusE` therefore lays the two matrices out
block-diagonally: the combined set has `p₁ + p₂` factors, and a generator that
came from one set carries exponent zero on every factor of the other, which
reads its monomial back as a monomial of its own set alone.

This is where positional factor identity costs something. CORA's `id` vector
lets `plus` *keep* a shared factor shared when the two sets are known to have
one; here `plus` always separates, which is sound and never tighter.
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
