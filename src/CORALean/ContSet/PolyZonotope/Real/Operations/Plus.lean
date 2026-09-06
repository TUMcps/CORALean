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

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def PolyZonotope.plus (PZ₁ PZ₂ : PolyZonotope α) : PolyZonotope α where
  p := PZ₁.p + PZ₂.p
  h := PZ₁.h + PZ₂.h
  q := PZ₁.q + PZ₂.q
  c := PZ₁.c + PZ₂.c
  G := Fin.append PZ₁.G PZ₂.G
  E := PolyZonotope.plusE PZ₁.E PZ₂.E
  GI := Fin.append PZ₁.GI PZ₂.GI

end CORALean.Real
