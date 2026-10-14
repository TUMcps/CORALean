module

public import CORALean.ContSet.Zonotope.Float.Operations.Plus
public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.ExactPlusGap

@[expose] public section

/-!
# `Zonotope.exactPlus`, over a floating-point scalar

CORA's `@zonotope/exactPlus`: the first `m = min(h₁, h₂, k)` generator columns of the two operands
share their coefficients and are added pairwise, the remaining columns of each follow, and the
centres add. Only the added entries round: the centre as in `plus` (its residual goes into the
box), and each pairwise column sum, stored rounded down, whose gap to the sum rounded up
(`exactPlusGap`) is a generator error, paid into the box by `generatorError` since the
coefficients range over `[-1, 1]`. A copied column costs nothing.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.exactPlus (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  let m := min (min Z₁.h Z₂.h) k
  have hm₁ : m ≤ Z₁.h := (min_le_left _ _).trans (min_le_left _ _)
  have hm₂ : m ≤ Z₂.h := (min_le_left _ _).trans (min_le_right _ _)
  -- the shared columns, added pairwise and rounded down
  let shared : Mat 𝕋 n m := fun i j =>
    addDown (Z₁.G (Fin.castLE hm₁ j) i) (Z₂.G (Fin.castLE hm₂ j) i)
  -- the rest of each operand's columns, copied
  let rest₁ : Mat 𝕋 n (Z₁.h - m) := fun i j => Z₁.G ⟨m + j, by have := j.2; omega⟩ i
  let rest₂ : Mat 𝕋 n (Z₂.h - m) := fun i j => Z₂.G ⟨m + j, by have := j.2; omega⟩ i
  { h := m + (Z₁.h - m) + (Z₂.h - m)
    c := fun i => addDown (Z₁.c i) (Z₂.c i)
    G := fun j i => Fin.append (Fin.append (shared i) (rest₁ i)) (rest₂ i) j
    I_error := ((Z₁.I_error.plus Z₂.I_error).plus (Zonotope.centerResidual Z₁.c Z₂.c)).plus
      (Zonotope.generatorError (Z₁.exactPlusGap Z₂ k)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
