module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Real.Operations.Plus

@[expose] public section

/-!
# `SpectraShadow.inter`

CORA's `and_(S₁, S₂, 'exact')`, between two shadows of the same space: the two inequalities side by
side, as in `plus`, over the free variables of both, and the two points they describe forced
equal. Equality is not an inequality, so it is two: `e ⪰ 0` and `-e ⪰ 0` for every entry of
`e = (c₁ + G₁ β₁) - (c₂ + G₂ β₂)`, one more diagonal block, `diag e ⊕ diag (-e)`. The point is
`S₁`'s; the second's variables carry no generator.

Over `Vec ℝ n`: the equality is stated per coordinate.

## Inputs
* `S₁` – spectrahedral shadow
* `S₂` – spectrahedral shadow

## Output
* the intersection: both inequalities side by side and the two points forced equal
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.inter (S₁ S₂ : SpectraShadow (Vec ℝ n)) : SpectraShadow (Vec ℝ n) where
  k := (S₁.k + S₂.k) + (n + n)
  m := S₁.m + S₂.m
  A₀ := blockDiag 0 (S₁.plus S₂).A₀
    (blockDiag 0 (diagonal (S₁.c - S₂.c)) (diagonal (-(S₁.c - S₂.c))))
  A := fun i => blockDiag 0 ((S₁.plus S₂).A i)
    (blockDiag 0 (diagonal ((Fin.append S₁.G (fun j => - S₂.G j) : Fin (S₁.m + S₂.m) → Vec ℝ n) i))
      (diagonal (-(Fin.append S₁.G (fun j => - S₂.G j) : Fin (S₁.m + S₂.m) → Vec ℝ n) i)))
  c := S₁.c
  G := Fin.append S₁.G 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
