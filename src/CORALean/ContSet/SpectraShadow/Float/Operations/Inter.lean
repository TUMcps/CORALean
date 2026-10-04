import CORALean.ContSet.SpectraShadow.Float.Operations.Plus

/-!
# `SpectraShadow.inter` over a floating-point scalar

CORA's `and_(S₁, S₂, 'exact')` between two shadows of the same space, on the stored floats: the
two inequalities side by side, as in `plus`, over the free variables of both, and the two points
they describe tied together by one more diagonal block. Over ℝ that block forces
`(c₁ + G₁ β₁) - (c₂ + G₂ β₂) = 0`; here a point of each set carries its own error box, so the two
nominal points only differ by a point of `E₂ - E₁`, and the block keeps the difference in that
box instead, `lo + e ⪰ 0` and `hi - e ⪰ 0` entrywise, with `lo`, `hi` rounded outward. The
generators of the difference are `G₁` and `-G₂`, exact since negation is. The point is `S₁`'s,
with its error box; the second's variables carry no generator. Outer, not exact.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.inter (S₁ S₂ : SpectraShadow 𝕋 n) : SpectraShadow 𝕋 n :=
  -- the two inequalities side by side
  let P := S₁.plus S₂
  -- the generators of the difference of the two points, `[G₁, -G₂]`, column by column
  let g : Fin (S₁.m + S₂.m) → Vec 𝕋 n := fun i r =>
    Fin.append (S₁.G r) (fun j => neg (S₂.G r j)) i
  -- `c₁ - c₂` against the most the error boxes let the points differ by, rounded outward
  let lo : Vec 𝕋 n := fun r => addUp (subUp (S₁.c r) (S₂.c r)) (subUp (S₁.E.sup r) (S₂.E.inf r))
  let hi : Vec 𝕋 n := fun r => addUp (subUp (S₂.c r) (S₁.c r)) (subUp (S₂.E.sup r) (S₁.E.inf r))
  { k := P.k + (n + n)
    m := P.m
    A₀ := blockDiag zero P.A₀ (blockDiag zero (diagonalBlock lo) (diagonalBlock hi))
    A := fun i => blockDiag zero (P.A i)
      (blockDiag zero (diagonalBlock (g i)) (diagonalBlock fun r => neg (g i r)))
    c := S₁.c
    G := fun r => Fin.append (S₁.G r) fun _ => zero
    E := S₁.E }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
