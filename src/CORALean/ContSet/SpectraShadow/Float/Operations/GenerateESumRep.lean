module

public import CORALean.ContSet.SpectraShadow.Float.Definitions.ESumRep
public import CORALean.Global.Float.GenBlockDiag

@[expose] public section

/-!
# `SpectraShadow.generateESumRep`, over a floating-point scalar

CORA's `generateESumRep(SpS)` as the exact layer writes it: the equality `x = c + G β` is not
eliminated but written out, as `x - c - G β ⪰ 0` and its negation along the diagonal beside the
shadow's inequality, the existential variables being all of `β`. Only blocks are rearranged and
entries negated, which is exact, so nothing rounds. The stored shadow's error box is not part of an
existential sum representation and is not read.

## Inputs
* `S` – spectrahedral shadow

## Output
* the existential sum representation, with `x = c + G β` written out beside the inequality
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps CORALean

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.generateESumRep (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow.ESumRep 𝕋 n where
  k := S.k + (n + n)
  q := S.m
  B₀ := blockDiag zero S.A₀ (blockDiag zero (diagonalBlock (-S.c))
    (diagonalBlock (-(-S.c))))
  B := fun i => blockDiag zero (fun _ _ => zero)
    (blockDiag zero (diagonalBlock fun r => if r = i then one else zero)
      (diagonalBlock (-(fun r => if r = i then one else zero))))
  C := fun j => blockDiag zero (S.A j)
    (blockDiag zero (diagonalBlock (-(S.G j)))
      (diagonalBlock (-(-(S.G j)))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
