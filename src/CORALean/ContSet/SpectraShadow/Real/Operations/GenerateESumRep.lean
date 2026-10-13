module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.SpectraShadow.Real.Definitions.ESumRep

@[expose] public section

/-!
# `SpectraShadow.generateESumRep`

CORA's `generateESumRep(SpS)`: the existential sum representation of the shadow, cached in the
object. CORA writes the point as `x = c + G β`, takes the singular value decomposition of `G` to
eliminate the `rank G` combinations of `β` that `x` determines and keeps the other `n - rank G` as
the existential variables `y` (tolerances `1e-12`, `1e-5`). Here the equality is not eliminated but
written out, as `x - c - G β ⪰ 0` and its negation along the diagonal beside the shadow's
inequality, so the existential variables are all of `β`. It is a different pair `(B, C)` of the same
set (`Theorems.GenerateESumRepExact`); the cache and the SVD are not modelled.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

abbrev SpectraShadow.generateESumRep (S : SpectraShadow (Vec ℝ n)) :
    SpectraShadow.ESumRep n where
  k := S.k + (n + n)
  q := S.m
  B₀ := blockDiag 0 S.A₀ (blockDiag 0 (diagonal (-S.c)) (diagonal (-(-S.c))))
  B := fun i => blockDiag 0 0
    (blockDiag 0 (diagonal (Pi.single i 1)) (diagonal (-(Pi.single i 1 : Vec ℝ n))))
  C := fun j => blockDiag 0 (S.A j)
    (blockDiag 0 (diagonal (-S.G j)) (diagonal (-(-S.G j))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
