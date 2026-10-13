module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.SpectraShadow.Real.Operations.ArrowMat

@[expose] public section

/-!
# `SpectraShadow.cone`

The conic hull `aux_conicHull` of `@spectraShadow/convHull_.m`, of a shadow of `ℝ^N`: the points `s
x` for `s > 0` and `x` in the shadow, and the origin. Its free variables are the homogenised ones,
`s`, `β' = s β` and an auxiliary `t`: the inequality `s A₀ + Σ β'ⱼ Aⱼ ⪰ 0` is the shadow's scaled by
`s`, and the arrowhead block `arrowMat s t z ⪰ 0` for the point `z = s c + Σ β'ⱼ Gⱼ` says `s ≥ 0`,
and `z = 0` when `s = 0`. That keeps the cone from adding the shadow's recession directions at `s =
0`, which would make the closure. CORA writes the shadow's point as its own free coordinates first,
through the SVD of `G` (`generateESumRep`); here the point is `s c + G β'` as it is stored.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix CORALean

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.cone (T : SpectraShadow (Vec ℝ N)) : SpectraShadow (Vec ℝ N) where
  k := T.k + (N + 1)
  m := 1 + T.m + 1
  A₀ := 0
  A := Fin.append
    (Fin.append (fun _ => blockDiag 0 T.A₀ (arrowMat 1 0 T.c))
      (fun j => blockDiag 0 (T.A j) (arrowMat 0 0 (T.G j))))
    (fun _ => blockDiag 0 0 (arrowMat 0 1 0))
  c := 0
  G := Fin.append (Fin.append (fun _ => T.c) T.G) (fun _ => 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
