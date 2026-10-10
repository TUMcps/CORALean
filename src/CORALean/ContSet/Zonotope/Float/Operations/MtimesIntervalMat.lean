import CORALean.ContSet.Interval.Float.Operations.CentreMat
import CORALean.ContSet.Interval.Float.Operations.MatResidual
import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes

/-!
# `Zonotope.mtimesIntervalMat`, over a floating-point scalar

CORA's `mtimes` at an interval matrix, `mid(M) Z ⊕ box(rad(M) |Z|)`, rounded.
`Zonotope.mtimes` handles the centre matrix `Interval.centreMat`, paying its
rounding into the box as it does for a plain matrix. What any member of `M`
does beyond it is a matrix known only to within `Interval.matResidual`: on the
nominal part `c + G β` that is at most `|M - mid(M)| (|c| + Σ|G|)` per
coordinate, rounded up and kept as `m` new diagonal generators, as CORA keeps
it; on the error box it is a box-times-box product, `Interval.mtimesIntervalMat`,
and joins `mid(M) E` in the box. So the box carries rounding and nothing of the
interval matrix's width — a long product chain wraps only what rounding cost.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   25-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `mid(M) Z`, plus `m` generators for what the radius does to the nominal part
and a box for what it does to the error box. -/
def Zonotope.mtimesIntervalMat (IM : Interval (Mat 𝕋 m n)) (Z : Zonotope 𝕋 n) : Zonotope 𝕋 m :=
  let C := Interval.centreMat IM                                    -- mid(M), stored
  let Rs := Interval.matResidual IM.inf IM.sup C                    -- M - mid(M), a box
  let MZ := Zonotope.mtimes C Z                                     -- mid(M) Z
  let b : Vec 𝕋 m := fun i => sumUp fun j =>                        -- |M - mid(M)| (|c| + Σ|G|)
    mulUp (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
      (addUp (absolute (Z.c j)) (radius (fun i j => Z.G j i) j))
  { h := Z.h + m
    c := MZ.c
    G := Fin.append MZ.G (diagonalBlock b)                          -- mid(M) G, then diag(b)
    E := MZ.E.plus (Interval.mtimesIntervalMat Rs Z.E) }            -- mid(M) E ⊕ (M - mid(M)) E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
