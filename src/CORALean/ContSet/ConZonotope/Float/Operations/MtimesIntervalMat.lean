module

public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.ConZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
public import CORALean.ContSet.Interval.Float.Operations.CentreMat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat

@[expose] public section

/-!
# `ConZonotope.mtimesIntervalMat`, over a floating-point scalar

`Zonotope.mtimesIntervalMat` with the constraints carried along: the centre matrix
`Interval.centreMat` acts through `ConZonotope.mtimes`, and what any member of `M` does beyond
it, a matrix known only to within `Interval.matResidual`, is `|M - mid(M)| (|c| + Σ|G|)` per
coordinate on the nominal part, rounded up and kept as `m` new diagonal generators; the
constraints are padded on the right, so the new coefficients answer to nothing, as over `ℝ`.
The error box takes `mid(M) E` and the box-times-box product `(M - mid(M)) E`.

The bound only has to hold: the constraints could tighten it, and are not used to.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `mid(M) cZ`, plus `m` generators for what the radius does to the nominal part and a box for
what it does to the error box. -/
def ConZonotope.mtimesIntervalMat (IM : Interval (Mat 𝕋 m n)) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    ConZonotope 𝕋 (Vec 𝕋 m) :=
  let C := Interval.centreMat IM                                    -- mid(M), stored
  let Rs := Interval.matResidual IM.inf IM.sup C                    -- M - mid(M), a box
  let MZ := ConZonotope.mtimes C cZ                                 -- mid(M) cZ
  let b : Vec 𝕋 m := fun i => sumUp fun j =>                        -- |M - mid(M)| (|c| + Σ|G|)
    mulUp (maximum (absolute (Rs.inf i j)) (absolute (Rs.sup i j)))
      (addUp (absolute (cZ.c j)) (radius (fun i j => cZ.G j i) j))
  { h := cZ.h + m
    c := MZ.c
    G := Fin.append MZ.G (diagonalBlock b)                          -- mid(M) G, then diag(b)
    P := MZ.P.padLeft m                                             -- new coefficients are free
    -- mid(M) E ⊕ (M - mid(M)) E
    I_error := MZ.I_error.plus (Interval.mtimesIntervalMat Rs cZ.I_error) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
