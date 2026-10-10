import CORALean.ContSet.Zonotope.Float.Operations.EncloseManyBasisInv
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.Global.Float.Sqrt

/-!
# `Zonotope.encloseMany`, over a floating-point scalar

CORA's `@zonotope/encloseMany(Z, direction)` [1]: one oriented box around a list of zonotopes.
Each cell is reduced to a parallelotope (`reduceGirard 1`, standing in for the `'parallelpiped'`
method CORA names and does not have), taken to the frame `R` whose first axis is
`direction / ‖direction‖₂`, boxed there by the componentwise hull of the cells' interval
enclosures, and rotated back.

`R⁻¹` is not formed: `encloseManyBasisInv` holds it in a box, and the cells are mapped by
`mtimesIntervalMat`, which encloses the image under every matrix of the box. The unit vector is
rounded, which is harmless: any vector with a nonzero entry at the dropped axis gives an invertible
`R`, and the enclosure holds for that `R`. `none` where `ltStrict` cannot show that entry nonzero
(a zero direction, where CORA errors as well). At least one cell is required, as in CORA.

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `encloseMany(Z, direction)`: the oriented box, in the frame whose first axis is
`direction`, around the parallelotope reductions of the cells `Zs`; `p` Newton steps of the
norm. -/
def Zonotope.encloseMany (p : ℕ) (Zs : Fin (q + 1) → Zonotope 𝕋 (m + 1))
    (direction : Vec 𝕋 (m + 1)) : Option (Zonotope 𝕋 (m + 1)) :=
  let newGen : Vec 𝕋 (m + 1) := fun i => divDown (direction i) (normUp p direction)
  let dropped := Zonotope.encloseManyDropped newGen
  if ltStrict zero (newGen dropped) || ltStrict (newGen dropped) zero then
    let rotMatrix := Zonotope.encloseManyBasis newGen                    -- [newGen, picked axes]
    let rotMatrixInv := Zonotope.encloseManyBasisInv newGen               -- inv(rotMatrix), boxed
    let Zred := fun i => (Zs i).reduceGirard 1                          -- the parallelotope of Z{i}
    let rotated := fun i => (Zonotope.mtimesIntervalMat rotMatrixInv (Zred i)).interval
    let I : Interval (Vec 𝕋 (m + 1)) :=                                    -- interval.enclosePoints
      ⟨fun k => minimumOver fun i => (rotated i).inf k,
       fun k => maximumOver fun i => (rotated i).sup k⟩
    some (Zonotope.mtimes rotMatrix I.zonotope)                           -- rotMatrix * zonotope(I)
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
