import CORALean.Global.Float.BilinUp
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.NormMag
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# The cubic remainder of a second-order expansion, in floats

`lagrangeRemainder` in `𝕋`: CORA's `priv_lagrangeRemainder`, [1, Sec. 4.1], the box `[-l, l]` with
`lᵢ = (1/6) Σⱼ γⱼ (γᵀ Eᵢⱼ γ)`, `γ` bounding `|z - z✱|` over the zonotope and `Eᵢⱼ` bounding the
third derivative of coordinate `i`, once more in the direction `j`, entrywise. `γ` is read off the
box of the zonotope, the magnitudes of `Eᵢⱼ` and the sums are rounded up, and the sixth is the
dyadic `11/64`, an upper bound on `1/6` that `FloatOps` can form without a division.

`E` is data here as in the exact layer: `FloatHessModel` carries Hessians and no third derivative,
so `linReachFloat` does not call this; it stands for a model that does.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The symmetric box `[-l, l]` bounding a third-order remainder over `Z`, at the expansion point
`zs` and the entrywise third-derivative bound `E`. -/
def lagrangeRemainderFloat {d n : ℕ} (E : Fin n → Fin d → Mat 𝕋 d d) (Z : Zonotope (Vec 𝕋 d))
    (zs : Vec 𝕋 d) : Interval (Vec 𝕋 n) :=
  let Z' := Z.interval                                              -- Z's box
  let γ : Vec 𝕋 d := (Interval.plus Z' (Interval.point fun j => neg (zs j))).normMag  -- |z - z✱|
  let Eabs := fun i j (k l : Fin d) => absolute (E i j k l)         -- |Eᵢⱼ|
  let eighth := half (half (half one))                              -- 1/8
  let sixth := addUp eighth (addUp (half (half eighth)) (half (half (half eighth))))  -- 11/64
  let l : Vec 𝕋 n := fun i =>                                       -- (1/6) Σⱼ γⱼ (γᵀ Eᵢⱼ γ)
    mulUp (sumUp fun j => mulUp (γ j) (bilinUp γ (Eabs i j) γ)) sixth
  ⟨fun i => neg (l i), l⟩                                           -- [-l, l]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
