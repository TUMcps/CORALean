import CORALean.ContSet.SpectraShadow.Float.Operations.DualBound
import CORALean.ContSet.SpectraShadow.Float.Operations.DualCertified
import CORALean.ContSet.HPolytope.Float.Operations.Ineqs

/-!
# `SpectraShadow.polytopeOuter`, over a floating-point scalar

CORA's `polytope(SpS, 'outer', splits)`: the rows `dirᵀ x ≤ val` along a grid of directions `dirs`.
`val` is the support value of the semidefinite program CORA's `supportFunc_` solves; here it is
the rounded-up `dualBound` along `dirs i` of a dual certificate `Y i` the caller supplies, and a
row is kept only if `dualCertified` accepts the certificate (CORA keeps the rows with a finite
support value). CORA shifts the shadow by its `center` first and shifts the polytope back, which
leaves the rows as they are: the shift is not needed here. A direction with no certificate is
skipped.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.polytopeOuter (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (dirs : Fin N → Vec 𝕋 n)
    (Y : (i : Fin N) → Mat 𝕋 S.k S.k) : HPolytope 𝕋 (Vec 𝕋 n) :=
  let finite : List (Fin N) := (List.finRange N).filter fun i => S.dualCertified (dirs i) (Y i)
  let P_A : Mat 𝕋 finite.length n := fun r j => dirs (finite.get r) j
  let P_b : Vec 𝕋 finite.length := fun r =>
    S.dualBound (dirs (finite.get r)) (Y (finite.get r))
  HPolytope.ineqs P_A P_b

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
