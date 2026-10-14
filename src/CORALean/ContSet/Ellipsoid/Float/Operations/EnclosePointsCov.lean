module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Ellipsoid.enclosePointsCov`, over a floating-point scalar

CORA's `@ellipsoid/enclosePoints.m`, method `'cov'`, the real layer's
`Real.Ellipsoid.enclosePointsCov` step for step: the mean `c`, the points rotated by the caller's
`T` and `U` (CORA: `svd(points)` and `svd(cov(.))`), the scalings `nt`, the radius `maxDist`, and
the generators `T U diag(nt · sqrt maxDist)`. None of it is trusted. The real layer's proof needs
`T` and `U` orthogonal and every step exact; a float rotation is neither, and an inverse or an
eigen-decomposition would have to be certified. Instead every point is placed explicitly: its
factor vector `u` is the rotated point divided by the scalings, shrunk by `1 - 2⁻³⁰` against
rounding and kept only if its upward square sum is at most `1` (else `0`), and the remainder
`p - c - G u`, bracketed by directed roundings as in `containsPoint`, goes into the error box,
which is the hull of all remainders. Every point is then in the set whatever the rotations, the
rounding or the Newton steps `steps` of the square root did; they decide only how small the box
is. For points spanning the space with orthogonal `T`, `U` and no vanishing `ntᵢ` the remainders
are rounding errors.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `enclosePoints(points, 'cov')`, given `T` and `U`; `steps` Newton steps for `sqrt maxDist`. -/
def Ellipsoid.enclosePointsCov (steps : ℕ) (pts : Fin N → Vec 𝕋 n) (T U : Mat 𝕋 n n) :
    Ellipsoid 𝕋 n :=
  -- `c = mean(points, 2)`
  let cV : Vector 𝕋 n := Vector.ofFn fun i => divDown (sumDown fun j => pts j i) (nsmulDown N one)
  let c : Vec 𝕋 n := fun i => cV[i.val]'i.isLt
  -- `orientedMatrix = U' * (T' * (points - c))`, one row per point
  let OV : Vector (Vector 𝕋 n) N := Vector.ofFn fun j =>
    let points : Vec 𝕋 n := fun l => subDown (pts j l) (c l)
    let pointsTV : Vector 𝕋 n := Vector.ofFn fun i => dotDown (fun l => T l i) points
    Vector.ofFn fun i => dotDown (fun l => U l i) fun l => pointsTV[l.val]'l.isLt
  let orientedMatrix : Fin N → Vec 𝕋 n := fun j i => (OV[j.val]'j.isLt)[i.val]'i.isLt
  -- `nt = max([m1, m2], [], 2)`
  let ntV : Vector 𝕋 n := Vector.ofFn fun i =>
    maximum (maximumOver fun j => orientedMatrix j i) (minimumOver fun j => orientedMatrix j i)
  let nt : Vec 𝕋 n := fun i => ntV[i.val]'i.isLt
  -- `maxDist = max_j Σᵢ (orientedMatrix(i,j) / ntᵢ)²`
  let maxDist : 𝕋 := maximumOver fun j =>
    sqSumUp fun i => absolute (divUp (orientedMatrix j i) (nt i))
  -- `diag(nt · sqrt maxDist)` and the generators `T U diag(nt · sqrt maxDist)`
  let r : 𝕋 := sqrtUp steps maxDist
  let D : Vec 𝕋 n := fun i => mulUp (nt i) r
  let TUV : Vector (Vector 𝕋 n) n :=
    Vector.ofFn fun l => Vector.ofFn fun i => dotDown (T l) fun m => U m i
  let GV : Vector (Vector 𝕋 n) n := Vector.ofFn fun l => Vector.ofFn fun i =>
    mulDown ((TUV[l.val]'l.isLt)[i.val]'i.isLt) (D i)
  let G : Mat 𝕋 n n := fun l i => (GV[l.val]'l.isLt)[i.val]'i.isLt
  -- each point's factor vector, shrunk against rounding and kept only at certified length `≤ 1`
  let shrink : 𝕋 := subDown one (half^[30] one)
  let uV : Vector (Vector 𝕋 n) N := Vector.ofFn fun j =>
    let u₀ : Vector 𝕋 n := Vector.ofFn fun i => mulDown (divDown (orientedMatrix j i) (D i)) shrink
    if le (sqSumUp fun i => absolute (u₀[i.val]'i.isLt)) one then u₀ else Vector.replicate n zero
  let u : Fin N → Vec 𝕋 n := fun j i => (uV[j.val]'j.isLt)[i.val]'i.isLt
  -- the remainders `p - c - G u`, between their two roundings, and their hull
  let lo : Fin N → Vec 𝕋 n := fun j i => subDown (pts j i) (addUp (c i) (dotUp (G i) (u j)))
  let hi : Fin N → Vec 𝕋 n := fun j i => subUp (pts j i) (addDown (c i) (dotDown (G i) (u j)))
  let err : Interval (Vec 𝕋 n) :=
    Interval.materialise
      ⟨fun i => minimumOver fun j => lo j i, fun i => maximumOver fun j => hi j i⟩
  ⟨n, c, G, err⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
