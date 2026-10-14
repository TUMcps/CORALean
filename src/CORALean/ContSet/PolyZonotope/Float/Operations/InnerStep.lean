module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Recip
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianBox
public import CORALean.ContSet.PolyZonotope.Float.Operations.SliceBox

@[expose] public section

/-!
# `PolyZonotope.innerStep`

One body of the `while` loop of CORA's `aux_InnerGeneral` and `aux_containsInterval` ([1, Alg. 3],
line 14): the Jacobian re-evaluated on `X_modified`, preconditioned, split into the columns `ind`
(`J1`) and the others (`J2`), and
`t = aux_InvDiag(J1)·(b - aux_OffDiag(J1)·(U1_ - u1_)) - J2·(U2_ - u2_)`. `none` where a diagonal
entry of `J1` holds `0`, where CORA's `aux_InvDiag` makes the step fail (`catch; break`). The
diagonal product is taken row by row rather than as an interval matrix with zero off-diagonal
entries, which is the same interval.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The step `t` of [1, Alg. 3] at the current `U1_`, or `none` if `diag(J1)` holds `0`. -/
def PolyZonotope.innerStep (pZ : PolyZonotope (Vec 𝕋 n)) (X₀ : Interval (Vec 𝕋 pZ.p))
    (ind : Fin n ↪ Fin pZ.p) (C : Mat 𝕋 n n) (xc : Vec 𝕋 pZ.p) (b U : Interval (Vec 𝕋 n)) :
    Option (Interval (Vec 𝕋 n)) :=
  -- the coordinates of `u₁`
  let sel : Fin pZ.p → Bool := fun k => (List.finRange n).any fun i => decide (ind i = k)
  -- U2_ - u2_, and `0` at the coordinates of `u₁`
  let W2 : Interval (Vec 𝕋 pZ.p) := ⟨fun k => if sel k then zero else subDown (X₀.inf k) (xc k),
    fun k => if sel k then zero else subUp (X₀.sup k) (xc k)⟩
  -- C*df(X_modified)
  let CJ := (Interval.matMul (Interval.point C) (PolyZonotope.jacobianBox pZ
    (PolyZonotope.sliceBox X₀ ind U))).materialiseMat
  -- [J1, J2] = aux_Extract(C*df(X_modified), ind, n)
  let J1 : Interval (Mat 𝕋 n n) := ⟨fun i j => CJ.inf i (ind j), fun i j => CJ.sup i (ind j)⟩
  let J2 : Interval (Mat 𝕋 n pZ.p) := ⟨fun i k => if sel k then zero else CJ.inf i k,
    fun i k => if sel k then zero else CJ.sup i k⟩
  -- diag(J1) and aux_OffDiag(J1)
  let D : Interval (Vec 𝕋 n) := ⟨fun i => J1.inf i i, fun i => J1.sup i i⟩
  let Off : Interval (Mat 𝕋 n n) := ⟨fun i j => if i = j then zero else J1.inf i j,
    fun i j => if i = j then zero else J1.sup i j⟩
  -- u1_
  let u1c : Vec 𝕋 n := fun i => xc (ind i)
  if (List.finRange n).all fun i => ltStrict zero (D.inf i) || ltStrict (D.sup i) zero then
    -- t = aux_InvDiag(J1)*(b - aux_OffDiag(J1)*(U1_-u1_)) - J2*(U2_ - u2_)
    some ((D.recip.times (b.minus (Off.mtimesIntervalMat (U.minus (Interval.point u1c))))).minus
      (J2.mtimesIntervalMat W2)).materialise
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
