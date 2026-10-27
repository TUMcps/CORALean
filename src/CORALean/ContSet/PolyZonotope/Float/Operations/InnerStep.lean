module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Recip
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.PolyZonotope.Float.Operations.JacobianBox
public import CORALean.ContSet.Interval.Float.Interval

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

## Inputs
* `pZ` – polynomial zonotope
* `X₀` – inner factor box
* `ind` – selected factor indices
* `C` – approximate inverse Jacobian
* `xc` – center of the factor box
* `b` – residual box
* `U` – candidate enclosure box

## Output
* contracted enclosure box, if the step succeeds

## References

* [1] [O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing,
      2013.](../../../../../../references/2013/mullier-rc-general-inner-approximation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} {n p : ℕ}

/-- `X₀` with coordinate `ind i` replaced by `U`'s coordinate `i`. -/
def PolyZonotope.aux_sliceBox (X₀ : Interval (Vec 𝕋 p)) (ind : Fin n → Fin p)
    (U : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 p) :=
  -- which coordinate of `U`, if any, sits at `k`
  let pick : Fin p → Option (Fin n) := fun k => (List.finRange n).find? fun i => decide (ind i = k)
  ⟨fun k => match pick k with | some i => U.inf i | none => X₀.inf k,
   fun k => match pick k with | some i => U.sup i | none => X₀.sup k⟩

end


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The step `t` of [1, Alg. 3] at the current `U1_`, or `none` if `diag(J1)` holds `0`. -/
def PolyZonotope.innerStep (pZ : PolyZonotope (Vec 𝕋 n)) (X₀ : Interval (Vec 𝕋 pZ.p))
    (ind : Fin n ↪ Fin pZ.p) (C : Mat 𝕋 n n) (xc : Vec 𝕋 pZ.p) (b U : Interval (Vec 𝕋 n)) :
    Option (Interval (Vec 𝕋 n)) :=
  -- 10. which coordinates make up `u₁`
  let sel : Fin pZ.p → Bool := fun k => (List.finRange n).any fun i => decide (ind i = k)
  -- 14. `ũ₂ - ũ₂`, and `0` at the coordinates of `u₁`
  let W2 : Interval (Vec 𝕋 pZ.p) := ⟨fun k => if sel k then zero else subDown (X₀.inf k) (xc k),
    fun k => if sel k then zero else subUp (X₀.sup k) (xc k)⟩
  -- 10. `C J`, the preconditioned Jacobian on the current box
  let CJ := (Interval.matMul (Interval.point C) (PolyZonotope.jacobianBox pZ
    (PolyZonotope.aux_sliceBox X₀ ind U))).materialiseMat
  -- 10. `(J_{f1:r,u1}, J_{f1:r,u2}) ← Extract(C J, r, m)`
  let J1 : Interval (Mat 𝕋 n n) := ⟨fun i j => CJ.inf i (ind j), fun i j => CJ.sup i (ind j)⟩
  let J2 : Interval (Mat 𝕋 n pZ.p) := ⟨fun i k => if sel k then zero else CJ.inf i k,
    fun i k => if sel k then zero else CJ.sup i k⟩
  -- 14. `Diag J_{f1:r,u1}` and `OffDiag J_{f1:r,u1}`
  let D : Interval (Vec 𝕋 n) := ⟨fun i => J1.inf i i, fun i => J1.sup i i⟩
  let Off : Interval (Mat 𝕋 n n) := ⟨fun i j => if i = j then zero else J1.inf i j,
    fun i j => if i = j then zero else J1.sup i j⟩
  -- 14. the midpoint `ũ₁`
  let u1c : Vec 𝕋 n := fun i => xc (ind i)
  if (List.finRange n).all fun i => ltStrict zero (D.inf i) || ltStrict (D.sup i) zero then
    -- 14. `t ← (Diag⁻¹ J₁)(b - (OffDiag J₁)(ũ₁ - ũ₁) - J₂(ũ₂ - ũ₂))`
    some ((D.recip.times (b.minus (Off.mtimesIntervalMat (U.minus (Interval.point u1c))))).minus
      (J2.mtimesIntervalMat W2)).materialise
  else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
