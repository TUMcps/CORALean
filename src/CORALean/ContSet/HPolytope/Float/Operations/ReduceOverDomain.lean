module

public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.RowScale
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `HPolytope.reduceOverDomain` over a floating-point scalar

CORA's `reduceOverDomain` on the stored floats: the constraints replaced by the single
halfspace `A_reduced' x ≤ b_reduced`. Each row is scaled by its `rowScale` (CORA's 2-norm
normalization), every scaled entry and right-hand side rounded both ways; `A` is the interval
hull of the scaled rows (`min`/`max` over the rows) and `b` that of the scaled right-hand sides;
`A_reduced` is the rounded midpoint of `A`, and `b_reduced = b - (A - A_reduced)' * dom` is
bounded by corner products rounded outward, of which type `'outer'` takes the upper end and the
other type the lower. Equality constraints are not read; the Newton steps `p` of the norm are an
argument. Type `'outer'` reads the rows with the error box folded into them (`absorbRounding`),
which also writes an equality as two inequalities; the inner type reads the rows as stored, and
so is sound for a polytope without a box.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.reduceOverDomain (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n))
    (outer : Bool := true) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- the outer type reads the rows with the error box folded in, the inner as stored
  let Q := if outer then P.absorbRounding else P
  -- A = interval(min(A_,[],1)', max(A_,[],1)'), the scaled rows rounded outward
  let Ainf : Vec 𝕋 n := fun j => minimumOver fun i => mulDown (Q.A i j) (Q.rowScale p i)
  let Asup : Vec 𝕋 n := fun j => maximumOver fun i => mulUp (Q.A i j) (Q.rowScale p i)
  -- b = interval(min(b_), max(b_))
  let bInf : 𝕋 := minimumOver fun i => mulDown (Q.b i) (Q.rowScale p i)
  let bSup : 𝕋 := maximumOver fun i => mulUp (Q.b i) (Q.rowScale p i)
  -- A_reduced = center(A)
  let Ared : Vec 𝕋 n := fun j => half (addDown (Ainf j) (Asup j))
  -- (A - A_reduced)' * dom, both ends
  let prodInf : 𝕋 := sumDown fun j =>
    Interval.mulLo (subDown (Ainf j) (Ared j)) (subUp (Asup j) (Ared j)) (dom.inf j) (dom.sup j)
  let prodSup : 𝕋 := sumUp fun j =>
    Interval.mulHi (subDown (Ainf j) (Ared j)) (subUp (Asup j) (Ared j)) (dom.inf j) (dom.sup j)
  -- P_out = polytope(A_reduced', supremum(b_reduced)), or infimum for the other type
  { m := 1
    A := fun _ => Ared
    b := fun _ => if outer then subUp bSup prodInf else subDown bInf prodSup
    me := 0
    Ae := fun r => r.elim0
    be := fun r => r.elim0
    b_error := fun _ => zero
    be_error := fun _ => zero
    I_error := Interval.origin n }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
