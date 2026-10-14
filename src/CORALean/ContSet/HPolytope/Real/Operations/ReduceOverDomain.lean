module

public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec

@[expose] public section

/-!
# `HPolytope.reduceOverDomain`

CORA's `reduceOverDomain`: the constraints of `P` replaced by the single halfspace
`A_reduced' x ≤ b_reduced`. The normalized rows `A_` are enclosed by the interval vector `A`
(`min`/`max` over the rows) and the right-hand sides by the interval `b`; `A_reduced` is the
centre of `A`, and `b_reduced = b - (A - A_reduced)' * dom`, an interval, of which type `'outer'`
takes the supremum and the other type the infimum. Equality constraints are not read.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.reduceOverDomain (P : HPolytope (Vec ℝ n)) (dom : Interval (Vec ℝ n))
    (outer : Bool := true) : HPolytope (Vec ℝ n) :=
  -- [A_,b_,Ae_,be_] = priv_normalizeConstraints(P.A_.val,P.b_.val,P.Ae_.val,P.be_.val,'A')
  let Pn := P.normalizeRows
  let A_ : Fin P.m → Vec ℝ n := fun i => dualVec (Pn.A i)
  let b_ : Fin P.m → ℝ := Pn.b
  -- A = interval(min(A_,[],1)',max(A_,[],1)'); b = interval(min(b_),max(b_))
  let A : Interval (Vec ℝ n) := ⟨fun j => ⨅ i, A_ i j, fun j => ⨆ i, A_ i j⟩
  let bInf : ℝ := ⨅ i, b_ i
  let bSup : ℝ := ⨆ i, b_ i
  -- A_reduced = center(A); b_reduced = b - (A - A_reduced)'*dom
  let A_reduced : Vec ℝ n := A.center
  let prodInf : ℝ := ∑ j,
    Interval.mulLo (A.inf j - A_reduced j) (A.sup j - A_reduced j) (dom.inf j) (dom.sup j)
  let prodSup : ℝ := ∑ j,
    Interval.mulHi (A.inf j - A_reduced j) (A.sup j - A_reduced j) (dom.inf j) (dom.sup j)
  let b_reducedInf : ℝ := bInf - prodSup
  let b_reducedSup : ℝ := bSup - prodInf
  -- P_out = polytope(A_reduced', supremum(b_reduced)), or infimum for the other type
  { m := 1
    A := fun _ => HPolytope.rowLin (Matrix.of fun (_ : Fin 1) j => A_reduced j) 0
    b := fun _ => if outer then b_reducedSup else b_reducedInf
    me := 0
    Ae := Fin.elim0
    be := Fin.elim0 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
