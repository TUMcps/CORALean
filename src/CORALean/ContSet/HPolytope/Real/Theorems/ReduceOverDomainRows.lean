module

public import CORALean.ContSet.HPolytope.Real.Operations.ReduceOverDomain
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.Ellipsoid.Real.Operations.ApplyEqDotProduct

@[expose] public section

/-!
# Each normalized row against the reduced one, over the domain

On the domain, the reduced row `A_reduced' x` differs from a normalized row `a_i' x` by
`(a_i - A_reduced)' x`, which lies between the infimum and the supremum of
`(A - A_reduced)' * dom`, the corner sums of `reduceOverDomain`. Written against the reduced
right-hand sides: the outer one is `sup b - prodInf`, the inner one `inf b - prodSup`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.reduceOverDomain_rows (P : HPolytope (Vec ℝ n)) (dom : Interval (Vec ℝ n))
    {x : Vec ℝ n} (hx : x ∈ dom.construct) (i : Fin P.m) :
    ((P.reduceOverDomain dom true).A (0 : Fin 1) x +
        ((⨆ k, P.normalizeRows.b k) - (P.reduceOverDomain dom true).b (0 : Fin 1))
        ≤ P.normalizeRows.A i x) ∧
      P.normalizeRows.A i x ≤ (P.reduceOverDomain dom false).A (0 : Fin 1) x +
        ((⨅ k, P.normalizeRows.b k) -
          (P.reduceOverDomain dom false).b (0 : Fin 1)) := by -- --- PROOF ---
  -- the difference of the normalized row and the reduced one, entrywise
  set Pn := P.normalizeRows with hPn
  set Aint : Interval (Vec ℝ n) :=
    ⟨fun j => ⨅ i, dualVec (Pn.A i) j, fun j => ⨆ i, dualVec (Pn.A i) j⟩ with hAint
  have hred : ∀ y : Vec ℝ n,
      (HPolytope.rowLin (Matrix.of fun (_ : Fin 1) j => Aint.center j) 0) y =
        ∑ j, Aint.center j * y j := fun y => by
    simp [HPolytope.rowLin, Matrix.mulVec, dotProduct]
  -- the normalized row, the corner products and their sums
  have hrow : Pn.A i x = ∑ j, dualVec (Pn.A i) j * x j := by
    rw [apply_eq_dotProduct, dotProduct]
  have hdiff : ∀ j, Interval.mulLo (Aint.inf j - Aint.center j) (Aint.sup j - Aint.center j)
        (dom.inf j) (dom.sup j) ≤ (dualVec (Pn.A i) j - Aint.center j) * x j ∧
      (dualVec (Pn.A i) j - Aint.center j) * x j ≤
        Interval.mulHi (Aint.inf j - Aint.center j) (Aint.sup j - Aint.center j)
          (dom.inf j) (dom.sup j) := fun j => by
    have h1 : Aint.inf j ≤ dualVec (Pn.A i) j :=
      ciInf_le (Set.finite_range _).bddBelow i
    have h2 : dualVec (Pn.A i) j ≤ Aint.sup j :=
      le_ciSup (f := fun i => dualVec (Pn.A i) j) (Set.finite_range _).bddAbove i
    exact Interval.mul_between_corners (by linarith) (by linarith) (hx j).1 (hx j).2
  have hsum : ∑ j, Interval.mulLo (Aint.inf j - Aint.center j) (Aint.sup j - Aint.center j)
        (dom.inf j) (dom.sup j) ≤ Pn.A i x - ∑ j, Aint.center j * x j ∧
      Pn.A i x - ∑ j, Aint.center j * x j ≤
        ∑ j, Interval.mulHi (Aint.inf j - Aint.center j) (Aint.sup j - Aint.center j)
          (dom.inf j) (dom.sup j) := by
    rw [hrow, ← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    exact ⟨Finset.sum_le_sum fun j _ => (hdiff j).1, Finset.sum_le_sum fun j _ => (hdiff j).2⟩
  -- the reduced row and right-hand sides, read off the definition
  have hb1 : (P.reduceOverDomain dom true).b (0 : Fin 1) = (⨆ k, Pn.b k) -
      ∑ j, Interval.mulLo (Aint.inf j - Aint.center j) (Aint.sup j - Aint.center j)
        (dom.inf j) (dom.sup j) := rfl
  have hb2 : (P.reduceOverDomain dom false).b (0 : Fin 1) = (⨅ k, Pn.b k) -
      ∑ j, Interval.mulHi (Aint.inf j - Aint.center j) (Aint.sup j - Aint.center j)
        (dom.inf j) (dom.sup j) := rfl
  have hA1 : (P.reduceOverDomain dom true).A (0 : Fin 1) x = ∑ j, Aint.center j * x j :=
    (hred x).trans rfl
  have hA2 : (P.reduceOverDomain dom false).A (0 : Fin 1) x = ∑ j, Aint.center j * x j :=
    (hred x).trans rfl
  rw [hb1, hb2, hA1, hA2]
  constructor <;> linarith [hsum.1, hsum.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
