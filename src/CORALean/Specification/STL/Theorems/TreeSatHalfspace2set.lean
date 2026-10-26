module

public import CORALean.Specification.STL.Operations.TreeHalfspace2set
public import CORALean.Specification.STL.Theorems.Basic
public import CORALean.Specification.STL.Theorems.TreeSatCompare
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A halfspace row is the comparison it states

`aux_halfspace2set(x,A,b)` of `polytope2stl.m` builds a formula satisfied by a trace exactly when
the initial state meets the halfspace: `op (Σⱼ aⱼ xⱼ) b`.

## Inputs
* `op` – comparison
* `a` – normal vector
* `b` – offset
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* the node holds iff the halfspace comparison holds at time zero
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped BigOperators NNReal

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem STL.Tree.aux_sum_filter (a x : Fin n → ℝ) : -- --- CONCL ---
    (((List.finRange n).filter (fun i => a i ≠ 0)).map (fun i => a i * x i)).sum
      = ∑ j, a j * x j := by -- --- PROOF ---
  rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  have : ((List.finRange n).filter (fun i => a i ≠ 0)).toFinset
      = Finset.univ.filter (fun i => a i ≠ 0) := by ext; simp
  rw [this, Finset.sum_filter_of_ne]
  intro i _ h h0
  exact h (by simp [h0])

private theorem STL.Tree.aux_eval_term (a x : Fin n → ℝ) (i : Fin n) :
    (if a i = 1 then STL.Expr.var i else STL.Expr.times (.num (a i)) (.var i)).eval x
      = a i * x i := by
  split_ifs with h
  · simp [STL.Expr.eval, h]
  · simp [STL.Expr.times, STL.Expr.eval]

private theorem STL.Tree.aux_eval_foldl (a x : Fin n → ℝ) (rest : List (Fin n))
    (ind : Fin n) : -- --- CONCL ---
    (rest.foldl (fun rhs i => STL.Expr.plus rhs
        (if a i = 1 then STL.Expr.var i else STL.Expr.times (.num (a i)) (.var i)))
      (if a ind = 1 then STL.Expr.var ind else STL.Expr.times (.num (a ind)) (.var ind))).eval x
      = a ind * x ind + (rest.map fun i => a i * x i).sum := by -- --- PROOF ---
  suffices ∀ init : STL.Expr ℝ n, (rest.foldl (fun rhs i => STL.Expr.plus rhs
        (if a i = 1 then STL.Expr.var i else STL.Expr.times (.num (a i)) (.var i))) init).eval x
      = init.eval x + (rest.map fun i => a i * x i).sum by
    rw [this, STL.Tree.aux_eval_term]
  induction rest with
  | nil => simp
  | cons i rest ih =>
    intro init
    rw [List.foldl_cons, ih, STL.Expr.eval_plus, STL.Tree.aux_eval_term, List.map_cons,
      List.sum_cons]
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_halfspace2set (op : STL.Cmp) (a : Fin n → ℝ) (b : ℝ)
    (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (STL.Tree.halfspace2set op a b).Satisfies ξ ↔ op.Relates (∑ j, a j * ξ 0 j)
    b := by -- --- PROOF ---
  unfold STL.Tree.halfspace2set
  split
  · rename_i h
    rw [STL.Tree.sat_compare]
    have h0 : ∀ j, a j = 0 := fun j => by simpa using List.filter_eq_nil_iff.1 h j (by simp)
    simp [STL.Expr.eval, h0]
  · rename_i ind rest h
    rw [STL.Tree.sat_compare, ← STL.Tree.aux_sum_filter a (ξ 0), h]
    simp only [STL.Expr.eval, List.map_cons, List.sum_cons]
    rw [STL.Tree.aux_eval_foldl a (ξ 0) rest ind]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
