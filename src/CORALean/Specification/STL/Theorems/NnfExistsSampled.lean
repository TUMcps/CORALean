module

public import CORALean.Specification.STL.Operations.NnfWeight
public import CORALean.Specification.STL.Theorems.NnfRewriteLit
public import CORALean.Specification.STL.Theorems.NnfRewriteAnd
public import CORALean.Specification.STL.Theorems.NnfRewriteOr
public import CORALean.Specification.STL.Theorems.NnfRewriteUntil
public import CORALean.Specification.STL.Theorems.NnfRewriteRelease

@[expose] public section

/-!
# Every normal form rewrites to sampled time

[1, Lemma 4]: a formula in negation normal form with natural bounds, `c = 1`, has a sampled time
formula implying it, and one implying `F_I` and `G_I` of it. By strong induction on the weight,
which falls from `φ U[i,j] ψ` to its operands and to `φ U[i-1,j-1] ψ`; the cases are the
rewriting rules of [1, Table 1], one theorem each. This is the content of the iteration "until no
rule matches anymore": that it ends is the induction.

## Inputs
* `n` – formula in negation normal form

## Hypotheses
* none

## Conclusion
* the normal form rewrites to sampled time

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Nnf.hasSampledRewrite (n : STL.Nnf X) : -- --- CONCL ---
    n.HasSampledRewrite := by -- --- PROOF ---
  induction hw : n.weight using Nat.strong_induction_on generalizing n with
  | _ w ih =>
    -- every operand weighs less than its parent, and `φ U[i',j'] ψ` less than `φ U[i,j] ψ`
    have key : ∀ m : STL.Nnf X, m.weight < w → m.HasSampledRewrite := fun m hm => ih _ hm m rfl
    subst hw
    cases n with
    | lit ϱ => exact STL.Nnf.hasSampledRewrite_lit ϱ
    | and φ ψ =>
      exact STL.Nnf.hasSampledRewrite_and (key φ (by simp [STL.Nnf.weight]; omega))
        (key ψ (by simp [STL.Nnf.weight]; omega))
    | or φ ψ =>
      -- the operands weigh less
      exact STL.Nnf.hasSampledRewrite_or (key φ (by simp [STL.Nnf.weight]; omega))
        (key ψ (by simp [STL.Nnf.weight]; omega))
    | «until» i j φ ψ =>
      -- the operands and the smaller bounds all weigh less
      have hS : 0 < φ.weight + ψ.weight + 1 := by omega
      refine STL.Nnf.hasSampledRewrite_until i j
        (key φ ?_) (key ψ ?_) fun j' hj' i' => key _ ?_
      · simp only [STL.Nnf.weight]
        nlinarith
      · simp only [STL.Nnf.weight]
        nlinarith
      · simp only [STL.Nnf.weight]
        exact Nat.mul_lt_mul_of_pos_right (by omega) hS
    | release i j φ ψ =>
      -- the same, and `φ ∧ ψ` weighs less once `j ≥ 1`
      have hS : 0 < φ.weight + ψ.weight + 1 := by omega
      refine STL.Nnf.hasSampledRewrite_release i j
        (key φ ?_) (key ψ ?_) (fun hj => key _ ?_) fun j' hj' i' => key _ ?_
      · simp only [STL.Nnf.weight]
        nlinarith
      · simp only [STL.Nnf.weight]
        nlinarith
      · simp only [STL.Nnf.weight]
        nlinarith
      · simp only [STL.Nnf.weight]
        exact Nat.mul_lt_mul_of_pos_right (by omega) hS

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
