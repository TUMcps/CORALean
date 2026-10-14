module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGO
public import CORALean.Global.DescProdState
public import CORALean.Global.LinResidual
public import CORALean.Global.StackSelectMulVec

@[expose] public section

/-!
# `computeGO` gives the state of every run

For a run `x` under inputs `u` of the system, `x(k+1) - x_ref(k+1)` is `A{k}` applied to the
initial deviation, plus `B{k,j}` applied to each input deviation, plus `F{k,j}` applied to each
linearization error `L_j = [L_x; L_y]`, the `linResidual` of `f` and of the output equation at
the reference point. An identity, exact for any run: it says how the deviation is built from
the errors, and nothing about how large the errors are.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.computeGO_state (sys : NonlinearSysDT n m)
    (x0 : Vec ℝ n) (u_ref : ℕ → Vec ℝ m)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} (hx : ∀ k, x (k + 1) = sys.f (x k) (u k)) (k : ℕ) :
    x (k + 1) - (sys.computeGO x0 u_ref).x (k + 1)
      = (sys.computeGO x0 u_ref).A k *ᵥ (x 0 - x0)
        + ∑ j ∈ Finset.range (k + 1),
            (sys.computeGO x0 u_ref).B k j *ᵥ (u j - u_ref j)
        + ∑ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).F k j *ᵥ
            (Fin.append
              (linResidual sys.f ((sys.computeGO x0 u_ref).x j) (u_ref j) (x j) (u j))
              (linResidual sys.g ((sys.computeGO x0 u_ref).x j) (u_ref j) (x j) (u j))
              : Vec ℝ (n + sys.q)) := by -- --- PROOF ---
  -- the recursion of the deviation, with the residual as its error
  have h := descProd_state
    (fun k => jacobianMat (fun x => sys.f x (u_ref k)) (sys.refState x0 u_ref k))
    (fun k => jacobianMat (fun u => sys.f (sys.refState x0 u_ref k) u) (u_ref k))
    (fun k => x k - sys.refState x0 u_ref k) (fun k => u k - u_ref k)
    (fun k => linResidual sys.f (sys.refState x0 u_ref k) (u_ref k) (x k) (u k))
    (fun k => by
      simp only [linResidual, NonlinearSysDT.refState, hx]
      abel) k
  simp only [NonlinearSysDT.computeGO] at h ⊢
  rw [h]
  refine congrArg₂ _ (congrArg₂ _ rfl ?_) ?_
  · -- the input terms: `j ≤ k` throughout the sum
    exact Finset.sum_congr rfl fun j hj => by
      rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  · -- the error terms: the selection matrix picks `L_x`
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), ← Matrix.mulVec_mulVec,
      stackFst_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
