module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.ComputeGO
public import CORALean.Global.DescProd
public import Mathlib.Tactic.Abel
public import CORALean.Global.LinResidual
public import CORALean.Global.StackSelect

@[expose] public section

/-!
# `computeGO` gives the state of every run

For a run `x` under inputs `u` of the system, `x(k+1) - x_ref(k+1)` is `A{k}` applied to the
initial deviation, plus `B{k,j}` applied to each input deviation, plus `F{k,j}` applied to each
linearization error `L_j = [L_x; L_y]`, the `linResidual` of `f` and of the output equation at
the reference point. An identity, exact for any run: it says how the deviation is built from
the errors, and nothing about how large the errors are.

## Inputs
* `sys` – system
* `x0` – initial point
* `u_ref` – reference input
* `x` – state trajectory
* `u` – input trajectory
* `k` – step

## Hypotheses
* `hx` – states follow the dynamics

## Conclusion
* the state deviation is the sum of the parameter terms
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n r : ℕ}

/-- The selection matrices pick their block. -/
private theorem aux_stackFst_mulVec (a : Vec ℝ n) (b : Vec ℝ r) : -- --- CONCL ---
    stackFst n r *ᵥ (Fin.append a b : Vec ℝ (n + r)) = a := by -- --- PROOF ---
  funext i
  -- split the sum over `Fin (n + r)` into its two halves
  simp only [Matrix.mulVec, dotProduct, stackFst, Matrix.of_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  simp [Fin.val_inj]
  -- the second half lies above `n`, the diagonal below it
  exact Finset.sum_eq_zero fun x _ => by rw [if_neg (by have := i.isLt; omega)]

end


/-- A recursion `Δ(k+1) = A_k Δ(k) + B_k δ(k) + L_k` in closed form. -/
private theorem aux_descProd_state (A : ℕ → Mat ℝ n n) (B : ℕ → Mat ℝ n m) (Δ : ℕ → Vec ℝ n)
    (δ : ℕ → Vec ℝ m) (L : ℕ → Vec ℝ n)
    (h : ∀ k, Δ (k + 1) = A k *ᵥ Δ k + B k *ᵥ δ k + L k) (k : ℕ) : -- --- CONCL ---
    Δ (k + 1) = descProd A k (k + 1) *ᵥ Δ 0
      + ∑ j ∈ Finset.range (k + 1), (descProd A k (k - j) * B j) *ᵥ δ j
      + ∑ j ∈ Finset.range (k + 1), descProd A k (k - j) *ᵥ L j := by -- --- PROOF ---
  induction k with
  | zero =>
    -- one step: the products are `A 0` and the empty product
    simp [h 0, descProd]
  | succ k ih =>
    -- the next step multiplies every term of the previous one by `A (k+1)`
    have hp : ∀ j ∈ Finset.range (k + 1),
        descProd A (k + 1) (k + 1 - j) = A (k + 1) * descProd A k (k - j) := fun j hj => by
      have : k + 1 - j = (k - j) + 1 := by have := Finset.mem_range.1 hj; omega
      rw [this]; simp [descProd]
    -- the two sums over `range (k+2)`: the last term, and `A (k+1)` times the rest
    have hB : ∑ j ∈ Finset.range (k + 2), (descProd A (k + 1) (k + 1 - j) * B j) *ᵥ δ j
        = A (k + 1) *ᵥ ∑ j ∈ Finset.range (k + 1), (descProd A k (k - j) * B j) *ᵥ δ j
          + B (k + 1) *ᵥ δ (k + 1) := by
      rw [Finset.sum_range_succ, Matrix.mulVec_sum]
      simp only [Nat.sub_self, descProd, Matrix.one_mul, Matrix.mulVec_mulVec]
      rw [Finset.sum_congr rfl fun j hj => by rw [hp j hj, Matrix.mul_assoc]]
    have hL : ∑ j ∈ Finset.range (k + 2), descProd A (k + 1) (k + 1 - j) *ᵥ L j
        = A (k + 1) *ᵥ ∑ j ∈ Finset.range (k + 1), descProd A k (k - j) *ᵥ L j
          + L (k + 1) := by
      rw [Finset.sum_range_succ, Matrix.mulVec_sum]
      simp only [Nat.sub_self, descProd, Matrix.one_mulVec, Matrix.mulVec_mulVec]
      rw [Finset.sum_congr rfl fun j hj => by rw [hp j hj]]
    have h0 : descProd A (k + 1) (k + 2) = A (k + 1) * descProd A k (k + 1) := by
      simp [descProd]
    rw [h (k + 1), ih, hB, hL, h0]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.computeGO_state (sys : NonlinearSysDT n m)
    (x0 : Vec ℝ n) (u_ref : ℕ → Vec ℝ m)
    {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} (hx : ∀ k, x (k + 1) = sys.f (x k) (u k))
    (k : ℕ) : -- --- CONCL ---
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
  have h := aux_descProd_state
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
      aux_stackFst_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
