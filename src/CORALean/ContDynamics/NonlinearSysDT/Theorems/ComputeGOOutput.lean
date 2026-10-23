module

public import CORALean.ContDynamics.NonlinearSysDT.NonlinearSysDT
public import CORALean.ContDynamics.NonlinearSysDT.Theorems.ComputeGOState

@[expose] public section

/-!
# `computeGO` gives the output of every run

`y(k) - y_ref(k)` is `C{k}` applied to the initial deviation, plus `D{k,j}` applied to each input
deviation, plus `E{k,j}` applied to each linearization error `L_j = [L_x; L_y]`, for every run
of the system, `y` its output as `IsTrajectory` states it. As for the state, an identity: the
errors are the `linResidual`s, not bounded.

## Inputs
* `sys` – system
* `x0` – initial point
* `u_ref` – reference input
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory
* `k` – step

## Hypotheses
* `traj` – trajectory of the system

## Conclusion
* the output deviation is the sum of the parameter terms
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n r : ℕ}

/-- The second selection matrix applied to a stacked vector gives its second block. -/
theorem aux_stackSnd_mulVec (a : Vec ℝ n) (b : Vec ℝ r) : -- --- CONCL ---
    stackSnd n r *ᵥ (Fin.append a b : Vec ℝ (n + r)) = b := by -- --- PROOF ---
  funext i
  simp only [Matrix.mulVec, dotProduct, stackSnd, Matrix.of_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  simp only [ite_mul, one_mul, zero_mul, Nat.add_left_cancel_iff, Fin.val_inj,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- the first half lies below `n`, the diagonal above it
  rw [Finset.sum_eq_zero (fun x _ => by rw [if_neg (by omega)]), zero_add]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSysDT.computeGO_output (sys : NonlinearSysDT n m)
    (x0 : Vec ℝ n) (u_ref : ℕ → Vec ℝ m)
    {R₀ : S n} {U : S m} {x : ℕ → Vec ℝ n} {u : ℕ → Vec ℝ m} {y : ℕ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory R₀ U x u y) (k : ℕ) : -- --- CONCL ---
    let res := fun j : ℕ => (Fin.append (linResidual sys.f ((sys.computeGO x0 u_ref).x j) (u_ref j)
      (x j) (u j))
        (linResidual sys.g ((sys.computeGO x0 u_ref).x j) (u_ref j) (x j) (u j)) : Vec ℝ (n +
          sys.q))
    y k - (sys.computeGO x0 u_ref).y k
      = (sys.computeGO x0 u_ref).C k *ᵥ (x 0 - x0)
        + ∑ j ∈ Finset.range (k + 1),
            (sys.computeGO x0 u_ref).D k j *ᵥ (u j - u_ref j)
        + ∑ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).E k j *ᵥ
            (res j) := by -- --- PROOF ---
  intro res
  rw [traj.output k]
  cases k with
  | zero =>
    -- no earlier step: only the feedthrough and `L_y` remain
    rw [Finset.sum_range_one, Finset.sum_range_one]
    have hD : (sys.computeGO x0 u_ref).D 0 0
        = jacobianMat (fun u => sys.g x0 u) (u_ref 0) := by
      simp [NonlinearSysDT.computeGO, NonlinearSysDT.refState]
    have hE : (sys.computeGO x0 u_ref).E 0 0 = stackSnd n sys.q := by
      simp [NonlinearSysDT.computeGO]
    have hC : (sys.computeGO x0 u_ref).C 0
        = jacobianMat (fun x => sys.g x (u_ref 0)) x0 := by
      simp [NonlinearSysDT.computeGO, descProd, NonlinearSysDT.refState]
    rw [hD, hE, hC, aux_stackSnd_mulVec]
    simp only [linResidual, NonlinearSysDT.computeGO, NonlinearSysDT.refState]
    abel
  | succ k =>
    -- the deviation of the state one step back, from the state theorem
    have hs := NonlinearSysDT.computeGO_state sys x0 u_ref traj.step k
    -- row `k + 1` is the output Jacobian times row `k`, plus the feedthrough and `L_y`
    have hC : (sys.computeGO x0 u_ref).C (k + 1) = jacobianMat
        (fun x => sys.g x (u_ref (k + 1))) ((sys.computeGO x0 u_ref).x (k + 1))
        * (sys.computeGO x0 u_ref).A k := rfl
    have hD : ∀ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).D (k + 1) j
        = jacobianMat (fun x => sys.g x (u_ref (k + 1))) ((sys.computeGO x0 u_ref).x (k + 1))
          * (sys.computeGO x0 u_ref).B k j := fun j hj => by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      simp only [NonlinearSysDT.computeGO, if_pos (Nat.lt_succ_of_le this), if_pos this,
        Nat.add_sub_cancel, Matrix.mul_assoc]
    have hE : ∀ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).E (k + 1) j
        = jacobianMat (fun x => sys.g x (u_ref (k + 1))) ((sys.computeGO x0 u_ref).x (k + 1))
          * (sys.computeGO x0 u_ref).F k j := fun j hj => by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      simp only [NonlinearSysDT.computeGO, if_pos (Nat.lt_succ_of_le this), if_pos this,
        Nat.add_sub_cancel, Matrix.mul_assoc]
    have hD' : (sys.computeGO x0 u_ref).D (k + 1) (k + 1) = jacobianMat
        (fun u => sys.g ((sys.computeGO x0 u_ref).x (k + 1)) u) (u_ref (k + 1)) := by
      simp [NonlinearSysDT.computeGO]
    have hE' : (sys.computeGO x0 u_ref).E (k + 1) (k + 1) = stackSnd n sys.q := by
      simp [NonlinearSysDT.computeGO]
    -- the earlier terms, as the output Jacobian applied to those of the state
    have sD : ∑ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).D (k + 1) j
          *ᵥ (u j - u_ref j) = jacobianMat (fun x => sys.g x (u_ref (k + 1)))
          ((sys.computeGO x0 u_ref).x (k + 1)) *ᵥ ∑ j ∈ Finset.range (k + 1),
          (sys.computeGO x0 u_ref).B k j *ᵥ (u j - u_ref j) := by
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j hj => by rw [hD j hj, Matrix.mulVec_mulVec]
    have sE : ∑ j ∈ Finset.range (k + 1), (sys.computeGO x0 u_ref).E (k + 1) j
          *ᵥ (res j) = jacobianMat (fun x => sys.g x (u_ref (k + 1)))
          ((sys.computeGO x0 u_ref).x (k + 1)) *ᵥ ∑ j ∈ Finset.range (k + 1),
          (sys.computeGO x0 u_ref).F k j *ᵥ (res j) := by
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j hj => by rw [hE j hj, Matrix.mulVec_mulVec]
    rw [Finset.sum_range_succ _ (k + 1), Finset.sum_range_succ _ (k + 1), hC, sD, sE, hD', hE',
      aux_stackSnd_mulVec]
    -- the output deviation is the Jacobians applied to those of state and input, plus `L_y`
    have hy : sys.g (x (k + 1)) (u (k + 1)) - (sys.computeGO x0 u_ref).y (k + 1)
        = jacobianMat (fun x => sys.g x (u_ref (k + 1)))
            ((sys.computeGO x0 u_ref).x (k + 1))
            *ᵥ (x (k + 1) - (sys.computeGO x0 u_ref).x (k + 1))
          + jacobianMat (fun u => sys.g ((sys.computeGO x0 u_ref).x (k + 1)) u) (u_ref (k + 1))
            *ᵥ (u (k + 1) - u_ref (k + 1))
          + linResidual sys.g ((sys.computeGO x0 u_ref).x (k + 1)) (u_ref (k + 1))
            (x (k + 1)) (u (k + 1)) := by
      simp only [linResidual, NonlinearSysDT.computeGO]
      abel
    rw [hy, hs, Matrix.mulVec_add, Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
