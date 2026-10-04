import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The state of a run in closed form

`x(k) = Aᵏ x(0) + ∑_{j<k} A^{k-1-j} u(j)`, the variation-of-constants formula the GO
parameters of `computeGO` tabulate.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.Trajectory.state_eq {sys : LinearSysDT 𝕋 n} {R₀ U : S n}
    {x u : ℕ → Vec ℝ n} (h : sys.Trajectory R₀ U x u) (k : ℕ) :
    x k = toRealMat sys.A ^ k *ᵥ x 0
      + ∑ j ∈ Finset.range k, toRealMat sys.A ^ (k - 1 - j) *ᵥ u j := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [h.step k, ih, Matrix.mulVec_add, Matrix.mulVec_sum, Finset.sum_range_succ,
      Matrix.mulVec_mulVec, ← pow_succ']
    have hs : ∀ j ∈ Finset.range k, toRealMat sys.A *ᵥ (toRealMat sys.A ^ (k - 1 - j) *ᵥ u j)
        = toRealMat sys.A ^ (k + 1 - 1 - j) *ᵥ u j := fun j hj => by
      have hj := Finset.mem_range.mp hj
      rw [Matrix.mulVec_mulVec, ← pow_succ']
      congr 3
      omega
    rw [Finset.sum_congr rfl hs]
    simp [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
