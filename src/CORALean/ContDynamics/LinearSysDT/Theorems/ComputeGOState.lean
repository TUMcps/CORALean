module

public import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGO
public import CORALean.ContDynamics.LinearSysDT.Theorems.TrajectoryStateEq

@[expose] public section

/-!
# `computeGO` gives the state of every run

`x(k+1) = A{k} x(0) + ∑_j B{k,j} u(j)`, for every run of the system, whatever its sets: the
`A` and `B` of the GO model are exactly the coefficients of the closed form of the state.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.computeGO_state {sys : LinearSysDT 𝕋 n} {R₀ U : S n} {x u : ℕ → Vec ℝ n}
    (h : sys.Trajectory R₀ U x u) (out : OutputEq 𝕋 n n r) {nk : ℕ} (k : Fin nk) :
    x (k.val + 1) = (sys.computeGO out nk).A k *ᵥ x 0
      + ∑ j : Fin nk, (sys.computeGO out nk).B k j *ᵥ u j := by -- --- PROOF ---
  rw [h.state_eq (k.val + 1)]
  simp only [LinearSysDT.computeGO]
  congr 1
  -- the sum over `Fin nk` is a sum over `range nk`, and the guard keeps `j ≤ k`
  have h1 : ∑ j : Fin nk, (if j.val ≤ k.val then toRealMat sys.A ^ (k.val - j.val) else 0) *ᵥ u j
      = ∑ j ∈ Finset.range nk,
        if j ≤ k.val then toRealMat sys.A ^ (k.val - j) *ᵥ u j else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if j ≤ k.val
      then toRealMat sys.A ^ (k.val - j) *ᵥ u j else 0) nk]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [h1, ← Finset.sum_filter]
  have h2 : (Finset.range nk).filter (· ≤ k.val) = Finset.range (k.val + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h2]
  exact Finset.sum_congr rfl fun j _ => by simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
