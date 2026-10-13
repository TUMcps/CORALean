module

public import CORALean.ContDynamics.LinearSysDT.Operations.ComputeGO
public import CORALean.ContDynamics.LinearSysDT.Theorems.TrajectoryStateEq

@[expose] public section

/-!
# `computeGO` gives the output of every run

`y(k) = C{k} x(0) + ∑_j D{k,j} u(j)`, with `y(k) = C x(k) + D u(k)` the output equation: the
`C` and `D` of the GO model are the coefficients of the output in the initial state and the
inputs, for every run of the system.
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

theorem LinearSysDT.computeGO_output {sys : LinearSysDT 𝕋 n} {R₀ U : S n} {x u : ℕ → Vec ℝ n}
    (h : sys.Trajectory R₀ U x u) (out : OutputEq 𝕋 n n r) {nk : ℕ} (k : Fin nk) :
    out.eval (x k.val) (u k.val) = (sys.computeGO out nk).C k *ᵥ x 0
      + ∑ j : Fin nk, (sys.computeGO out nk).D k j *ᵥ u j := by -- --- PROOF ---
  -- the output is `C x(k) + D u(k)`, with `x(k)` in closed form
  simp only [OutputEq.eval, LinearSysDT.computeGO]
  rw [h.state_eq k.val, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_sum]
  -- each term of `D k j` splits into the strictly-past part and the feedthrough
  have h1 : ∀ j : Fin nk, (if j = k then toRealMat out.D
        else if j.val < k.val then toRealMat out.C * toRealMat sys.A ^ (k.val - 1 - j.val)
        else 0) *ᵥ u j
      = (if j.val < k.val then
          toRealMat out.C *ᵥ (toRealMat sys.A ^ (k.val - 1 - j.val) *ᵥ u j) else 0)
        + (if j = k then toRealMat out.D *ᵥ u j else 0) := fun j => by
    by_cases hjk : j = k
    · subst hjk; simp
    · have : ¬ j.val = k.val := fun e => hjk (Fin.ext e)
      by_cases hlt : j.val < k.val <;> simp [hjk, hlt, Matrix.mulVec_mulVec]
  -- sum the two parts: the feedthrough is the single term `j = k`
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ k]
  simp only [Finset.mem_univ, if_true]
  have h2 : ∑ j : Fin nk, (if j.val < k.val then
        toRealMat out.C *ᵥ (toRealMat sys.A ^ (k.val - 1 - j.val) *ᵥ u j) else 0)
      = ∑ j ∈ Finset.range k.val,
        toRealMat out.C *ᵥ (toRealMat sys.A ^ (k.val - 1 - j) *ᵥ u j) := by
    have hf : (Finset.range nk).filter (· < k.val) = Finset.range k.val := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have := k.isLt
      omega
    rw [← hf, Finset.sum_filter,
      ← Fin.sum_univ_eq_sum_range (fun j => if j < k.val then
        toRealMat out.C *ᵥ (toRealMat sys.A ^ (k.val - 1 - j) *ᵥ u j) else 0) nk]
  rw [h2]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
