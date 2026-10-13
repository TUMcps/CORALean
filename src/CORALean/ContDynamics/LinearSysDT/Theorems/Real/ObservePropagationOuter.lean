import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

/-!
# The set-propagation observer holds the true state

[1, Eq. 6] at any gains: every run `x_{k+1} = A x_k + u_k + w_k`, `w_k ∈ W`, with outputs
`y_k = C x_k + v_k`, `v_k ∈ V`, is in the observer's set at every step, provided `x_0 ∈ S_0`.
The true state satisfies `x_{k+1} = (A - L C) x_k + u_k + L y_k + (-L) v_k + w_k`, a point of
each summand of [1, Eq. 6]. [1] states the condition as `x̂_0 ∈ S_0` with `0 ∈ V`, `0 ∈ W`; the
estimate's start says nothing of the true state's, and the origin is not needed: what the
induction uses is `x_0 ∈ S_0`.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observePropagation_outer (sys : LinearSysDT ℝ n) (C : Mat ℝ p n)
    (gain : Zonotope (Vec ℝ n) → Mat ℝ n p) (order : ℕ) (W R₀ : Zonotope (Vec ℝ n))
    (V : Zonotope (Vec ℝ p)) (u : ℕ → Vec ℝ n) (y : ℕ → Vec ℝ p) (x w : ℕ → Vec ℝ n)
    (v : ℕ → Vec ℝ p) (h0 : x 0 ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hv : ∀ k, v k ∈ V.construct) (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + u k + w k)
    (hy : ∀ k, y k = C *ᵥ x k + v k) (k : ℕ) :
    x k ∈ (sys.observePropagation C gain order W R₀ V u y k).construct := by -- --- PROOF ---
  induction k with
  | zero => exact h0
  | succ k ih =>
    set S := sys.observePropagation C gain order W R₀ V u y k
    set L := gain S
    -- the true state, one point of each summand of (6)
    have heq : x (k + 1) =
        (sys.A - L * C) *ᵥ x k + u k + L *ᵥ y k + (-L) *ᵥ v k + w k := by
      rw [hstep, hy, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
        Matrix.neg_mulVec]
      abel
    have h1 : (sys.A - L * C) *ᵥ x k ∈ (Zonotope.mtimes (sys.A - L * C) S).construct := by
      rw [← Zonotope.mtimes_exact]; exact ⟨x k, ih, rfl⟩
    have h4 : (-L) *ᵥ v k ∈ (Zonotope.mtimes (-L) V).construct := by
      rw [← Zonotope.mtimes_exact]; exact ⟨v k, hv k, rfl⟩
    show x (k + 1) ∈ (Zonotope.reduce (((((Zonotope.mtimes (sys.A - L * C) S).plus
      (Zonotope.ofPoint (u k))).plus (Zonotope.ofPoint (L *ᵥ y k))).plus
      (Zonotope.mtimes (-L) V)).plus W) order).construct
    refine Zonotope.reduce_outer _ _ ?_
    rw [heq, ← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.plus_exact,
      ← Zonotope.plus_exact]
    exact Set.add_mem_add (Set.add_mem_add (Set.add_mem_add (Set.add_mem_add h1
      (Zonotope.mem_ofPoint _)) (Zonotope.mem_ofPoint _)) h4) (hw k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
