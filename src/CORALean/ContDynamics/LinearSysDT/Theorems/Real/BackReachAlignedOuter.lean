module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachSetRobustSucc
public import CORALean.ContSet.Zonotope.Real.Theorems.MemBackReachAlignedSuccIff
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedExact
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono

@[expose] public section

/-!
# (13) runs around the robust backward reachable sets

[1, Prop. 5], the outer half: `X_k ⊆ Z̄_k` when every step's aligned zonotope is inside
`EW` with scalings in `[0, 1]`. That is what (max-in) gives when its halfspaces are
`EW`'s (`Zonotope.aligned_subset_of_maxIn`); with `W`'s, as [1] builds (max-in), the
step can cut off part of `X_k` (`aligned_subset_of_maxIn_counterexample`). The
difference by the aligned zonotope is exact ([1, Prop. 3]), so `X_k ⊖ EW ⊆ Z̄_k ⊖ EW`
is inside it. `A` is invertible, [1]'s assumption A3.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise

variable {n m p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 5], `X_k ⊆ Z̄_k`: with an aligned zonotope inside `EW` at every step, the
recursion encloses the robust backward reachable set. -/
theorem LinearSysDT.backReachAligned_outer {A : Mat ℝ n n} (hA : IsUnit A.det) (B : Mat ℝ n m)
    (E : Mat ℝ n p) (K : Vec ℝ n) (U : Zonotope (Vec ℝ m)) (W : Set (Vec ℝ p))
    (Z₀ : Zonotope (Vec ℝ n)) (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ))
    (hσ : ∀ Z, (∀ i, 0 ≤ (σ Z).2 i ∧ (σ Z).2 i ≤ 1) ∧
      (Z.aligned (σ Z).1 (σ Z).2).construct ⊆ (E *ᵥ ·) '' W) (k : ℕ) : -- --- STMT ---
    LinearSysDT.backReachSetRobust A B E K U.construct W Z₀.construct k
      ⊆ (Zonotope.backReachAligned A B K U Z₀ σ k).construct := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    intro x hx
    rw [LinearSysDT.backReachSetRobust_succ, Set.mem_preimage] at hx
    obtain ⟨_, ⟨d, hd, _, ⟨u, hu, rfl⟩, rfl⟩, _, rfl, hsum⟩ := hx
    rw [Zonotope.mem_backReachAligned_succ_iff hA]
    set Zk := Zonotope.backReachAligned A B K U Z₀ σ k
    -- `X_k ⊖ EW ⊆ Z̄_k ⊖ EW ⊆ Z̄_k ⊖ Z(Z̄_k, EW)`, which the generator-wise difference is
    have hdiff : d ∈ (Zk.minkDiffAligned (Zk.aligned (σ Zk).1 (σ Zk).2) rfl).construct := by
      rw [Zk.minkDiffAligned_exact (Zk.aligned (σ Zk).1 (σ Zk).2) rfl (σ Zk).2
        (fun i => ((hσ Zk).1 i).1) (fun i => ((hσ Zk).1 i).2) (fun _ => rfl)]
      exact minkowskiDiff_mono ih (hσ Zk).2 hd
    refine ⟨d, hdiff, (-B) *ᵥ u, ⟨u, hu, rfl⟩, ?_⟩
    beta_reduce at hsum ⊢
    rw [← hsum, Matrix.neg_mulVec, neg_add_cancel_right]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
