import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachSetRobustSucc
import CORALean.ContSet.Zonotope.Real.Theorems.MemBackReachAlignedSuccIff
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedInner
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffMono

/-!
# (12) runs inside the robust backward reachable sets

[1, Prop. 5], the inner half: `Z̲_k ⊆ X_k` when every step's aligned zonotope is around
`EW` with scalings in `[0, 1]` — what a feasible point of (min-out) gives
(`Zonotope.image_subset_aligned_of_minOut`). By induction, as in [1]: the step's
difference is inside `Z̲_k ⊖ EW ⊆ X_k ⊖ EW`, and [1, Eq. 4] reads the rest. `A` is
invertible, [1]'s assumption A3.

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

/-- [1, Prop. 5], `Z̲_k ⊆ X_k`: with an aligned zonotope around `EW` at every step, the
recursion stays inside the robust backward reachable set. -/
theorem LinearSysDT.backReachAligned_inner {A : Mat ℝ n n} (hA : IsUnit A.det) (B : Mat ℝ n m)
    (E : Mat ℝ n p) (K : Vec ℝ n) (U : Zonotope (Vec ℝ m)) (W : Set (Vec ℝ p))
    (Z₀ : Zonotope (Vec ℝ n)) (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ))
    (hσ : ∀ Z, (∀ i, 0 ≤ (σ Z).2 i ∧ (σ Z).2 i ≤ 1) ∧
      (E *ᵥ ·) '' W ⊆ (Z.aligned (σ Z).1 (σ Z).2).construct) (k : ℕ) :
    (Zonotope.backReachAligned A B K U Z₀ σ k).construct
      ⊆ LinearSysDT.backReachSetRobust A B E K U.construct W Z₀.construct k := by -- --- PROOF ---
  induction k with
  | zero => exact subset_rfl
  | succ k ih =>
    intro x hx
    rw [Zonotope.mem_backReachAligned_succ_iff hA] at hx
    obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, hsum⟩ := hx
    set Zk := Zonotope.backReachAligned A B K U Z₀ σ k
    -- the difference by the aligned zonotope is inside `X_k ⊖ EW`
    have hdiff : d ∈ minkowskiDiff (LinearSysDT.backReachSetRobust A B E K U.construct W
        Z₀.construct k) ((E *ᵥ ·) '' W) :=
      minkowskiDiff_mono ih (hσ Zk).2 (Zk.minkDiffAligned_inner (Zk.aligned (σ Zk).1 (σ Zk).2)
        rfl (σ Zk).2 (fun i => ((hσ Zk).1 i).1) (fun i => ((hσ Zk).1 i).2) (fun _ => rfl) hd)
    rw [LinearSysDT.backReachSetRobust_succ, Set.mem_preimage]
    refine ⟨_, ⟨d, hdiff, -(B *ᵥ u), ⟨u, hu, rfl⟩, rfl⟩, -K, rfl, ?_⟩
    beta_reduce at hsum ⊢
    rw [← Matrix.neg_mulVec, hsum, add_neg_cancel_right]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
