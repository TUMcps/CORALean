module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemBackReachAlignedSuccIff
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedInner

@[expose] public section

/-!
# An input from (16) steers `Z̲_{k+1}` into `Z̲_k` against every disturbance

[1, Sec. IV-B.2]: for `x ∈ Z̲_{k+1}` some `u ∈ U` has `Ax + Bu + K` in the generator-wise
difference `Z̲_k ⊖ Z(Z̲_k, EW)` — [1, Eq. 16]'s projected set, a linear program — and every such
`u` is in `U(x, Z̲_k)`: `Ax + Bu + Ew + K ∈ Z̲_k` for all `w ∈ W`. The hypothesis is (12)'s,
an aligned zonotope around `EW` with scalings in `[0, 1]`.

(16) writes the two sets of inputs as equal; only this inclusion holds, the aligned
zonotope being larger than `EW` in general (the paper's page). Iterated, the inputs
drive `x₀ ∈ Z̲_k` into `Z₀` in `k` steps (`backReachAligned_feedback`).

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

/-- [1, Sec. IV-B.2]: a state of `Z̲_{k+1}` has an input in (16)'s set, and every input
there keeps the next state in `Z̲_k` whatever the disturbance. -/
theorem LinearSysDT.backReachAligned_control {A : Mat ℝ n n} (hA : IsUnit A.det)
    (B : Mat ℝ n m) (E : Mat ℝ n p) (K : Vec ℝ n) (U : Zonotope (Vec ℝ m)) (W : Set (Vec ℝ p))
    (Z₀ : Zonotope (Vec ℝ n)) (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ))
    (hσ : ∀ Z, (∀ i, 0 ≤ (σ Z).2 i ∧ (σ Z).2 i ≤ 1) ∧
      (E *ᵥ ·) '' W ⊆ (Z.aligned (σ Z).1 (σ Z).2).construct) (k : ℕ) (x : Vec ℝ n)
    (hx : x ∈ (Zonotope.backReachAligned A B K U Z₀ σ (k + 1)).construct) :
    let Zk := Zonotope.backReachAligned A B K U Z₀ σ k
    (∃ u ∈ U.construct, A *ᵥ x + B *ᵥ u + K
      ∈ (Zk.minkDiffAligned (Zk.aligned (σ Zk).1 (σ Zk).2) rfl).construct) ∧
    ∀ u, A *ᵥ x + B *ᵥ u + K ∈ (Zk.minkDiffAligned (Zk.aligned (σ Zk).1 (σ Zk).2) rfl).construct →
      ∀ w ∈ W, A *ᵥ x + B *ᵥ u + E *ᵥ w + K ∈ Zk.construct := by -- --- PROOF ---
  intro Zk
  refine ⟨?_, fun u hu w hw => ?_⟩
  -- `Ax + K = d - Bu` for a point `d` of the difference
  · rw [Zonotope.mem_backReachAligned_succ_iff hA] at hx
    obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, hsum⟩ := hx
    refine ⟨u, hu, ?_⟩
    beta_reduce at hsum
    rwa [add_right_comm, ← hsum, Matrix.neg_mulVec, neg_add_cancel_right]
  -- the difference by an aligned zonotope around `EW` is inside `Z̲_k ⊖ EW`
  · have := Zk.minkDiffAligned_inner (Zk.aligned (σ Zk).1 (σ Zk).2) rfl (σ Zk).2
      (fun i => ((hσ Zk).1 i).1) (fun i => ((hσ Zk).1 i).2) (fun _ => rfl) hu (E *ᵥ w)
      ((hσ Zk).2 ⟨w, hw, rfl⟩)
    rwa [add_right_comm _ K] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
