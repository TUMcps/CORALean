module

public import CORALean.ContDynamics.Conform.Theorems.ConformantIffDevSet
public import CORALean.ContDynamics.Conform.Theorems.DevSetZeroTemplateZono
public import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIff

@[expose] public section

/-!
# [1, Thm. 1]: reachset conformance is linear in the identified parameters

For `W = ⟨c_W, G'_W diag(α_W)⟩` and `V = ⟨c_V, G'_V diag(α_V)⟩`, the model is conformant on
the test cases up to `K` exactly when, for every step `k`, test case `m` and row `n` of
`N_k`, `n y_a⁽ᵐ⁾(k) ≤ [∑ᵢ n Eᵢ, n, ∑ᵢ |n Eᵢ G'_W|, |n G'_V|] ξ` — (19), linear in
`ξ = (c_W, c_V, α_W, α_V)`. The maximum over `m` there is the conjunction here.

`N_k` is any family carrying both signs of every cross-product normal of `R_a(k)`'s
template `[E₀ G'_W ⋯ E_{k-1} G'_W  G'_V]` — so fixed before `ξ` is — and that template must
span the output space, which [1, Prop. 1] needs and the theorem leaves implicit. The
printed proof cancels `det(diag(α))` and so needs `α > 0`; this holds at `α ≥ 0`, the
template's normals still describing a zonotope one of whose generators has vanished
(`Zonotope.mem_scale_iff`).

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One halfspace of `R_a(k)`, its offset split into (19)'s four blocks. -/
theorem aux_row_iff (sys : Conform.Plant n p (q + 1)) {ιW ιV : Type} [Fintype ιW]
    [Fintype ιV] (cW : Vec ℝ n) (GW : ιW → Vec ℝ n) (αW : ιW → ℝ) (cV : Vec ℝ (q + 1))
    (GV : ιV → Vec ℝ (q + 1)) (αV : ιV → ℝ) (k : ℕ) (v y : Vec ℝ (q + 1)) :
    v ⬝ᵥ (y - (∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ cW + cV))
        ≤ ∑ j, |v ⬝ᵥ Sum.elim (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)
            GV j| * Sum.elim (fun r => αW r.2) αV j ↔
      v ⬝ᵥ y ≤ (∑ i : Fin k, v ⬝ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ cW)) + v ⬝ᵥ cV
        + ∑ r, (∑ i : Fin k, |v ⬝ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r)|) * αW r
        + ∑ l, |v ⬝ᵥ GV l| * αV l := by -- --- PROOF ---
  have hoff : ∑ j, |v ⬝ᵥ Sum.elim (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)
        GV j| * Sum.elim (fun r => αW r.2) αV j
      = ∑ r, (∑ i : Fin k, |v ⬝ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r)|) * αW r
        + ∑ l, |v ⬝ᵥ GV l| * αV l := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hoff, dotProduct_sub, dotProduct_add, dotProduct_sum]
  constructor <;> intro h <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: conformance up to `K` is (19), linear in `(c_W, c_V, α_W, α_V)`. -/
theorem Conform.Plant.conformant_iff_hRep {M κ : Type} (sys : Conform.Plant n p (q + 1))
    {ιW ιV : Type} [Fintype ιW] [Fintype ιV] (cW : Vec ℝ n) (GW : ιW → Vec ℝ n)
    (αW : ιW → ℝ) (cV : Vec ℝ (q + 1)) (GV : ιV → Vec ℝ (q + 1)) (αV : ιV → ℝ)
    (hαW : ∀ r, 0 ≤ αW r) (hαV : ∀ l, 0 ≤ αV l) (T : M → Conform.TestCase n p (q + 1)) (K : ℕ)
    (N : ℕ → κ → Vec ℝ (q + 1))
    (hspan : ∀ k ≤ K, Submodule.span ℝ (Set.range
      (Sum.elim (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2) GV)) = ⊤)
    (hN : ∀ k ≤ K, Conform.HasNormals
      (Sum.elim (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2) GV) (N k)) :
    sys.Conformant {0} (Conform.templateZono cW GW αW) (Conform.templateZono cV GV αV) T K ↔
      ∀ k ≤ K, ∀ m, ∀ i, N k i ⬝ᵥ ((T m).y k - sys.nominal (T m).x0 (T m).u k)
        ≤ (∑ j : Fin k, N k i ⬝ᵥ ((sys.C * sys.A ^ (j : ℕ)) *ᵥ cW)) + N k i ⬝ᵥ cV
          + ∑ r, (∑ j : Fin k, |N k i ⬝ᵥ ((sys.C * sys.A ^ (j : ℕ)) *ᵥ GW r)|) * αW r
          + ∑ l, |N k i ⬝ᵥ GV l| * αV l := by -- --- PROOF ---
  rw [sys.conformant_iff_devSet]
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  rw [sys.devSet_zero_templateZono, Set.iUnion_subset_iff]
  refine forall_congr' fun m => ?_
  rw [Set.singleton_subset_iff, Conform.mem_templateZono_iff _ _ (hspan k hk) (N k) (hN k hk)
    _ (fun j => by cases j with
      | inl r => exact hαW r.2
      | inr l => exact hαV l)]
  exact forall_congr' fun i => aux_row_iff sys cW GW αW cV GV αV k (N k i) _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
