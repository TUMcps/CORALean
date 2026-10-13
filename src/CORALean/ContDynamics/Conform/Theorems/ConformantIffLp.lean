import CORALean.ContDynamics.Conform.Theorems.ConformantIffDevSet
import CORALean.ContDynamics.Conform.Theorems.DevSetTemplateZono
import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIff

/-!
# [2, Thm. 1]: the linear program's constraints are exactly reachset conformance

`X̃₀`, `W` and `V` stretched templates [2, Eq. 9], `z = (c, α)` (14). A point `z`
with `α ≥ 0` satisfies (12)'s `Ã z ≤ b̃` — row `k`:
`max_y N(t_k)(y - ỹ) ≤ N(t_k) Γ(t_k) c + G̃(N(t_k), t_k) α`, (18)-(20) with the
signs moved across — exactly when (8) holds at every `k ≤ K`, i.e. every measurement lies
in its test case's reachable set. Both directions: the program's feasible set is the
set of conformant parameters, so its optimum (`n^T z`, `LpCostEq`) is the cost's minimum
over conformant models — what the solver then returns is the solver's.

`N(t_k)` is any family carrying both signs of every cross product of the template
`[Λ_k G_X, Λ₀ G_W ⋯ Λ_{k-1} G_W, G_V]`, which must span the output space. The printed
proof takes the normals of `G(t_k)` itself, citing [1, Thm. 1] for their independence of
`α`; that independence fails where some `αᵢ = 0`, which the program allows. The statement
holds there too (`Zonotope.mem_scale_iff`).

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One row of `Ã(t_k) z ≤ b̃(t_k)`, the offset split into (20)'s three blocks. -/
theorem aux_lp_row_iff (sys : Conform.Plant n p (q + 1)) {ιX ιW ιV : Type} [Fintype ιX]
    [Fintype ιW] [Fintype ιV] (cX : Vec ℝ n) (GX : ιX → Vec ℝ n) (αX : ιX → ℝ)
    (cW : Vec ℝ n) (GW : ιW → Vec ℝ n) (αW : ιW → ℝ) (cV : Vec ℝ (q + 1))
    (GV : ιV → Vec ℝ (q + 1)) (αV : ιV → ℝ) (k : ℕ) (v y : Vec ℝ (q + 1)) :
    v ⬝ᵥ (y - ((sys.C * sys.A ^ k) *ᵥ cX + ∑ i : Fin k, (sys.C * sys.A ^ (i : ℕ)) *ᵥ cW + cV))
        ≤ ∑ j, |v ⬝ᵥ Sum.elim (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
            (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV j|
          * Sum.elim (Sum.elim αX fun r => αW r.2) αV j ↔
      v ⬝ᵥ y ≤ v ⬝ᵥ ((sys.C * sys.A ^ k) *ᵥ cX)
        + (∑ i : Fin k, v ⬝ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ cW)) + v ⬝ᵥ cV
        + ∑ x, |v ⬝ᵥ ((sys.C * sys.A ^ k) *ᵥ GX x)| * αX x
        + ∑ r, (∑ i : Fin k, |v ⬝ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r)|) * αW r
        + ∑ l, |v ⬝ᵥ GV l| * αV l := by -- --- PROOF ---
  have hoff : ∑ j, |v ⬝ᵥ Sum.elim (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
        (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV j|
        * Sum.elim (Sum.elim αX fun r => αW r.2) αV j
      = ∑ x, |v ⬝ᵥ ((sys.C * sys.A ^ k) *ᵥ GX x)| * αX x
        + ∑ r, (∑ i : Fin k, |v ⬝ᵥ ((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r)|) * αW r
        + ∑ l, |v ⬝ᵥ GV l| * αV l := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
      Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin k))]
  rw [hoff, dotProduct_sub, dotProduct_add, dotProduct_add, dotProduct_sum]
  constructor <;> intro h <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [2, Thm. 1]: a point `z = (c, α)`, `α ≥ 0`, meets every constraint of (12)
exactly when the model is reachset conformant up to `K`, i.e. [2, Eq. 8] at every step. -/
theorem Conform.Plant.conformant_iff_lp {M κ : Type} (sys : Conform.Plant n p (q + 1))
    {ιX ιW ιV : Type} [Fintype ιX] [Fintype ιW] [Fintype ιV] (cX : Vec ℝ n)
    (GX : ιX → Vec ℝ n) (αX : ιX → ℝ) (cW : Vec ℝ n) (GW : ιW → Vec ℝ n) (αW : ιW → ℝ)
    (cV : Vec ℝ (q + 1)) (GV : ιV → Vec ℝ (q + 1)) (αV : ιV → ℝ) (hαX : ∀ x, 0 ≤ αX x)
    (hαW : ∀ r, 0 ≤ αW r) (hαV : ∀ l, 0 ≤ αV l) (T : M → Conform.TestCase n p (q + 1))
    (K : ℕ) (N : ℕ → κ → Vec ℝ (q + 1))
    (hspan : ∀ k ≤ K, Submodule.span ℝ (Set.range (Sum.elim
      (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
        (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV)) = ⊤)
    (hN : ∀ k ≤ K, Conform.HasNormals (Sum.elim
      (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
        (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV) (N k)) :
    sys.Conformant (Conform.templateZono cX GX αX) (Conform.templateZono cW GW αW)
        (Conform.templateZono cV GV αV) T K ↔
      ∀ k ≤ K, ∀ m, ∀ i, N k i ⬝ᵥ ((T m).y k - sys.nominal (T m).x0 (T m).u k)
        ≤ N k i ⬝ᵥ ((sys.C * sys.A ^ k) *ᵥ cX)
          + (∑ j : Fin k, N k i ⬝ᵥ ((sys.C * sys.A ^ (j : ℕ)) *ᵥ cW)) + N k i ⬝ᵥ cV
          + ∑ x, |N k i ⬝ᵥ ((sys.C * sys.A ^ k) *ᵥ GX x)| * αX x
          + ∑ r, (∑ j : Fin k, |N k i ⬝ᵥ ((sys.C * sys.A ^ (j : ℕ)) *ᵥ GW r)|) * αW r
          + ∑ l, |N k i ⬝ᵥ GV l| * αV l := by -- --- PROOF ---
  rw [sys.conformant_iff_devSet]
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  rw [sys.devSet_templateZono, Set.iUnion_subset_iff]
  refine forall_congr' fun m => ?_
  rw [Set.singleton_subset_iff, Conform.mem_templateZono_iff _ _ (hspan k hk) (N k) (hN k hk)
    _ (fun j => by rcases j with (x | r) | l <;> simp [hαX, hαW, hαV])]
  exact forall_congr' fun i => aux_lp_row_iff sys cX GX αX cW GW αW cV GV αV k (N k i) _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
