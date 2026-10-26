module

public import CORALean.Global.InnerRangeTest
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# (5) does not give condition (i) on the whole of `∂u`

The proof of [1, Cor. 3.1] derives (i) of [1, Thm. 3.1], `y₁ ∩ f₁:ᵣ(∂u) = ∅`, from (5): a
point `u ∈ ∂u` with `f₁:ᵣ(u) ∈ y₁` would put `u₁ ∈ H` "and `u₁ ∈ ∂u₁`". When `m > r` a point of
`∂u` may have `u₂` at a bound and `u₁` interior. For `f(x₁, x₂) = x₁` on `[-1, 1]²`, `ũ = 0`,
the point intervals `J₁ = 1`, `J₂ = 0` and `y₁ = [-1/2, 1/2]`, `H = y₁ ⊆ int([-1, 1])`, so (5)
holds, while `(0, 1) ∈ ∂u` is mapped into `y₁`. The corollary itself holds
(`Icc_subset_image_of_innerTest`, through the slice at `ũ₂`); this is the step.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* condition (5) holds while condition (i) fails at a boundary point

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The constant `1` is on the frontier of `[-1, 1]` in `ℝ¹`. -/
private theorem aux_one_mem_frontier : -- --- CONCL ---
    (fun _ => (1 : ℝ)) ∈
      frontier (Icc (fun _ : Fin 1 => (-1 : ℝ)) fun _ => 1) := by -- --- PROOF ---
  -- the frontier of a closed box is what its interior, the open box, leaves out
  rw [isClosed_Icc.frontier_eq]
  refine ⟨⟨fun _ => by norm_num, fun _ => le_rfl⟩, fun hint => ?_⟩
  rw [← pi_univ_Icc, interior_pi_set finite_univ] at hint
  have h0 := hint 0 trivial
  rw [interior_Icc] at h0
  exact lt_irrefl _ h0.2


-- =======================================  MAIN THEOREM  ======================================= --

/-- (5) holds for `f(x₁, x₂) = x₁` on `[-1, 1]²` and `y₁ = [-1/2, 1/2]`, and (i) does not. -/
theorem innerTest_step_counterexample : -- --- CONCL ---
    let g : (Fin 1 → ℝ) × (Fin 1 → ℝ) → (Fin 1 → ℝ) := fun x => x.1
    let lo : Fin 1 → ℝ := fun _ => -1
    let hi : Fin 1 → ℝ := fun _ => 1
    PassesInnerTest g 0 lo hi lo hi (Matrix.of fun _ _ => 1) (Matrix.of fun _ _ => 1) 0 0
        (fun _ => -1 / 2) (fun _ => 1 / 2) ∧
      ¬ Disjoint (Icc (fun _ => -1 / 2) fun _ => 1 / 2)
        (g '' frontier (Icc lo hi ×ˢ Icc lo hi)) := by -- --- PROOF ---
  intro g lo hi
  refine ⟨?_, fun hdis => ?_⟩
  · -- `H = ũ₁ + (y - 0 - 0 - 0) / 1 = y`
    intro y hy J₁ hJ₁ J₂ hJ₂ v _ w _ i
    have h1 : J₁ i i = 1 := by
      have := hJ₁ i i
      simp only [Matrix.of_apply, mem_Icc] at this
      exact le_antisymm this.2 this.1
    have h2 : ∀ l, J₂ i l = 0 := fun l => le_antisymm (hJ₂ i l).2 (hJ₂ i l).1
    have he : Finset.univ.erase i = ∅ := by
      ext j
      simp [Fin.fin_one_eq_zero j, Fin.fin_one_eq_zero i]
    simp only [he, Finset.sum_empty, h1, h2, zero_mul, Finset.sum_const_zero, sub_zero, div_one]
    simp only [g, Prod.fst_zero, Pi.zero_apply, zero_add]
    exact ⟨by linarith [(hy.1 i : -1 / 2 ≤ y i)], by linarith [(hy.2 i : y i ≤ 1 / 2)]⟩
  · -- `(0, 1)` is on the frontier of the box, and `g(0, 1) = 0 ∈ y₁`
    have hfr : ((fun _ => (0 : ℝ)), (fun _ => (1 : ℝ))) ∈ frontier (Icc lo hi ×ˢ Icc lo hi) := by
      rw [frontier_prod_eq]
      exact Or.inl ⟨subset_closure ⟨fun _ => by norm_num [lo], fun _ => by norm_num [hi]⟩,
        aux_one_mem_frontier⟩
    exact disjoint_left.mp hdis ⟨fun _ => by norm_num, fun _ => by norm_num⟩ ⟨_, hfr, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
