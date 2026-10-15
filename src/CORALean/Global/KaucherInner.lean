module

public import CORALean.Global.CoordinatePath
public import CORALean.Global.Tensor
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The inner range of a flow component in Kaucher arithmetic

[1, Alg. 1, Step 3], (18): `]z[ = [z̃] + [J] * ([z̄₀, z̲₀] - z̃₀)` in Kaucher arithmetic, with
`[z̃] ∋ z(t, z̃₀)` and `[J] ∋ ∂z(t, ·)/∂z₀` on the initial box; if a component comes out
improper, its proper counterpart is in the range of that component of the flow. This is
[1, Thm. 1] (the generalized mean-value extension of Goldsztejn et al.) at the flow,
with an enclosure `[z̃]` for the center where the theorem has the point `f(x̃)`. Steps 1, 2
and 4, the Taylor-model enclosures, are hypotheses here: `φ` is the flow at time `t`.

The multiplication is the three cases [1, Sec. 2.3] lists for a proper factor and one in
`dual Z`, the Kaucher sum is endpoint-wise. The guarantee is per component, `pro ]z[ᵢ`
inside the `i`-th projection of the reachable set: the box of all components is not
inside it in general (the paper's page).

## References

* [1] E. Goubault and S. Putot. "Forward Inner-Approximated Reachability of Non-Linear
      Continuous Systems". In Proc. of the 20th International Conference on Hybrid Systems:
      Computation and Control (HSCC), pp. 1-10, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate's move gains at least the first endpoint of the Kaucher product, and
loses at most the second: `∂ⱼφᵢ ∈ [a, b]` on the box, moved from `x₀ⱼ` to its bound. -/
theorem aux_kaucher_gain {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) {lo hi : Fin n → ℝ}
    {a b : ℝ} (j : Fin n)
    (hab : ∀ y ∈ Icc lo hi, fderiv ℝ f y (Pi.single j 1) ∈ Icc a b) (p : Fin n → ℝ)
    (hp : p ∈ Icc lo hi) (s t : ℝ) (hs : s ∈ Icc (lo j) (hi j)) (ht : t ∈ Icc (lo j) (hi j))
    (hst : s ≤ t) :
    a * (t - s) ≤ f (Function.update p j t) - f (Function.update p j s) ∧
      f (Function.update p j t) - f (Function.update p j s) ≤ b * (t - s) := by -- --- PROOF ---
  set g : ℝ → ℝ := fun r => f (Function.update p j r)
  have hd : ∀ r, HasDerivAt g (fderiv ℝ f (Function.update p j r) (Pi.single j 1)) r :=
    fun r => hasDerivAt_comp_update hf p j r
  have hcont : ContinuousOn g (Icc (lo j) (hi j)) := fun r _ =>
    (hd r).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior (Icc (lo j) (hi j))) := fun r _ =>
    (hd r).differentiableAt.differentiableWithinAt
  have hbd : ∀ r ∈ interior (Icc (lo j) (hi j)), deriv g r ∈ Icc a b := fun r hr => by
    rw [(hd r).deriv]
    exact hab _ (update_mem_Icc hp j (interior_subset hr))
  exact ⟨(convex_Icc (lo j) (hi j)).mul_sub_le_image_sub_of_le_deriv hcont hdiff
      (fun r hr => (hbd r hr).1) s hs t ht hst,
    (convex_Icc (lo j) (hi j)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (fun r hr => (hbd r hr).2) s hs t ht hst⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 2.3]: the Kaucher product of a proper `[a, b]` with `[d₁, d₂]`, `d₁ ≥ 0 ≥ d₂`:
`P × dual Z`, `-P × dual Z` and `Z × dual Z`. -/
noncomputable def kaucherMulDualZ (a b d₁ d₂ : ℝ) : ℝ × ℝ :=
  if 0 ≤ a then (a * d₁, a * d₂)              -- [a, b] ∈ P
  else if b ≤ 0 then (b * d₂, b * d₁)         -- [a, b] ∈ -P
  else (0, 0)                                 -- [a, b] ∈ Z

/-- [1, Eq. 18], component `i`: `[z̲̃ᵢ, z̄̃ᵢ] + Σⱼ [J̲ᵢⱼ, J̄ᵢⱼ] × ([z̄₀ⱼ, z̲₀ⱼ] - z̃₀ⱼ)`. -/
noncomputable def kaucherInnerStep (zlo zhi : Fin n → ℝ) (Jlo Jhi : Mat ℝ n n)
    (lo hi z₀ : Fin n → ℝ) (i : Fin n) : ℝ × ℝ :=
  let d : Fin n → ℝ × ℝ := fun j => (hi j - z₀ j, lo j - z₀ j)    -- [z̄₀, z̲₀] - z̃₀, dual Z
  let prod : Fin n → ℝ × ℝ := fun j => kaucherMulDualZ (Jlo i j) (Jhi i j) (d j).1 (d j).2
  let sum : ℝ × ℝ := (∑ j, (prod j).1, ∑ j, (prod j).2)          -- Kaucher sum, endpoint-wise
  (zlo i + sum.1, zhi i + sum.2)                                -- [z̃]ᵢ + …, (18)

/-- [1, Alg. 1, Step 3]: the proper counterpart of `]z[ᵢ` is in the range of `φᵢ` over the
initial box (empty when `]z[ᵢ` is proper). -/
theorem kaucherInnerStep_inner {φ : (Fin n → ℝ) → (Fin n → ℝ)} (i : Fin n)
    (hφ : Differentiable ℝ fun z => φ z i) {lo hi z₀ : Fin n → ℝ} (hz₀ : z₀ ∈ Icc lo hi)
    {zlo zhi : Fin n → ℝ} (hz : φ z₀ i ∈ Icc (zlo i) (zhi i)) {Jlo Jhi : Mat ℝ n n}
    (hJ : ∀ j, ∀ y ∈ Icc lo hi, fderiv ℝ (fun z => φ z i) y (Pi.single j 1)
      ∈ Icc (Jlo i j) (Jhi i j)) :
    Icc (kaucherInnerStep zlo zhi Jlo Jhi lo hi z₀ i).2
        (kaucherInnerStep zlo zhi Jlo Jhi lo hi z₀ i).1
      ⊆ (fun z => φ z i) '' Icc lo hi := by -- --- PROOF ---
  set f : (Fin n → ℝ) → ℝ := fun z => φ z i
  -- each coordinate's target: up where `∂ⱼφᵢ ≥ 0`, down where `≤ 0`, kept otherwise
  let up : Fin n → ℝ := fun j =>
    if 0 ≤ Jlo i j then hi j else if Jhi i j ≤ 0 then lo j else z₀ j
  let dn : Fin n → ℝ := fun j =>
    if 0 ≤ Jlo i j then lo j else if Jhi i j ≤ 0 then hi j else z₀ j
  have hmem : ∀ (w : Fin n → ℝ), (∀ j, w j = hi j ∨ w j = lo j ∨ w j = z₀ j) →
      w ∈ Icc lo hi := fun w hw => ⟨fun j => by
        rcases hw j with h | h | h <;> rw [h] <;> linarith [hz₀.1 j, hz₀.2 j],
      fun j => by rcases hw j with h | h | h <;> rw [h] <;> linarith [hz₀.1 j, hz₀.2 j]⟩
  have hup : up ∈ Icc lo hi := hmem up fun j => by
    simp only [up]; split_ifs <;> simp
  have hdn : dn ∈ Icc lo hi := hmem dn fun j => by
    simp only [dn]; split_ifs <;> simp
  have hj : ∀ j, z₀ j ∈ Icc (lo j) (hi j) := fun j => ⟨hz₀.1 j, hz₀.2 j⟩
  have hl : ∀ j, lo j ∈ Icc (lo j) (hi j) := fun j => ⟨le_rfl, (hz₀.1 j).trans (hz₀.2 j)⟩
  have hh : ∀ j, hi j ∈ Icc (lo j) (hi j) := fun j => ⟨(hz₀.1 j).trans (hz₀.2 j), le_rfl⟩
  -- moving to `up` gains the first endpoints, moving to `dn` loses at most the second
  have hgain := le_of_coord_gain (f := f) hz₀ hup
    (fun j => (kaucherMulDualZ (Jlo i j) (Jhi i j) (hi j - z₀ j) (lo j - z₀ j)).1)
    fun j p hp => by
      have hk := aux_kaucher_gain hφ j (hJ j) p hp
      simp only [up, kaucherMulDualZ]
      split_ifs with h1 h2
      · linarith [(hk (z₀ j) (hi j) (hj j) (hh j) (hz₀.2 j)).1]
      · have := (hk (lo j) (z₀ j) (hl j) (hj j) (hz₀.1 j)).2; nlinarith
      · simp
  have hloss := le_of_coord_gain (f := fun z => -f z) hz₀ hdn
    (fun j => -(kaucherMulDualZ (Jlo i j) (Jhi i j) (hi j - z₀ j) (lo j - z₀ j)).2)
    fun j p hp => by
      have hk := aux_kaucher_gain hφ j (hJ j) p hp
      simp only [dn, kaucherMulDualZ]
      split_ifs with h1 h2
      · have := (hk (lo j) (z₀ j) (hl j) (hj j) (hz₀.1 j)).1; nlinarith
      · linarith [(hk (z₀ j) (hi j) (hj j) (hh j) (hz₀.2 j)).2]
      · simp
  simp only [Finset.sum_neg_distrib] at hloss
  -- the box is connected: every value between `f dn` and `f up` is taken
  refine fun z hzz => (convex_Icc lo hi).isPreconnected.intermediate_value hdn hup
    hφ.continuous.continuousOn ⟨?_, ?_⟩
  · simp only [kaucherInnerStep] at hzz
    linarith [hzz.1, hz.2]
  · simp only [kaucherInnerStep] at hzz
    linarith [hzz.2, hz.1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
