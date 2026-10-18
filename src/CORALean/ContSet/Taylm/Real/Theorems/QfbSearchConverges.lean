module

public import CORALean.ContSet.Taylm.Real.Theorems.QfbSearchStepFixedIsMinOn
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# The search for `x₀` determines the minimizer of `P₂`

[1, Sec. 3 (search for x₀)]: "for a given `P₂` in `D`, `x₀` can be determined inexpensively by an
iterative scheme to search a series of `x₀⁽ⁱ⁾` in the direction of `-∇P₂` while limiting `x₀⁽ⁱ⁾` to
stay inside `D`", the `x₀` sought being the minimizer of `P₂` in `D`. For `H` positive semidefinite
and a step `α` with `α v ⬝ Hv ≤ v ⬝ v`, the series from any start in the box has a limit point,
every limit point minimizes `P₂` on the box, and `P₂(x₀⁽ⁱ⁾)` tends to that minimum.

The argument is the projected-gradient one. The projection property gives the descent
`2α P₂(x⁺) + ‖x⁺ - x‖² ≤ 2α P₂(x)`, so the steps are square-summable and tend to `0`. The box is
compact, so a subsequence converges, and by continuity its limit is a fixed point of the step,
which is a minimizer (`qfbSearchStep_fixed_isMinOn`). `P₂(x₀⁽ⁱ⁾)` falls monotonically, so it
converges, and to the value at that limit.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Filter Topology

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step decreases `P₂` by at least `‖x⁺ - x‖² / (2α)`. -/
theorem Taylm.aux_qfbSearchStep_descent {H : Mat ℝ n n} (hH : H.IsSymm) (c : ℝ) (g : Vec ℝ n)
    {α L : ℝ} (hα : 0 < α) (hL : ∀ v : Vec ℝ n, v ⬝ᵥ (H *ᵥ v) ≤ L * (v ⬝ᵥ v))
    (hαL : α * L ≤ 1) {x : Vec ℝ n} (hx : x ∈ Taylm.box n) : -- --- STMT ---
    2 * α * (c + g ⬝ᵥ Taylm.qfbSearchStep H g α x
        + Taylm.qfbSearchStep H g α x ⬝ᵥ (H *ᵥ Taylm.qfbSearchStep H g α x) / 2)
      + (Taylm.qfbSearchStep H g α x - x) ⬝ᵥ (Taylm.qfbSearchStep H g α x - x)
      ≤ 2 * α * (c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2) := by -- --- PROOF ---
  set d := Taylm.qfbSearchStep H g α x - x with hd
  have hxd : Taylm.qfbSearchStep H g α x = x + d := by rw [hd, add_sub_cancel]
  -- the projection property at `z = x`: `d ⬝ d + α ∇ ⬝ d ≤ 0`
  have hv := (Taylm.qfbSearchStep_variational H g α x).2 x hx
  have h1 : d ⬝ᵥ d + α * ((g + H *ᵥ x) ⬝ᵥ d) ≤ 0 := by
    have e1 : x - α • (g + H *ᵥ x) - Taylm.qfbSearchStep H g α x = -d - α • (g + H *ᵥ x) := by
      rw [hxd]; abel
    have e2 : x - Taylm.qfbSearchStep H g α x = -d := by rw [hxd]; abel
    rw [e1, e2] at hv
    simp only [sub_dotProduct, neg_dotProduct, dotProduct_neg, smul_dotProduct, smul_eq_mul,
      dotProduct_comm (g + H *ᵥ x) d] at hv ⊢
    linarith
  have hdd : 0 ≤ d ⬝ᵥ d := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 := mul_le_mul_of_nonneg_left (hL d) hα.le
  have h3 : α * L * (d ⬝ᵥ d) ≤ d ⬝ᵥ d := by nlinarith
  rw [hxd, Taylm.qfb_quad_expand hH c g x d]
  nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (search for x₀)]: the search from any `x₀⁽⁰⁾` in the box has a subsequence converging
to a minimizer `x*` of `P₂` on the box, and `P₂(x₀⁽ⁱ⁾) → P₂(x*)`. -/
theorem Taylm.qfbSearch_converges {H : Mat ℝ n n} (hH : H.IsSymm) (hP : H.PosSemidef) (c : ℝ)
    (g : Vec ℝ n) {α L : ℝ} (hα : 0 < α) (hL : ∀ v : Vec ℝ n, v ⬝ᵥ (H *ᵥ v) ≤ L * (v ⬝ᵥ v))
    (hαL : α * L ≤ 1) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ Taylm.box n) : -- --- STMT ---
    ∃ xs ∈ Taylm.box n, IsMinOn (fun x => c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2) (Taylm.box n) xs ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => (Taylm.qfbSearchStep H g α)^[φ j] x₀) atTop (𝓝 xs)) ∧
      Tendsto (fun i => c + g ⬝ᵥ (Taylm.qfbSearchStep H g α)^[i] x₀
          + (Taylm.qfbSearchStep H g α)^[i] x₀ ⬝ᵥ (H *ᵥ (Taylm.qfbSearchStep H g α)^[i] x₀) / 2)
        atTop (𝓝 (c + g ⬝ᵥ xs + xs ⬝ᵥ (H *ᵥ xs) / 2)) := by -- --- PROOF ---
  set S := Taylm.qfbSearchStep H g α with hS
  set f : Vec ℝ n → ℝ := fun x => c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2 with hf
  set xs : ℕ → Vec ℝ n := fun i => S^[i] x₀ with hxs
  have hsucc : ∀ i, xs (i + 1) = S (xs i) := fun i => Function.iterate_succ_apply' S i x₀
  -- every iterate stays in the box
  have hbox : ∀ i, xs i ∈ Taylm.box n := by
    intro i
    induction i with
    | zero => exact hx₀
    | succ i _ => rw [hsucc]; exact (Taylm.qfbSearchStep_variational H g α _).1
  -- the box is compact and nonempty, `f` continuous: a minimum `m` exists
  have hcpt : IsCompact (Taylm.box n) := by
    have : Taylm.box n = Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 1 := by
      ext t
      exact ⟨fun h k _ => abs_le.mp (h k), fun h k => abs_le.mpr (h k (Set.mem_univ k))⟩
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hfc : Continuous f := by simp only [hf, dotProduct, mulVec]; fun_prop
  obtain ⟨xm, -, hxm⟩ := hcpt.exists_isMinOn ⟨x₀, hx₀⟩ hfc.continuousOn
  -- the descent, read along the iterates
  set dd : ℕ → ℝ := fun i => (xs (i + 1) - xs i) ⬝ᵥ (xs (i + 1) - xs i) with hdd
  have hdesc : ∀ i, 2 * α * f (xs (i + 1)) + dd i ≤ 2 * α * f (xs i) := fun i => by
    simp only [hdd, hsucc]
    exact Taylm.aux_qfbSearchStep_descent hH c g hα hL hαL (hbox i)
  -- so `f` falls along the iterates
  have hdd0 : ∀ i, 0 ≤ dd i := fun i => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hanti : Antitone (fun i => f (xs i)) := antitone_nat_of_succ_le fun i => by
    have := hdesc i; have := hdd0 i; nlinarith
  -- the steps are square-summable, so they tend to `0`
  have hsum : ∀ N, ∑ i ∈ Finset.range N, dd i ≤ 2 * α * (f x₀ - f xm) := by
    intro N
    induction N with
    | zero =>
        have h0 : f xm ≤ f x₀ := hxm hx₀
        simp only [Finset.range_zero, Finset.sum_empty]
        nlinarith
    | succ N ih =>
        rw [Finset.sum_range_succ]
        have h1 := hdesc N
        have h2 : f xm ≤ f (xs (N + 1)) := hxm (hbox (N + 1))
        -- the sum telescopes against the descent
        have h3 : ∑ i ∈ Finset.range N, dd i ≤ 2 * α * (f x₀ - f (xs N)) := by
          clear ih h1 h2
          induction N with
          | zero => simp [hxs]
          | succ N ihN =>
              rw [Finset.sum_range_succ]
              have := hdesc N
              linarith
        nlinarith
  have hddt : Tendsto dd atTop (𝓝 0) :=
    (summable_of_sum_range_le hdd0 hsum).tendsto_atTop_zero
  have hstep : Tendsto (fun i => xs (i + 1) - xs i) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [Pi.zero_apply]
    refine squeeze_zero_norm (fun i => ?_) (by
      simpa using (Real.continuous_sqrt.tendsto 0).comp hddt)
    -- one coordinate of the step is at most its whole length
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    rw [sq]
    exact Finset.single_le_sum (f := fun k => (xs (i + 1) - xs i) k * (xs (i + 1) - xs i) k)
      (fun k _ => mul_self_nonneg _) (Finset.mem_univ k)
  -- a convergent subsequence, and its limit is a fixed point of the step
  obtain ⟨x', hx', φ, hφ, hφt⟩ := hcpt.tendsto_subseq hbox
  have hSc : Continuous S := by
    simp only [hS]
    unfold Taylm.qfbSearchStep
    have hHc : Continuous fun x : Vec ℝ n => H *ᵥ x := continuous_const.matrix_mulVec continuous_id
    fun_prop
  have hfix : S x' = x' := by
    have hA : Tendsto (fun j => xs (φ j + 1)) atTop (𝓝 (S x')) := by
      simp only [hsucc]; exact (hSc.tendsto x').comp hφt
    have hB : Tendsto (fun j => xs (φ j + 1)) atTop (𝓝 x') := by
      have := hφt.add (hstep.comp hφ.tendsto_atTop)
      simp only [add_zero, Function.comp_def, add_sub_cancel] at this
      exact this
    exact tendsto_nhds_unique hA hB
  have hmin := Taylm.qfbSearchStep_fixed_isMinOn hH hP c g hα hfix
  refine ⟨x', hx', hmin, ⟨φ, hφ, hφt⟩, ?_⟩
  -- `f` falls monotonically to its infimum, which the subsequence identifies as `f x'`
  have hbdd : BddBelow (Set.range fun i => f (xs i)) :=
    ⟨f xm, by rintro _ ⟨i, rfl⟩; exact hxm (hbox i)⟩
  have hinf := tendsto_atTop_ciInf hanti hbdd
  have hsub : Tendsto (fun j => f (xs (φ j))) atTop (𝓝 (f x')) := (hfc.tendsto x').comp hφt
  have heq := tendsto_nhds_unique (hinf.comp hφ.tendsto_atTop) hsub
  show Tendsto (fun i => f (xs i)) atTop (𝓝 (f x'))
  rw [← heq]
  exact hinf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
