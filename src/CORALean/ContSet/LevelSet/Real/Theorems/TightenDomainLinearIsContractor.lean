module

public import CORALean.ContSet.LevelSet.Real.Operations.TightenDomainLinear
public import CORALean.ContSet.LevelSet.Real.Definitions.Contractor
public import CORALean.ContSet.Interval.Real.Theorems.MemCenter
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Real.Theorems.InvBetween
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The `'linear'` contractor of `tightenDomain` is a contractor

The box it returns lies in the box it was given and keeps every solution of `f(x) = 0`
([1, Def. 6], `IsContractor`), whatever the number of sweeps. The reason is the mean value form
of the equation: along the segment from the centre `m` to a solution `x`, both in the box,
`0 = f(x) = f(m) + Σᵢ κᵢ (xᵢ - mᵢ)` with `κᵢ = ∂ᵢ f(ξ)` at a point `ξ` of the segment, hence of
the box, so `κᵢ` lies in the interval gradient `kᵢ`. Solving for `xⱼ` and enclosing each term in
interval arithmetic puts `xⱼ` in the tightened range, as long as `0 ∉ kⱼ`; the later coordinates
see the narrowed box, which still holds `x`.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise LevelSet

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Membership in a vector box, in coordinates. -/
theorem LevelSet.aux_mem_vecBox (I : Interval (Vec ℝ n)) (x : Vec ℝ n) :
    x ∈ I.construct ↔ ∀ i, I.inf i ≤ x i ∧ x i ≤ I.sup i := Iff.rfl

/-- A coordinate step only narrows the box. -/
theorem LevelSet.aux_linearCoord_subset (fm : ℝ) (m : Vec ℝ n) (k : Interval (Vec ℝ n))
    (j : Fin n) (int : Interval (Vec ℝ n)) :
    (LevelSet.linearCoord fm m k j int).construct ⊆ int.construct := by -- --- PROOF ---
  unfold LevelSet.linearCoord
  split_ifs
  · intro x hx
    dsimp only at hx
    rw [LevelSet.aux_mem_vecBox] at hx ⊢
    intro l
    have hl := hx l
    by_cases hlj : l = j
    · subst hlj
      simp only [Function.update_self] at hl
      exact ⟨(le_max_left _ _).trans hl.1, hl.2.trans (min_le_left _ _)⟩
    · simpa only [Function.update_of_ne hlj] using hl
  · exact fun x hx => hx

/-- A coordinate step keeps every solution whose mean value form holds with a gradient in `k`. -/
theorem LevelSet.aux_linearCoord_mem {fm : ℝ} {m : Vec ℝ n} {k : Interval (Vec ℝ n)} {j : Fin n}
    {int : Interval (Vec ℝ n)} {x : Vec ℝ n} (hx : x ∈ int.construct) (κ : Vec ℝ n)
    (hκ : ∀ i, k.inf i ≤ κ i ∧ κ i ≤ k.sup i) (heq : fm + ∑ i, κ i * (x i - m i) = 0) :
    x ∈ (LevelSet.linearCoord fm m k j int).construct := by -- --- PROOF ---
  unfold LevelSet.linearCoord
  split_ifs with hc
  swap
  · exact hx
  dsimp only
  rw [LevelSet.aux_mem_vecBox]
  rw [LevelSet.aux_mem_vecBox] at hx
  intro i
  have hxi := hx i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self]
    -- the equation solved for `x i`
    have hsum : ∑ l, κ l * x l = κ i * x i + ∑ l ∈ Finset.univ.erase i, κ l * x l :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have hsplit : ∑ l, κ l * (x l - m l) = ∑ l, κ l * x l - ∑ l, κ l * m l := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hr : κ i * x i = -fm + ∑ l, κ l * m l - ∑ l ∈ Finset.univ.erase i, κ l * x l := by
      linarith
    -- the numerator lies in `[sLo, sHi]`
    have hm₁ : ∑ l, Interval.mulLo (k.inf l) (k.sup l) (m l) (m l) ≤ ∑ l, κ l * m l :=
      Finset.sum_le_sum fun l _ =>
        (Interval.mul_between_corners (hκ l).1 (hκ l).2 le_rfl le_rfl).1
    have hm₂ : ∑ l, κ l * m l ≤ ∑ l, Interval.mulHi (k.inf l) (k.sup l) (m l) (m l) :=
      Finset.sum_le_sum fun l _ =>
        (Interval.mul_between_corners (hκ l).1 (hκ l).2 le_rfl le_rfl).2
    have hx₁ : ∑ l ∈ Finset.univ.erase i, κ l * x l ≤
        ∑ l ∈ Finset.univ.erase i, Interval.mulHi (k.inf l) (k.sup l) (int.inf l) (int.sup l) :=
      Finset.sum_le_sum fun l _ =>
        (Interval.mul_between_corners (hκ l).1 (hκ l).2 (hx l).1 (hx l).2).2
    have hx₂ : ∑ l ∈ Finset.univ.erase i, Interval.mulLo (k.inf l) (k.sup l) (int.inf l)
        (int.sup l) ≤ ∑ l ∈ Finset.univ.erase i, κ l * x l :=
      Finset.sum_le_sum fun l _ =>
        (Interval.mul_between_corners (hκ l).1 (hκ l).2 (hx l).1 (hx l).2).1
    -- and `x i` is the numerator times `1 / κ i`
    have hκi : κ i ≠ 0 := by
      rcases hc with h | h
      · exact (h.trans_le (hκ i).1).ne'
      · exact ((hκ i).2.trans_lt h).ne
    have hxr : x i = (-fm + ∑ l, κ l * m l - ∑ l ∈ Finset.univ.erase i, κ l * x l) * (κ i)⁻¹ := by
      rw [← hr]
      field_simp
    obtain ⟨hinv₁, hinv₂⟩ := Interval.inv_between hc (hκ i).1 (hκ i).2
    obtain ⟨hq₁, hq₂⟩ := Interval.mul_between_corners
      (a := -fm + ∑ l, Interval.mulLo (k.inf l) (k.sup l) (m l) (m l)
        - ∑ l ∈ Finset.univ.erase i, Interval.mulHi (k.inf l) (k.sup l) (int.inf l) (int.sup l))
      (b := -fm + ∑ l, Interval.mulHi (k.inf l) (k.sup l) (m l) (m l)
        - ∑ l ∈ Finset.univ.erase i, Interval.mulLo (k.inf l) (k.sup l) (int.inf l) (int.sup l))
      (y := -fm + ∑ l, κ l * m l - ∑ l ∈ Finset.univ.erase i, κ l * x l)
      (by linarith) (by linarith) hinv₁ hinv₂
    rw [← hxr] at hq₁ hq₂
    exact ⟨max_le hxi.1 hq₁, le_min hxi.2 hq₂⟩
  · simpa only [Function.update_of_ne hij] using hxi

/-- The coordinate steps in turn narrow the box and keep every such solution. -/
theorem LevelSet.aux_linearFold (fm : ℝ) (m : Vec ℝ n) (k : Interval (Vec ℝ n)) :
    ∀ (l : List (Fin n)) (X : Interval (Vec ℝ n)),
      (l.foldl (fun X j => linearCoord fm m k j X) X).construct ⊆ X.construct ∧
      ∀ x ∈ X.construct, ∀ κ : Vec ℝ n, (∀ i, k.inf i ≤ κ i ∧ κ i ≤ k.sup i) →
        fm + ∑ i, κ i * (x i - m i) = 0 →
        x ∈ (l.foldl (fun X j => linearCoord fm m k j X) X).construct := by -- --- PROOF ---
  intro l
  induction l with
  | nil => exact fun X => ⟨fun x hx => hx, fun x hx _ _ _ => hx⟩
  | cons j l ih =>
    intro X
    obtain ⟨h₁, h₂⟩ := ih (LevelSet.linearCoord fm m k j X)
    exact ⟨h₁.trans (LevelSet.aux_linearCoord_subset fm m k j X),
      fun x hx κ hκ heq => h₂ x (LevelSet.aux_linearCoord_mem hx κ hκ heq) κ hκ heq⟩

/-- The mean value form of `f` along the segment from `m` to `x`. -/
theorem LevelSet.aux_meanValue {f : Vec ℝ n → ℝ} (hf : Differentiable ℝ f) (m x : Vec ℝ n) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      f x - f m = ∑ i, taylorGrad f (m + t • (x - m)) i * (x i - m i) := by -- --- PROOF ---
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (m + t • (x - m)))
      (fderiv ℝ f (m + t • (x - m)) (x - m)) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => m + t • (x - m)) (x - m) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - m)).const_add m
    exact (hf _).hasFDerivAt.comp_hasDerivAt t h1
  obtain ⟨t, ht, hder⟩ := exists_deriv_eq_slope (fun t : ℝ => f (m + t • (x - m))) one_pos
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
  refine ⟨t, ht, ?_⟩
  rw [(hd t).deriv] at hder
  simp only [one_smul, zero_smul, add_sub_cancel, add_zero, sub_zero, div_one] at hder
  have hv : x - m = ∑ i, (x i - m i) • (Pi.single i (1 : ℝ) : Vec ℝ n) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hder]
  generalize m + t • (x - m) = ξ
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, taylorGrad]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- One sweep narrows the box and keeps every solution. -/
theorem LevelSet.aux_linearSweep {f : Vec ℝ n → ℝ} (hf : Differentiable ℝ f)
    {grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)} (hg : IsGradEnclosure f grad)
    (I : Interval (Vec ℝ n)) :
    (LevelSet.linearSweep f grad I).construct ⊆ I.construct ∧
      ∀ x ∈ I.construct, f x = 0 →
        x ∈ (LevelSet.linearSweep f grad I).construct := by -- --- PROOF ---
  -- the fold of `aux_linearFold`, at the centre, the interval gradient and `f` of the centre
  obtain ⟨h₁, h₂⟩ := LevelSet.aux_linearFold (f I.center) I.center (grad I) (List.finRange n) I
  refine ⟨h₁, fun x hx hfx => ?_⟩
  have hI : I.IsNonempty (ι := Fin n) := fun i => (hx i).1.trans (hx i).2
  have hm : I.center ∈ I.construct := Interval.mem_center I hI
  obtain ⟨t, ht, hmv⟩ := LevelSet.aux_meanValue hf I.center x
  -- the point of the segment lies in the box, so the gradient there lies in the interval gradient
  have hξ : I.center + t • (x - I.center) ∈ I.construct := by
    have := Interval.convex_construct I hm hx (sub_nonneg.mpr ht.2.le) ht.1.le
      (by ring)
    convert this using 1
    module
  refine h₂ x hx (fun i => taylorGrad f (I.center + t • (x - I.center)) i)
    (fun i => hg I _ hξ i) ?_
  rw [hfx] at hmv
  simp only [zero_sub] at hmv
  linarith

/-- The sweeps keep narrowing and keep every solution. -/
theorem LevelSet.aux_tightenDomainLinear {f : Vec ℝ n → ℝ} (hf : Differentiable ℝ f)
    {grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)} (hg : IsGradEnclosure f grad) :
    ∀ (k : ℕ) (I : Interval (Vec ℝ n)),
      (LevelSet.tightenDomainLinear f grad k I).construct ⊆ I.construct ∧
      ∀ x ∈ I.construct, f x = 0 →
        x ∈ (LevelSet.tightenDomainLinear f grad k I).construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun I => ⟨fun x hx => hx, fun x hx _ => hx⟩
  | succ k ih =>
    intro I
    obtain ⟨s₁, s₂⟩ := LevelSet.aux_linearSweep hf hg I
    obtain ⟨i₁, i₂⟩ := ih (LevelSet.linearSweep f grad I)
    unfold LevelSet.tightenDomainLinear at *
    rw [Function.iterate_succ_apply]
    exact ⟨i₁.trans s₁, fun x hx hfx => i₂ x (s₂ x hx hfx) hfx⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.tightenDomainLinear_isContractor {f : Vec ℝ n → ℝ} (hf : Differentiable ℝ f)
    {grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)} (hg : IsGradEnclosure f grad)
    (maxIter : ℕ) : IsContractor f (LevelSet.tightenDomainLinear f grad maxIter) :=
  fun I => ⟨(LevelSet.aux_tightenDomainLinear hf hg maxIter I).1,
    fun x hx hfx => (LevelSet.aux_tightenDomainLinear hf hg maxIter I).2 x hx hfx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
