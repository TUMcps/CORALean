import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# An orthant of the `ℓ₁` ball has `2⁻ᵐ` of its volume

`[1, Thm. 4.6]` at `p = ∞` samples the unit ball `B₁ = B_{p*}` of `ℝᵐ` and rounds each sample `v`
to the corner `sign(v)` of the cube: the corner `s` is hit by the open orthant `{x | sᵢ xᵢ > 0}`
of the ball, which has `2⁻ᵐ` of its volume under every Haar measure. The `2ᵐ` orthants are
carried onto one another by sign reflections, which have determinant `±1`, and cover the ball
up to the coordinate hyperplanes, which are null.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory Matrix

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the proof is a single partition-of-the-ball argument, not worth splitting into files
theorem l1Ball_orthant_volume (vol : Measure (Fin m → ℝ)) [vol.IsAddHaarMeasure]
    (s : Fin m → ℝ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    vol {x | (∑ j, |x j|) ≤ 1 ∧ ∀ j, 0 < s j * x j} * 2 ^ m
      = vol {x | ∑ j, |x j| ≤ 1} := by -- --- PROOF ---
  set K : Set (Fin m → ℝ) := {x | ∑ j, |x j| ≤ 1} with hK
  -- the reflection `x ↦ (tⱼ xⱼ)` by signs preserves volume
  have hR : ∀ t : Fin m → ℝ, (∀ j, t j = 1 ∨ t j = -1) →
      ∃ f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ), (∀ x j, f x j = t j * x j) ∧
        ∀ S, vol (f ⁻¹' S) = vol S := by
    intro t ht
    refine ⟨Matrix.toLin' (Matrix.diagonal t), fun x j => by simp [Matrix.mulVec_diagonal],
      fun S => ?_⟩
    have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal t)) = ∏ j, t j := by
      rw [LinearMap.det_toLin', Matrix.det_diagonal]
    have habs : |∏ j, t j| = 1 := by
      rw [Finset.abs_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      rcases ht j with h | h <;> simp [h]
    have hne : LinearMap.det (Matrix.toLin' (Matrix.diagonal t)) ≠ 0 := by
      rw [hdet]; intro h; rw [h] at habs; simp at habs
    rw [Measure.addHaar_preimage_linearMap vol hne, hdet, abs_inv, habs]
    simp
  -- the orthants of the ball
  let sg : Bool → ℝ := fun b => if b then 1 else -1
  let O : (Fin m → Bool) → Set (Fin m → ℝ) :=
    fun σ => {x | (∑ j, |x j|) ≤ 1 ∧ ∀ j, 0 < sg (σ j) * x j}
  have hsg : ∀ b, sg b = 1 ∨ sg b = -1 := fun b => by cases b <;> simp [sg]
  have hKm : MeasurableSet K :=
    (isClosed_le (continuous_finsetSum _ fun j _ => (continuous_apply j).abs)
      continuous_const).measurableSet
  have hOmeas : ∀ σ, MeasurableSet (O σ) := fun σ => by
    refine hKm.inter ?_
    have : IsOpen {x : Fin m → ℝ | ∀ j, 0 < sg (σ j) * x j} := by
      simp_rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
        (continuous_const.mul (continuous_apply j))
    exact this.measurableSet
  -- the orthant of the signs `s`
  have hs0 : ∀ j, sg (decide (s j = 1)) = s j := fun j => by
    rcases hs j with h | h
    · simp [sg, h]
    · have : ¬ ((-1 : ℝ) = 1) := by norm_num
      simp [sg, h, this]
  have hOs : {x | (∑ j, |x j|) ≤ 1 ∧ ∀ j, 0 < s j * x j}
      = O (fun j => decide (s j = 1)) := by
    ext x; simp only [O, hs0]
  have hsq : ∀ j, s j * s j = 1 := fun j => by rcases hs j with h | h <;> simp [h]
  -- every orthant has the volume of that one
  have hvol : ∀ σ, vol (O σ) = vol (O fun j => decide (s j = 1)) := fun σ => by
    obtain ⟨f, hf, hfv⟩ := hR (fun j => sg (σ j) * s j) fun j => by
      rcases hsg (σ j) with h | h <;> rcases hs j with h' | h' <;> simp [h, h']
    rw [← hfv (O fun j => decide (s j = 1))]
    congr 1
    ext x
    have habs : ∀ j, |sg (σ j) * s j * x j| = |x j| := fun j => by
      rcases hsg (σ j) with h | h <;> rcases hs j with h' | h' <;> simp [h, h']
    have hprod : ∀ j, s j * (sg (σ j) * s j * x j) = sg (σ j) * x j := fun j => by
      linear_combination (sg (σ j) * x j) * hsq j
    simp only [O, Set.mem_preimage, Set.mem_setOf_eq, hf, hs0, habs, hprod]
  -- the orthants are disjoint, they lie in the ball and cover it up to the coordinate hyperplanes
  have hdisj : Pairwise (Function.onFun Disjoint O) := fun σ τ hne => by
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨-, hx⟩ ⟨-, hy⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have h1 := hx j
    have h2 := hy j
    cases hσ : σ j <;> cases hτ : τ j <;> rw [hσ] at h1 <;> rw [hτ] at h2 <;>
      simp [sg] at h1 h2 <;> first | linarith | exact hj (hσ.trans hτ.symm)
  have hsub : (⋃ σ, O σ) ⊆ K := fun x hx => by
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hx
    exact hσ.1
  -- the coordinate hyperplanes are null
  have hZ : vol (⋃ j : Fin m, {x : Fin m → ℝ | x j = 0}) = 0 := by
    refine measure_iUnion_null fun j => ?_
    have := Measure.addHaar_submodule vol (LinearMap.ker (LinearMap.proj j : (Fin m → ℝ) →ₗ[ℝ] ℝ))
      (fun h => by
        have := (Submodule.eq_top_iff'.mp h) (Pi.single j 1)
        simp at this)
    -- the hyperplane is the kernel of a nonzero coordinate functional
    have heq : {x : Fin m → ℝ | x j = 0}
        = (LinearMap.ker (LinearMap.proj j : (Fin m → ℝ) →ₗ[ℝ] ℝ) : Set (Fin m → ℝ)) := by
      ext x; simp
    rw [heq]; exact this
  -- a point of the ball off the hyperplanes lies in the orthant of its own signs
  have hcover : K ⊆ (⋃ σ, O σ) ∪ ⋃ j : Fin m, {x : Fin m → ℝ | x j = 0} := fun x hx => by
    by_cases hz : ∃ j, x j = 0
    · obtain ⟨j, hj⟩ := hz
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)
    · push Not at hz
      refine Or.inl (Set.mem_iUnion.mpr ⟨fun j => decide (0 < x j), hx, fun j => ?_⟩)
      rcases lt_or_gt_of_ne (hz j) with h | h
      · simp [sg, not_lt.mpr h.le, h]
      · simp [sg, h]
  have hKeq : vol K = ∑ σ, vol (O σ) := by
    refine le_antisymm ?_ ?_
    · calc vol K
            ≤ vol ((⋃ σ, O σ) ∪ ⋃ j : Fin m, {x : Fin m → ℝ | x j = 0}) := measure_mono hcover
        _ ≤ vol (⋃ σ, O σ) + vol (⋃ j : Fin m, {x : Fin m → ℝ | x j = 0}) :=
            measure_union_le _ _
        _ = ∑ σ, vol (O σ) := by rw [hZ, add_zero, measure_iUnion hdisj hOmeas, tsum_fintype]
    · calc ∑ σ, vol (O σ) = vol (⋃ σ, O σ) := by rw [measure_iUnion hdisj hOmeas, tsum_fintype]
        _ ≤ vol K := measure_mono hsub
  -- the sum of `2ᵐ` equal volumes
  rw [hOs, hKeq, Finset.sum_congr rfl fun σ _ => hvol σ]
  simp [Finset.sum_const, mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
