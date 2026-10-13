module

public import CORALean.Global.InnerRangeOfFrontier
public import CORALean.Global.InnerTest
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Interval.Set.Pi

@[expose] public section

/-!
# The inclusion test for an inner box of the first `r` components

[1, Cor. 3.1]: `f₁:ᵣ` on `u = (u₁, u₂) ∈ IRʳ × IRᵐ⁻ʳ`, `J = (J₁ J₂)` enclosing its Jacobian
on `u`, `0 ∉ (J₁)ᵢᵢ`, and `f₁:ᵣ(ũ) ∈ y₁`: if
`H = ũ₁ + Diag⁻¹(J₁)(y₁ - f₁:ᵣ(ũ) - OffDiag(J₁)(u₁ - ũ₁) - J₂(u₂ - ũ₂)) ⊆ int(u₁)` (5),
then `y₁ ⊆ f₁:ᵣ(u)`. (5) is read over real matrices `J₁, J₂` in the interval ones and points
of `y₁` and `u`, which any interval evaluation of `H` encloses.

The printed proof checks (i) of [1, Thm. 3.1] on all of `∂u`, which (5) does not give: on a
face where `u₂` sits at a bound and `u₁` is interior there is no contradiction
(`innerTest_step_counterexample`). The statement holds: on the slice `v ↦ f₁:ᵣ(v, ũ₂)` the
mean-value argument reaches every point of `∂u₁`, and Thm. 3.1 applies there; the `J₂` term,
`0` on the slice, only makes (5) harder to meet. (3) is the hypothesis `det J₁(x) ≠ 0`.

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 18:117-143, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Matrix

variable {r s : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `g'(x)(w, 0) = J₁(x) w`, `J₁(x)` the columns `g'(x)(eⱼ, 0)`. -/
theorem aux_apply_inl_eq_mulVec (L : (Fin r → ℝ) × (Fin s → ℝ) →L[ℝ] (Fin r → ℝ))
    (w : Fin r → ℝ) :
    L (w, 0) = (Matrix.of fun i j => L (Pi.single j 1, 0) i) *ᵥ w := by -- --- PROOF ---
  have hw : (w, (0 : Fin s → ℝ)) = ∑ j, w j • ((Pi.single j 1 : Fin r → ℝ), (0 : Fin s → ℝ)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      simp only [Prod.smul_fst]
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    · rw [Prod.snd_sum]
      simp
  ext i
  rw [hw, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.1]: (5) gives `y₁ ⊆ f₁:ᵣ(u)`. -/
theorem Icc_subset_image_of_innerTest {g : (Fin r → ℝ) × (Fin s → ℝ) → (Fin r → ℝ)}
    {g' : (Fin r → ℝ) × (Fin s → ℝ) → ((Fin r → ℝ) × (Fin s → ℝ) →L[ℝ] (Fin r → ℝ))}
    {ũ : (Fin r → ℝ) × (Fin s → ℝ)} {lo₁ hi₁ : Fin r → ℝ} {lo₂ hi₂ : Fin s → ℝ}
    {J₁lo J₁hi : Matrix (Fin r) (Fin r) ℝ} {J₂lo J₂hi : Matrix (Fin r) (Fin s) ℝ}
    {ylo yhi : Fin r → ℝ}
    (hg : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, HasStrictFDerivAt g (g' x) x)
    (h3 : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂,
      (Matrix.of fun i j => g' x (Pi.single j 1, 0) i).det ≠ 0)
    (hJ₁ : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i j,
      g' x (Pi.single j 1, 0) i ∈ Icc (J₁lo i j) (J₁hi i j))
    (hJ₂ : ∀ x ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂, ∀ i l,
      g' x (0, Pi.single l 1) i ∈ Icc (J₂lo i l) (J₂hi i l))
    (hdiag : ∀ i, (0 : ℝ) ∉ Icc (J₁lo i i) (J₁hi i i)) (hũ : ũ ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂)
    (hii : g ũ ∈ Icc ylo yhi) (h5 : innerTest g ũ lo₁ hi₁ lo₂ hi₂ J₁lo J₁hi J₂lo J₂hi ylo yhi) :
    Icc ylo yhi ⊆ g '' (Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂) := by -- --- PROOF ---
  -- the slice `h(v) = g(v, ũ₂)`, a submersion by (3)
  let h : (Fin r → ℝ) → (Fin r → ℝ) := fun v => g (v, ũ.2)
  let h' : (Fin r → ℝ) → ((Fin r → ℝ) →L[ℝ] (Fin r → ℝ)) := fun v =>
    (g' (v, ũ.2)).comp (ContinuousLinearMap.inl ℝ (Fin r → ℝ) (Fin s → ℝ))
  have hmem : ∀ v ∈ Icc lo₁ hi₁, (v, ũ.2) ∈ Icc lo₁ hi₁ ×ˢ Icc lo₂ hi₂ := fun v hv => ⟨hv, hũ.2⟩
  have hh : ∀ v ∈ Icc lo₁ hi₁, HasStrictFDerivAt h (h' v) v := fun v hv =>
    (hg _ (hmem v hv)).comp v ((hasStrictFDerivAt_id v).prodMk (hasStrictFDerivAt_const ũ.2 v))
  have hh'eq : ∀ v w, h' v w = (Matrix.of fun i j => g' (v, ũ.2) (Pi.single j 1, 0) i) *ᵥ w :=
    fun v w => aux_apply_inl_eq_mulVec (g' (v, ũ.2)) w
  have hsurj : ∀ v ∈ Icc lo₁ hi₁, (h' v).range = ⊤ := by
    intro v hv
    refine LinearMap.range_eq_top.mpr fun z => ?_
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (h3 _ (hmem v hv)))
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu z
    exact ⟨w, by rw [ContinuousLinearMap.coe_coe, hh'eq, hw]⟩
  have hcont : ContinuousOn h (Icc lo₁ hi₁) := fun v hv =>
    (hh v hv).continuousAt.continuousWithinAt
  -- (i) on the slice: a point of `∂u₁` reaching `y₁` would lie in `H ⊆ int(u₁)`
  have hi : Disjoint (Icc ylo yhi) (h '' frontier (Icc lo₁ hi₁)) := by
    rw [disjoint_right]
    rintro _ ⟨v, hvf, rfl⟩ hvy
    have hv : v ∈ Icc lo₁ hi₁ := isClosed_Icc.frontier_subset hvf
    -- the mean-value theorem, one row at a time
    have hrow : ∀ i, ∃ p ∈ Icc lo₁ hi₁,
        h v i - g ũ i = ∑ j, g' (p, ũ.2) (Pi.single j 1, 0) i * (v j - ũ.1 j) := by
      intro i
      -- the segment from `ũ₁` to `v`, inside `u₁`
      let γ : ℝ → (Fin r → ℝ) := fun t => ũ.1 + t • (v - ũ.1)
      have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Icc lo₁ hi₁ := fun t ht =>
        (convex_Icc lo₁ hi₁).add_smul_sub_mem hũ.1 hv ht
      have hφ : ∀ t ∈ Icc (0 : ℝ) 1,
          HasDerivAt (fun t => h (γ t) i) (h' (γ t) (v - ũ.1) i) t := by
        intro t ht
        have hγd := ((hasDerivAt_id t).smul_const (v - ũ.1)).const_add ũ.1
        rw [one_smul] at hγd
        exact hasDerivAt_pi.mp ((hh _ (hγ t ht)).hasFDerivAt.comp_hasDerivAt t hγd) i
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t => h (γ t) i)
        (fun t => h' (γ t) (v - ũ.1) i) zero_lt_one
        (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
        (fun t ht => hφ t (Ioo_subset_Icc_self ht))
      refine ⟨γ c, hγ c (Ioo_subset_Icc_self hc), ?_⟩
      -- the derivative at `γ c` along `v - ũ₁` is row `i` of `J₁(γ c)` applied to it
      rw [hh'eq] at hcd
      simp only [γ, one_smul, zero_smul, add_zero, add_sub_cancel, sub_zero, div_one] at hcd
      show h v i - h ũ.1 i = _
      rw [← hcd]
      rfl
    -- one point per row: together a real matrix in the interval `J₁`
    choose p hp hpe using hrow
    let J : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => g' (p i, ũ.2) (Pi.single j 1, 0) i
    have hJ : ∀ i j, J i j ∈ Icc (J₁lo i j) (J₁hi i j) := fun i j => hJ₁ _ (hmem _ (hp i)) i j
    have hint : ∀ i, v i ∈ Ioo (lo₁ i) (hi₁ i) := by
      intro i
      have key := h5 (h v) hvy J hJ _ (hJ₂ ũ hũ) v hv ũ.2 hũ.2 i
      have hJii : J i i ≠ 0 := fun h0 => hdiag i (h0 ▸ hJ i i)
      have hsplit := (Finset.add_sum_erase Finset.univ
        (fun j => J i j * (v j - ũ.1 j)) (Finset.mem_univ i)).symm
      have hpi : h v i - g ũ i = ∑ j, J i j * (v j - ũ.1 j) := hpe i
      -- solving row `i` for `vᵢ` is the expression (5) bounds; the `J₂` term is `0`
      simp only [sub_self, mul_zero, Finset.sum_const_zero, sub_zero] at key
      rwa [hpi, hsplit, add_sub_cancel_right, mul_div_cancel_left₀ _ hJii, add_sub_cancel] at key
    have hpi : v ∈ Set.pi univ fun i => Ioo (lo₁ i) (hi₁ i) := fun i _ => hint i
    have hsubIcc : (Set.pi univ fun i => Ioo (lo₁ i) (hi₁ i)) ⊆ Icc lo₁ hi₁ := fun x hx =>
      ⟨fun i => (hx i trivial).1.le, fun i => (hx i trivial).2.le⟩
    exact hvf.2 (interior_maximal hsubIcc (isOpen_set_pi finite_univ fun i _ => isOpen_Ioo) hpi)
  -- Thm. 3.1 on the slice, whose image lies in `g(u)`
  have hsub := subset_image_of_disjoint_image_frontier isCompact_Icc
    (fun v hv => hh v (interior_subset hv)) (fun v hv => hsurj v (interior_subset hv)) hcont
    (convex_Icc ylo yhi).isPreconnected hi ⟨ũ.1, hũ.1, hii⟩
  exact hsub.trans (image_subset_iff.mpr fun v hv => ⟨(v, ũ.2), hmem v hv, rfl⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
