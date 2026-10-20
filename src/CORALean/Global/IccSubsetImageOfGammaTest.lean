module

public import CORALean.Global.HMatrixRegular
public import CORALean.Global.IsHMatrixOfGammaTest
public import CORALean.Global.SubsetImageOfDisjointBoundarySingular
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The inclusion test (2) proves a box inside the range

[1, Cor. 3.1]: for `f : x → ℝⁿ` continuous, continuously differentiable in `int x`, an interval
matrix `J = [Jlo, Jhi]` enclosing `f'` there, `0 ∉ Jᵢᵢ` and `f(x₀) ∈ y`, the inclusion
`x₀ + Γ(J, x - x₀, y - f(x₀)) ⊆ int x` (2), `gammaTest`, gives `y ⊆ f(x)`. Through [1, Thm. 3.1]
(`Icc_subset_image_of_disjoint_boundary_singular`): (2) puts `x₀` in `int x` and makes `J` an
H-matrix (`isHMatrix_of_gammaTest`), so every real matrix in `J` is regular, which is (ii); (i) is
the mean-value theorem along the segment from `x₀` to a boundary point, a row at a time, solving
row `i` for `vᵢ`, which (2) puts in `(xloᵢ, xhiᵢ)`, contradicting `v ∈ ∂x`.

## Inputs
* `f` – map
* `f'` – its derivative
* `x₀` – expansion point
* `xlo` – lower end of the domain box
* `xhi` – upper end of the domain box
* `ylo` – lower end of the target box
* `yhi` – upper end of the target box
* `Jlo` – lower end of the Jacobian enclosure
* `Jhi` – upper end of the Jacobian enclosure

## Hypotheses
* `hf` – the derivative is strict at interior points
* `hcont` – the map is continuous on the domain box
* `hJ₁` – the Jacobian enclosure contains the derivative at interior points
* `hJ` – the enclosure's ends are ordered
* `hdiag` – no diagonal enclosure contains zero
* `hx₀` – the expansion point lies in the domain box
* `hy` – the map's value at the expansion point lies in the target box
* `h2` – the inclusion test holds

## Conclusion
* the target box lies in the image of the domain box

## References

* [1] A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued
      functions". Reliable Computing, 14:1-23, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Finset

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `L w = Σ_j w_j L(e_j)`, one component at a time. -/
theorem aux_apply_eq_sum_single (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ)
    (i : Fin n) : -- --- CONCL ---
    L w i = ∑ j, L (Pi.single j 1) i * w j := by -- --- PROOF ---
  have hw : w = ∑ j, w j • (Pi.single j 1 : Fin n → ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 3.1]: (2) gives `y ⊆ f(x)`. -/
theorem Icc_subset_image_of_gammaTest
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {x₀ xlo xhi ylo yhi : Fin n → ℝ} {Jlo Jhi : Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ x ∈ interior (Icc xlo xhi), HasStrictFDerivAt f (f' x) x)
    (hcont : ContinuousOn f (Icc xlo xhi))
    (hJ₁ : ∀ x ∈ interior (Icc xlo xhi), ∀ i j, f' x (Pi.single j 1) i ∈ Icc (Jlo i j) (Jhi i j))
    (hJ : ∀ i j, Jlo i j ≤ Jhi i j) (hdiag : ∀ i, (0 : ℝ) ∉ Icc (Jlo i i) (Jhi i i))
    (hx₀ : x₀ ∈ Icc xlo xhi) (hy : f x₀ ∈ Icc ylo yhi)
    (h2 : gammaTest f x₀ xlo xhi Jlo Jhi ylo yhi) : -- --- CONCL ---
    Icc ylo yhi ⊆ f '' Icc xlo xhi := by -- --- PROOF ---
  have hH := isHMatrix_of_gammaTest hJ hdiag hx₀ hy h2
  -- a box point with every coordinate inside is an interior point
  have hopen : ∀ v : Fin n → ℝ, (∀ i, v i ∈ Ioo (xlo i) (xhi i)) → v ∈ interior (Icc xlo xhi) :=
    fun v hv => interior_maximal (fun x hx => ⟨fun i => (hx i trivial).1.le,
      fun i => (hx i trivial).2.le⟩ : (Set.pi univ fun i => Ioo (xlo i) (xhi i)) ⊆ Icc xlo xhi)
      (isOpen_set_pi finite_univ fun i _ => isOpen_Ioo) (fun i _ => hv i)
  have hconv : Convex ℝ (Icc xlo xhi) := convex_Icc xlo xhi
  -- (2) at `v = x₀` puts `x₀` in `int x`
  have hint₀ : x₀ ∈ interior (Icc xlo xhi) := hopen x₀ fun i => by
    have := h2 (f x₀) hy Jlo (fun i j => ⟨le_rfl, hJ i j⟩) x₀ hx₀ i
    simpa only [sub_self, Finset.sum_const_zero, mul_zero, zero_div, add_zero] using this
  -- (ii): `det f' ≠ 0` at every interior point, `f'` being a real matrix in the H-matrix `J`
  have hdet : ∀ x ∈ interior (Icc xlo xhi),
      LinearMap.det (f' x).toLinearMap ≠ 0 := by
    intro x hx
    rw [← LinearMap.det_toMatrix' (f' x).toLinearMap]
    have hA : ∀ i j, LinearMap.toMatrix' (f' x).toLinearMap i j
        = f' x (Pi.single j 1) i := fun i j => by
      simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    -- the H-matrix `J` gives regularity of every real matrix between its mignitudes and magnitudes
    refine det_ne_zero_of_isHMatrix hH _ (fun i => ?_) (fun i j _ => ?_)
    · -- the diagonal entry is at least the mignitude, as `0 ∉ Jᵢᵢ`
      have hm := hJ₁ x hx i i
      rw [hA]
      by_cases hlo : Jlo i i ≤ 0
      · have hhi : Jhi i i < 0 := lt_of_not_ge fun h0 => hdiag i ⟨hlo, h0⟩
        calc min |Jlo i i| |Jhi i i| ≤ |Jhi i i| := min_le_right _ _
          _ = -Jhi i i := abs_of_neg hhi
          _ ≤ -(f' x (Pi.single i 1) i) := neg_le_neg hm.2
          _ = |f' x (Pi.single i 1) i| := (abs_of_neg (lt_of_le_of_lt hm.2 hhi)).symm
      · calc min |Jlo i i| |Jhi i i| ≤ |Jlo i i| := min_le_left _ _
          _ = Jlo i i := abs_of_pos (not_le.mp hlo)
          _ ≤ f' x (Pi.single i 1) i := hm.1
          _ ≤ |f' x (Pi.single i 1) i| := le_abs_self _
    · -- an off-diagonal entry is at most the magnitude
      have hm := hJ₁ x hx i j
      rw [hA]
      refine abs_le.2 ⟨?_, ?_⟩
      · linarith [hm.1, neg_abs_le (Jlo i j), le_max_left |Jlo i j| |Jhi i j|]
      · linarith [hm.2, le_abs_self (Jhi i j), le_max_right |Jlo i j| |Jhi i j|]
  have hii : Disjoint (Icc ylo yhi) (f '' {x | x ∈ interior (Icc xlo xhi) ∧
      LinearMap.det (f' x).toLinearMap = 0}) := by
    rw [Set.disjoint_right]
    rintro _ ⟨x, ⟨hx, hx0⟩, rfl⟩ _
    exact hdet x hx hx0
  -- (i): a boundary point reaching `y` would lie in `x₀ + Γ(...) ⊆ int x`
  have hi : Disjoint (Icc ylo yhi) (f '' frontier (Icc xlo xhi)) := by
    rw [Set.disjoint_right]
    rintro _ ⟨v, hvf, rfl⟩ hvy
    have hv : v ∈ Icc xlo xhi := isClosed_Icc.frontier_subset hvf
    -- the mean-value theorem, one row at a time, along `γ t = x₀ + t (v - x₀)`
    let γ : ℝ → (Fin n → ℝ) := fun t => x₀ + t • (v - x₀)
    have hγc : Continuous γ := by fun_prop
    -- the segment lies in the box, and in its interior before the end point
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Icc xlo xhi := fun t ht =>
      hconv.add_smul_sub_mem hx₀ hv ht
    have hγi : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ interior (Icc xlo xhi) := fun t ht => by
      have hseg := hconv.openSegment_interior_closure_subset_interior hint₀ (subset_closure hv)
      refine hseg ?_
      rw [openSegment_eq_image]
      exact ⟨t, ht, by simp only [γ]; module⟩
    -- row `i` of the mean-value theorem: a point `p` of the segment with the slope of the row
    have hrow : ∀ i, ∃ p ∈ interior (Icc xlo xhi),
        f v i - f x₀ i = ∑ j, f' p (Pi.single j 1) i * (v j - x₀ j) := by
      intro i
      -- the row of `f ∘ γ` is differentiable inside, continuous on the closed segment
      have hφ : ∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (fun t => f (γ t) i) (f' (γ t) (v - x₀) i) t := by
        intro t ht
        have hγd := ((hasDerivAt_id t).smul_const (v - x₀)).const_add x₀
        rw [one_smul] at hγd
        exact hasDerivAt_pi.mp (((hf _ (hγi t ht)).hasFDerivAt).comp_hasDerivAt t hγd) i
      have hφc : ContinuousOn (fun t => f (γ t) i) (Icc 0 1) :=
        (continuous_apply i).comp_continuousOn
          (hcont.comp hγc.continuousOn fun t ht => hγ t ht)
      -- the mean-value theorem on `[0, 1]`
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t => f (γ t) i)
        (fun t => f' (γ t) (v - x₀) i) zero_lt_one hφc hφ
      refine ⟨γ c, hγi c hc, ?_⟩
      rw [← aux_apply_eq_sum_single]
      simp only [γ, one_smul, zero_smul, add_zero, add_sub_cancel, sub_zero, div_one] at hcd
      exact hcd.symm
    -- one point per row: together a real matrix in the interval `J`
    choose p hp hpe using hrow
    let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => f' (p i) (Pi.single j 1) i
    have hJmem : ∀ i j, J i j ∈ Icc (Jlo i j) (Jhi i j) := fun i j => hJ₁ _ (hp i) i j
    refine hvf.2 (hopen v fun i => ?_)
    have key := h2 (f v) hvy J hJmem v hv i
    have hJii : J i i ≠ 0 := fun h0 => hdiag i (h0 ▸ hJmem i i)
    have hsplit := (Finset.add_sum_erase Finset.univ
      (fun j => J i j * (v j - x₀ j)) (Finset.mem_univ i)).symm
    have hpi : f v i - f x₀ i = ∑ j, J i j * (v j - x₀ j) := hpe i
    -- solving row `i` for `vᵢ` is the expression (2) bounds
    rwa [hpi, hsplit, add_sub_cancel_right, mul_div_cancel_left₀ _ hJii, add_sub_cancel] at key
  exact Icc_subset_image_of_disjoint_boundary_singular hf hcont hi hii ⟨x₀, hx₀, hy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
