import CORALean.NN.Layers.PolyRelaxation

/-!
# The error a polynomial fit leaves, bounded by sampling

CORA's `nnHelper/minMaxDiffOrder` [1]: to bound `g = σ - p` over a box it does
not look for an extremum, it samples. With `|g'| ≤ M` on the box the mean value
theorem says `g` moves by at most `M` times a distance, so a grid of spacing
`dx` sees everything up to `M · dx`, and `min ys - M·dx ≤ g t ≤ max ys + M·dx`.

Sound at every sample count, and a larger one is tighter — the fit itself owes
nothing, exactly as `reduceBy_outer` owes nothing at any partition. `dx` is what
buys the precision, so refining a neuron is spending samples on it.

`sub_mul_bounds_of_deriv` in `Curvature` is this argument at degree 1, where one
application of the theorem over the whole box is enough because the comparison
point can be an end of it.

`ofSampling` closes the construction: the two ends of the bracket are averaged
into the constant coefficient, so what is left is a radius. That midpoint is
`Relaxation.ofDeriv`'s, and `computeApproxError`'s `coeffs[end]`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- The `N + 1` points sampled across `[l, u]`: `i` steps of `(u - l) / N` from
the left end. -/
noncomputable def sampleGrid (l u : ℝ) (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  l + (i : ℕ) * ((u - l) / N)

/-- The least sampled value of `g`. -/
noncomputable def sampleInf (g : ℝ → ℝ) (l u : ℝ) (N : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i : Fin (N + 1) => g (sampleGrid l u N i)

/-- The greatest sampled value of `g`. -/
noncomputable def sampleSup (g : ℝ → ℝ) (l u : ℝ) (N : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin (N + 1) => g (sampleGrid l u N i)

theorem sampleGrid_mem_Icc {l u : ℝ} {N : ℕ} (hN : 0 < N) (hlu : l ≤ u) (i : Fin (N + 1)) :
    l ≤ sampleGrid l u N i ∧ sampleGrid l u N i ≤ u := by -- --- PROOF ---
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdx : 0 ≤ (u - l) / N := div_nonneg (by linarith) hNpos.le
  have hfull : (N : ℝ) * ((u - l) / N) = u - l := by
    field_simp
  -- the last index is `N`, so no sample steps past the right end
  have hstep : ((i : ℕ) : ℝ) * ((u - l) / N) ≤ (N : ℝ) * ((u - l) / N) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.lt_succ_iff.mp i.isLt)) hdx
  have hlow : 0 ≤ ((i : ℕ) : ℝ) * ((u - l) / N) := mul_nonneg (Nat.cast_nonneg _) hdx
  exact ⟨by simp only [sampleGrid]; linarith, by simp only [sampleGrid]; linarith⟩

/-- Every point of the box is within one spacing of a sample, which is what lets
the sampled range speak for the whole box. -/
theorem exists_sampleGrid_close {l u t : ℝ} {N : ℕ} (hN : 0 < N) (hl : l ≤ t) (hu : t ≤ u) :
    ∃ i : Fin (N + 1), |t - sampleGrid l u N i| ≤ (u - l) / N := by -- --- PROOF ---
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfull : (N : ℝ) * ((u - l) / N) = u - l := by
    field_simp
  rcases eq_or_lt_of_le (hl.trans hu) with hlu | hlu
  · -- a degenerate box: the spacing is zero and the left end is the only point
    refine ⟨0, ?_⟩
    have ht : t = l := le_antisymm (by rw [hlu]; exact hu) hl
    have hdx : (u - l) / N = 0 := by rw [← hlu, sub_self, zero_div]
    have hg : sampleGrid l u N (0 : Fin (N + 1)) = l := by
      show l + ((0 : Fin (N + 1)) : ℕ) * ((u - l) / N) = l
      rw [hdx, mul_zero, add_zero]
    rw [ht, hg, sub_self, abs_zero, hdx]
  · have hdxpos : 0 < (u - l) / N := div_pos (by linarith) hNpos
    have hq : 0 ≤ (t - l) / ((u - l) / N) := div_nonneg (by linarith) hdxpos.le
    have hqN : (t - l) / ((u - l) / N) ≤ (N : ℝ) := by
      rw [div_le_iff₀ hdxpos, hfull]
      linarith
    -- the sample below `t`, which the floor names and the box's width keeps in range
    have hkN : ⌊(t - l) / ((u - l) / N)⌋₊ ≤ N := by
      have hfloor := Nat.floor_le_floor hqN
      rwa [Nat.floor_natCast] at hfloor
    refine ⟨⟨⌊(t - l) / ((u - l) / N)⌋₊, by omega⟩, ?_⟩
    have hfl : ((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) ≤ (t - l) / ((u - l) / N) :=
      Nat.floor_le hq
    have hfu : (t - l) / ((u - l) / N) < (⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) + 1 :=
      Nat.lt_floor_add_one _
    rw [le_div_iff₀ hdxpos] at hfl
    rw [div_lt_iff₀ hdxpos] at hfu
    have hexp : (((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) + 1) * ((u - l) / N)
        = ((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) * ((u - l) / N) + (u - l) / N := by
      ring
    show |t - (l + ((⌊(t - l) / ((u - l) / N)⌋₊ : ℕ) : ℝ) * ((u - l) / N))| ≤ (u - l) / N
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

/-- The sampled range, padded by the Lipschitz slack, brackets `g` on the whole
box. Sound at every `N`, and tighter as `N` grows. -/
theorem sample_bounds_of_deriv {g g' : ℝ → ℝ} {M l u t : ℝ} {N : ℕ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hN : 0 < N) (hl : l ≤ t) (hu : t ≤ u) :
    sampleInf g l u N - M * ((u - l) / N) ≤ g t
      ∧ g t ≤ sampleSup g l u N + M * ((u - l) / N) := by -- --- PROOF ---
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM t hl hu)
  obtain ⟨i, hi⟩ := exists_sampleGrid_close hN hl hu
  obtain ⟨hgl, hgu⟩ := sampleGrid_mem_Icc hN (hl.trans hu) i
  -- the mean value theorem between `t` and the sample it is nearest to
  have hlip : |g t - g (sampleGrid l u N i)| ≤ M * |t - sampleGrid l u N i| := by
    have hbound : ∀ x ∈ Set.Icc l u, ‖g' x‖ ≤ M := fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x hx.1 hx.2
    have hmv := (convex_Icc l u).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hd x).hasDerivWithinAt) hbound ⟨hgl, hgu⟩ ⟨hl, hu⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have habs := abs_le.mp (hlip.trans (mul_le_mul_of_nonneg_left hi hM0))
  have hinf : sampleInf g l u N ≤ g (sampleGrid l u N i) :=
    Finset.inf'_le (fun j : Fin (N + 1) => g (sampleGrid l u N j)) (Finset.mem_univ i)
  have hsup : g (sampleGrid l u N i) ≤ sampleSup g l u N :=
    Finset.le_sup' (fun j : Fin (N + 1) => g (sampleGrid l u N j)) (Finset.mem_univ i)
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a fit and a derivative bound buy. `c` is arbitrary — no
soundness rests on it, only precision — and `N` is how much effort a box gets. -/
noncomputable def PolyRelaxation.ofSampling {σ σ' : ℝ → ℝ} {n : ℕ}
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (c : ℝ → ℝ → Fin (n + 1) → ℝ)
    (M : ℝ → ℝ → ℝ) (N : ℝ → ℝ → ℕ)
    (hM : ∀ l u x, l ≤ x → x ≤ u → |σ' x - evalPolyDeriv (c l u) x| ≤ M l u)
    (hN : ∀ l u, 0 < N l u) : PolyRelaxation σ n where
  coeffs l u := shiftConst (c l u)
    ((sampleInf (fun x => σ x - evalPoly (c l u) x) l u (N l u)
      + sampleSup (fun x => σ x - evalPoly (c l u) x) l u (N l u)) / 2)
  error l u :=
    (sampleSup (fun x => σ x - evalPoly (c l u) x) l u (N l u)
      - sampleInf (fun x => σ x - evalPoly (c l u) x) l u (N l u)) / 2
      + M l u * ((u - l) / N l u)
  sound {l u t} hl hu := by
    have hg : ∀ x, HasDerivAt (fun y => σ y - evalPoly (c l u) y)
        (σ' x - evalPolyDeriv (c l u) x) x :=
      fun x => (hd x).sub (hasDerivAt_evalPoly (c l u) x)
    obtain ⟨hlow, hhigh⟩ :=
      sample_bounds_of_deriv hg (fun x hx hx' => hM l u x hx hx') (hN l u) hl hu
    -- the two ends average into the constant, so what is left of them is a radius
    rw [evalPoly_shiftConst, abs_le]
    exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
