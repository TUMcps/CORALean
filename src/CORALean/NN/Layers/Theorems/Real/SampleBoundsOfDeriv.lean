module

public import CORALean.NN.Layers.Definitions.PolySampling
public import CORALean.NN.Layers.Theorems.Real.SampleGridMemIcc
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# The exact sampled range brackets a function

ℝ-only, the grid and the range being exact: the mean value theorem between a point and the
sample nearest it. Sound at every `N`, and tighter as `N` grows.

## Inputs
* `g` – function
* `g'` – its derivative
* `M` – bound on the derivative
* `l` – lower end of the box
* `u` – upper end of the box
* `t` – point in the box
* `N` – number of sample intervals

## Hypotheses
* `hd` – the function has the given derivative
* `hM` – derivative is bounded on the box
* `hN` – number of intervals is positive
* `hl` – point is above the lower end
* `hu` – point is below the upper end

## Conclusion
* the function at the point lies within the sampled range widened by the slack
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every point of the box is near an exact sample. -/
theorem aux_exists_sampleGrid_close {l u t : ℝ} {N : ℕ} (hN : 0 < N) (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem sample_bounds_of_deriv {g g' : ℝ → ℝ} {M l u t : ℝ} {N : ℕ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hN : 0 < N) (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    sampleInf g l u N - M * ((u - l) / N) ≤ g t
      ∧ g t ≤ sampleSup g l u N + M * ((u - l) / N) := by -- --- PROOF ---
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM t hl hu)
  obtain ⟨i, hi⟩ := aux_exists_sampleGrid_close hN hl hu
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
