module

public import CORALean.NN.Layers.Theorems.Real.ExistsSampleGridClose
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem sample_bounds_of_deriv {g g' : ℝ → ℝ} {M l u t : ℝ} {N : ℕ}
    (hd : ∀ x, HasDerivAt g (g' x) x) (hM : ∀ x, l ≤ x → x ≤ u → |g' x| ≤ M)
    (hN : 0 < N) (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
