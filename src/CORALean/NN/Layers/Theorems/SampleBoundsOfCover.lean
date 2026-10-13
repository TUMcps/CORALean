module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.SampleHi
public import CORALean.NN.Layers.Operations.SampleLo
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# A sampled range brackets a function

The mean value theorem between a point of the box and the sample nearest it: with `|g'| ≤ M`,
`g` moves by at most `M` times the distance, so the sampled range padded by the slack brackets
`g` on the whole box — at any samples inside it leaving no point further off than `dx`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sample_bounds_of_cover {g g' : ℝ → ℝ} {l u M dx : 𝕋}
    {p gLo gUp : Fin (N + 1) → 𝕋} {t : ℝ} (hd : ∀ x, HasDerivAt g (g' x) x)
    (hM : ∀ x, toReal l ≤ x → x ≤ toReal u → |g' x| ≤ toReal M)
    (hp : ∀ i, toReal l ≤ toReal (p i) ∧ toReal (p i) ≤ toReal u)
    (hcov : ∀ y : ℝ, toReal l ≤ y → y ≤ toReal u → ∃ i, |y - toReal (p i)| ≤ toReal dx)
    (hlo : ∀ i, toReal (gLo i) ≤ g (toReal (p i)))
    (hup : ∀ i, g (toReal (p i)) ≤ toReal (gUp i)) (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    toReal (sampleLo gLo M dx) ≤ g t
      ∧ g t ≤ toReal (sampleHi gUp M dx) := by -- --- PROOF ---
  have hM0 : 0 ≤ toReal M := le_trans (abs_nonneg _) (hM t hl hu)
  obtain ⟨i, hi⟩ := hcov t hl hu
  obtain ⟨hgl, hgu⟩ := hp i
  -- the mean value theorem between `t` and the sample it is nearest to
  have hlip : |g t - g (toReal (p i))| ≤ toReal M * |t - toReal (p i)| := by
    have hbound : ∀ x ∈ Set.Icc (toReal l) (toReal u), ‖g' x‖ ≤ toReal M := fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x hx.1 hx.2
    have hmv := (convex_Icc (toReal l) (toReal u)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hd x).hasDerivWithinAt) hbound ⟨hgl, hgu⟩ ⟨hl, hu⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have hslack : toReal M * |t - toReal (p i)| ≤ toReal (mulUp M dx) :=
    le_trans (mul_le_mul_of_nonneg_left hi hM0) (mul_le_mulUp M dx)
  have habs := abs_le.mp (hlip.trans hslack)
  have hmin := minimumOver_le gLo i
  have hmax := le_maximumOver gUp i
  have hsub := subDown_le_sub (minimumOver gLo) (mulUp M dx)
  have hadd := add_le_addUp (maximumOver gUp) (mulUp M dx)
  exact ⟨by rw [sampleLo]; linarith [hlo i], by rw [sampleHi]; linarith [hup i]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
