module

public import CORALean.NN.Layers.Definitions.PolyAffineConj
public import CORALean.NN.Layers.Theorems.Real.EvalPolyScaleCoeffs
public import CORALean.NN.Layers.Theorems.Real.EvalPolyShiftConst

@[expose] public section

/-!
# A polynomial relaxation carried along an affine conjugation is sound

ℝ-only, the reweighting being exact: the conjugation's own scaling is all that separates the two
deviations, so precision carries over exactly — the transported error is `a` times `f`'s, and `a`
is precisely the factor by which the conjugation stretches the deviation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofAffineConj_sound {f g : ℝ → ℝ} {n : ℕ} {P : CORALean.PolyRelaxation ℝ n}
    (hP : P.Sound f) {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : ∀ t, g t = a * f (b * t) + d) :
    (PolyRelaxation.ofAffineConj P a b d).Sound g := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  have hbl : b * l ≤ b * t := mul_le_mul_of_nonneg_left hl hb.le
  have hbu : b * t ≤ b * u := mul_le_mul_of_nonneg_left hu hb.le
  show |g t - evalPoly (shiftConst (scaleCoeffs (P.coeffs (b * l) (b * u)) a b) d) t|
    ≤ a * P.error (b * l) (b * u)
  rw [evalPoly_shiftConst, evalPoly_scaleCoeffs, hg t]
  -- the conjugation's own scaling is all that separates the two deviations
  have heq : a * f (b * t) + d - (a * evalPoly (P.coeffs (b * l) (b * u)) (b * t) + d)
      = a * (f (b * t) - evalPoly (P.coeffs (b * l) (b * u)) (b * t)) := by
    ring
  rw [heq, abs_mul, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left (hP.sound hbl hbu) ha.le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
