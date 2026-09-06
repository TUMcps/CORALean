import CORALean.NN.Layers.PolyRelaxation

/-!
# A polynomial relaxation carried along an affine conjugation

`Relaxation.ofAffineConj` transports an affine enclosure of `f` to `g t =
a f (b t) + d`, and the argument survives the raise in order unchanged: the
monomial basis is closed under scaling its argument, `(b t) ^ i = b ^ i · t ^ i`,
so the conjugation only reweights the coefficients. Nothing about the fit or
about the error bound is redone, which is what makes `tanh` cost a line here as
it does at order 1.

The two scalings land in different places, and that is the whole content of
`scaleCoeffs`: `b` folds into the monomials one power at a time, `a` multiplies
every coefficient once, and the additive `d` is `shiftConst`, the same shift
`ofSampling` performs for its own recentring.

Precision carries over exactly, not merely soundly — the transported error is
`a` times `f`'s, and `a` is precisely the factor by which the conjugation
stretches the deviation.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- The coefficients of `t ↦ a · p (b · t)`, where `p` has coefficients `c`. -/
def scaleCoeffs {n : ℕ} (c : Fin (n + 1) → ℝ) (a b : ℝ) : Fin (n + 1) → ℝ :=
  fun i => a * c i * b ^ (i : ℕ)

theorem evalPoly_scaleCoeffs {n : ℕ} (c : Fin (n + 1) → ℝ) (a b t : ℝ) :
    evalPoly (scaleCoeffs c a b) t = a * evalPoly c (b * t) := by
  show ∑ i : Fin (n + 1), a * c i * b ^ (i : ℕ) * t ^ (i : ℕ)
    = a * ∑ i : Fin (n + 1), c i * (b * t) ^ (i : ℕ)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow]
  ring


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A polynomial relaxation of `f` transported along `g t = a f (b t) + d`.
Only the coefficients move; the error scales by `a` and nothing is re-proved. -/
noncomputable def PolyRelaxation.ofAffineConj {f g : ℝ → ℝ} {n : ℕ} (P : PolyRelaxation f n)
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : ∀ t, g t = a * f (b * t) + d) :
    PolyRelaxation g n where
  coeffs l u := shiftConst (scaleCoeffs (P.coeffs (b * l) (b * u)) a b) d
  error l u := a * P.error (b * l) (b * u)
  sound {l u t} hl hu := by
    have hbl : b * l ≤ b * t := mul_le_mul_of_nonneg_left hl hb.le
    have hbu : b * t ≤ b * u := mul_le_mul_of_nonneg_left hu hb.le
    rw [evalPoly_shiftConst, evalPoly_scaleCoeffs, hg t]
    -- the conjugation's own scaling is all that separates the two deviations
    have heq : a * f (b * t) + d - (a * evalPoly (P.coeffs (b * l) (b * u)) (b * t) + d)
        = a * (f (b * t) - evalPoly (P.coeffs (b * l) (b * u)) (b * t)) := by
      ring
    rw [heq, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (P.sound hbl hbu) ha.le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
