module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.LyapunovCertificateFloatSound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpLeWeighted

@[expose] public section

/-!
# An accepted Lyapunov weight bounds the growth of `e^{tA}`

For the real matrix `A` of the floats and an accepted weight
(`Krylov.lyapunovCertificateFloat_sound`), `Krylov.norm_exp_le_weighted` gives `‖e^{tA}x‖₂ ≤
√(upper/lower) e^{rate·t}‖x‖₂` for `t ≥ 0`: [1, Eq. 3.4]'s growth bound with the weight's
condition number in place of Gershgorin's rate, sharp for a stable non-normal `A` where
`Krylov.quadBoundUp A` is large.

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `L` – factor of `P - aI`
* `a` – shift
* `x` – vector
* `t` – time

## Hypotheses
* `hok` – the weight was accepted
* `ht` – time nonnegative

## Conclusion
* the 2-norm of `e^{tA}x` grows by at most `√(upper/lower) e^{rate·t}`

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An accepted weight: `‖e^{tA}x‖₂ ≤ √(upper/lower) e^{rate·t}‖x‖₂` for `t ≥ 0`. -/
theorem Krylov.lyapunovCertificateFloat_norm_exp_le (A P L : Mat 𝕋 n n) (a : 𝕋)
    (hok : (Krylov.lyapunovCertificateFloat A P L a).ok = true) (x : Vec ℝ n) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    ‖exp (t • toRealMat A) *ᵥ x‖₂ ≤
      Real.sqrt (toReal (Krylov.lyapunovCertificateFloat A P L a).upper /
        toReal (Krylov.lyapunovCertificateFloat A P L a).lower) *
        Real.exp (toReal (Krylov.lyapunovCertificateFloat A P L a).rate * t) *
        ‖x‖₂ := by -- --- PROOF ---
  -- the sound weight, against the real theorem
  obtain ⟨hS, ha0, hb0, ha, hb, hPA⟩ := Krylov.lyapunovCertificateFloat_sound A P L a hok
  exact _root_.CORALean.Krylov.norm_exp_le_weighted (toRealMat A) (toRealMat P) _ _ _ hS hPA ha hb
    ha0 hb0.le x ht

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
