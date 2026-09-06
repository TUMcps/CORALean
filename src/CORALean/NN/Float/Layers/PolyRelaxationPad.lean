import CORALean.NN.Float.Layers.ActivationPoly
import CORALean.NN.Layers.PolyRelaxationPad

/-!
# A float relaxation read at a higher degree

The exact padding with `0` replaced by `zero`, and there for the same reason: an
order pattern [1, Eq. 23] gives each neuron of a layer its own order, one
activation layer evaluates one coefficient list, so the fits have to meet at a
common degree.

Nothing rounds and nothing is lost. `zero` is exact and every added term is
`0 · t ^ j`, so `sound` carries over through `Real.evalPoly_padCoeffs` with the
error untouched, and a neuron below the layer's maximum order pays nothing.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {k M : ℕ}

/-- Coefficients read at degree `M`, the ones the original does not have `zero`. -/
def padCoeffs (c : Fin (k + 1) → 𝕋) (M : ℕ) : Fin (M + 1) → 𝕋 :=
  fun j => if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else zero

/-- Read as reals, the padded coefficients are the exact padding. -/
theorem toReal_padCoeffs (c : Fin (k + 1) → 𝕋) (M : ℕ) (j : Fin (M + 1)) :
    toReal (padCoeffs c M j) = Real.padCoeffs (fun i => toReal (c i)) M j := by -- --- PROOF ---
  show toReal (if h : (j : ℕ) < k + 1 then c ⟨(j : ℕ), h⟩ else zero)
    = if h : (j : ℕ) < k + 1 then toReal (c ⟨(j : ℕ), h⟩) else 0
  -- the padded slot is the only one that moves, and `zero` reads as `0`
  by_cases h : (j : ℕ) < k + 1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, toReal_zero]

/-- A float relaxation at a higher degree, which is how the neurons of one layer
meet at a common one. -/
def PolyRelaxation.padTo (P : PolyRelaxation 𝕋 σ k) (M : ℕ) (h : k ≤ M) :
    PolyRelaxation 𝕋 σ M where
  coeffs l u := padCoeffs (P.coeffs l u) M
  error := P.error
  sound {l u _t} hl hu := by
    -- the padded polynomial is the original one, so `sound` is the original's
    have hco : (fun j => toReal (padCoeffs (P.coeffs l u) M j))
        = Real.padCoeffs (fun i => toReal (P.coeffs l u i)) M := by
      funext j
      exact toReal_padCoeffs (P.coeffs l u) M j
    rw [hco, Real.evalPoly_padCoeffs _ h]
    exact P.sound hl hu


-- =======================================  MAIN THEOREM  ======================================= --

/-- Padding leaves the error alone, which is what makes it free. -/
theorem PolyRelaxation.padTo_error (P : PolyRelaxation 𝕋 σ k) (M : ℕ) (h : k ≤ M) :
    (P.padTo M h).error = P.error := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
