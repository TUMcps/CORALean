import CORALean.ContDynamics.LinearSys.MatExp.Theorems.GenMinusFloat
import CORALean.Global.Float.GenOpNorm

/-!
# `genOpNorm₂` of the true `G^{(-)}_h` is under the float upper bound

For a matrix `E = e^{AΔt}` that `[e^{AΔt}]` holds, the true generators `(E - I_n) G_h` are under
`genMinus` in magnitude (`abs_genMinus_le`), and so their `genOpNorm₂` is under `genOpNormUp`
of the float ones. This is the float upper bound on `genOpNorm₂` that [1]'s `Δε^h_k`, eq. (23),
needs.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The true generators `(E - I_n)G_h`, under `genMinus` in magnitude, have `genOpNorm₂` under
`genOpNormUp`. -/
theorem MatExp.genOpNorm₂_genMinus_le (p : ℕ) {eA : Interval (Mat 𝕋 n n)} {E : Mat ℝ n n}
    (hE : E ∈ eA.construct) (H : Zonotope 𝕋 n) :
    genOpNorm₂ (fun l : Fin H.h => (E - 1) *ᵥ fun i => toReal (H.G l i))
      ≤ toReal (genOpNormUp p (MatExp.genMinus eA H)) :=
  genOpNorm₂_le_genOpNormUp p fun l j =>
    (MatExp.abs_genMinus_le hE H l j).trans (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
