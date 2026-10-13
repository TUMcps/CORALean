import CORALean.ContSet.SpectraShadow.Float.Operations.DualCertified
import CORALean.Global.Float.NoNaN

/-!
# `SpectraShadow.representsa_emptySet`, over a floating-point scalar

CORA decides emptiness with a semidefinite program; here its infeasibility certificate is the
caller's and is checked: `Y` symmetric and diagonally dominant (so `⪰ 0`), `tr(Aₗ Y) = 0` for
every variable (`dualCertified` along the direction `0`) and `tr(A₀ Y) < 0`, both decided exactly
in ℚ. Then no `β` makes the inequality hold. Sufficient only: `true` proves the set empty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps ToRat

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.representsa_emptySet (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Y : Mat 𝕋 S.k S.k) : Bool :=
  let traceA₀ : ℚ := ∑ r, ∑ j, toRat (S.A₀ r j) * toRat (Y j r)
  S.dualCertified (fun _ => zero) Y && decide (traceA₀ < 0) && noNaN (𝕋 := 𝕋) S.A₀

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
