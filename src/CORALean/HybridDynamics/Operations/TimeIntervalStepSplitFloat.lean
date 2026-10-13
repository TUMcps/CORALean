import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.HybridDynamics.Operations.TimeIntervalStepFloat

/-!
# `Location.timeIntervalStepSplitFloat`

`Location.timeIntervalStepSplit` computed in `𝕋`, its input contribution split
as `reachFloatInput` splits it: `ℓ.U = ũ ⊕ Ũ` by `Recentre`, `ũ` the stored
centre. The constant's contribution `∫₀ᵗ e^{Aσ}dσ ũ` is an admissible input of
`[0, ũ]`, so `inputSolutionFloat` at that segment holds it at every `t ≤ r`,
where the exact step uses `expIntegral` and `constCorrectionMatrix`; `Ũ` holds
the origin, so `inputSolutionFloat Ũ` holds its share at every `t ≤ r` too.
The location's input set need not hold the origin.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of a stay of length up to `r` from `X₀`, at Taylor order `η`,
the input `ℓ.U` split at its centre, [1, Alg. 3]. -/
def Location.timeIntervalStepSplitFloat (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n)
    (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let ũ := (Interval.point ℓ.U.c).zonotope                         -- {ũ}, ℓ.U's stored centre
  let Ũ := Recentre.recentre ℓ.U                                    -- Ũ = U - ũ, holding 0
  let O := (Interval.point fun _ => zero).zonotope                  -- {0}
  let HR := ℓ.timeIntervalStepFloat r η X₀                          -- H^R(τ_0)
  let PuR := ℓ.dynamics.inputSolutionFloat r η (LinComb.linComb O ũ) -- P̃^R(τ_0), from [0, ũ]
  let PU := ℓ.dynamics.inputSolutionFloat r η Ũ                     -- P^R(r)
  HR ⊞ PuR ⊞ PU                                                     -- R(τ_0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
