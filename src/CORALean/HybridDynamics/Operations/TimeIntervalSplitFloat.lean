module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.HybridDynamics.Operations.InputSetFloat
public import CORALean.HybridDynamics.Operations.TimeIntervalFloat
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Location.timeIntervalSplitFloat`

`Location.timeIntervalSplit` computed in `𝕋`, its input contribution split
as `reachFloatInput` splits it: `ℓ.inputSetFloat = ũ ⊕ Ũ` by `Recenter`, `ũ` the stored
center. The constant's contribution `∫₀ᵗ e^{Aσ}dσ ũ` is an admissible input of
`[0, ũ]`, so `inputSolutionFloat` at that segment holds it at every `t ≤ r`,
where the exact step uses `expIntegral` and `constCorrectionMatrix`; `Ũ` holds
the origin, so `inputSolutionFloat Ũ` holds its share at every `t ≤ r` too.
The location's combined input set `B U ⊕ c ⊕ E W` need not hold the origin.

## Inputs
* `ℓ` – float location
* `r` – time step
* `η` – Taylor order
* `X₀` – initial zonotope

## Output
* float stay enclosure with split input

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of a stay of length up to `r` from `X₀`, at Taylor order `η`,
the combined input `ℓ.inputSetFloat` split at its center, [1, Eq. 4]. -/
def Location.timeIntervalSplitFloat (ℓ : Location 𝒵[𝕋] G L 𝕋 n)
    (r : 𝕋) (η : ℕ)
    (X₀ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  -- 1. `{ũ}`, the stored center of the combined input set
  let ũ := (Interval.point ℓ.inputSetFloat.c).zonotope
  -- 2. `Ũ ← U - ũ`, holding the origin
  let Ũ := Recenter.recenter ℓ.inputSetFloat
  -- 3. `{0}`
  let O := (Interval.point fun _ => zero).zonotope
  -- 4. `H^R(τ_0)`, the homogeneous solution
  let HR := ℓ.timeIntervalFloat r η X₀
  -- 5. `P̃^R(τ_0)`, the constant's share, from the segment `[0, ũ]`
  let PuR := ℓ.dynamics.inputSolutionFloat r η (LinComb.linComb O ũ)
  -- 6. `P^R(r)`, the share of `Ũ`
  let PU := ℓ.dynamics.inputSolutionFloat r η Ũ
  -- 7. `R(τ_0) ← H^R(τ_0) ⊕ P̃^R(τ_0) ⊕ P^R(r)`
  HR ⊞ PuR ⊞ PU

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
