module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumFloat

@[expose] public section

/-!
# The set every input contributes over one step, in floats, as CORA computes it

`inputSolutionEntrywise` of [1] computed in `𝕋`: the orders up to `η` by `inputTaylorSumFloat`, and
everything past `η` in `MatExp.intervalInputRemainderEntrywise`, the float `E(Δt,η)·Δt` with the
entry's own bound `W`.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `W` – float bound on the entrywise remainder
* `V` – float input zonotope

## Output
* float zonotope of everything the input contributes over one step

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⊕ᵢ [Aⁱr^{i+1}/(i+1)!] V ⊕ [E(r,η)·r] V`, the remainder entrywise. -/
def LinearSys.inputSolutionEntrywiseFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (W : Mat 𝕋 n n) (V : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  sys.inputTaylorSumFloat r V η ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
    (ContSet := 𝒵[𝕋]) (MatExp.intervalInputRemainderEntrywise r W) V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
