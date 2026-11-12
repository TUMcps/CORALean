module

public import CORALean.Global.Float.Exp
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The accumulated error of restarted Krylov steps in a Lyapunov weight, in floats

[1, Sec. 7] in the weight `P` of an accepted `Krylov.lyapunovCertificateFloat`: the local 2-norm
errors `ε'_j` of the windows accumulate as `β_{j+1} = e^{μΔt_j} β_j + √b ε'_j`, `β_0 = 0`, `μ` the
weight's rate and `√b` the root of its upper bound, so that `β_N/√a` bounds the 2-norm error after
`N` windows (`Krylov.restartedErrorBoundFloat`) and `(β_N + √b ε'_N)/√a` the error at every time of
window `N` (`Krylov.windowErrorBoundFloat`). Every operation is rounded up; the exponential's
argument must be within `expUp`'s range for every window.

## Inputs
* `q` – squarings of the exponential
* `root` – upper bound of `√b`
* `rate` – rate `μ` of the weight
* `Δt` – window lengths
* `ε` – local 2-norm errors of the windows

## Output
* upper bound of `β_j`

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

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound `β_j` of the error in the weight: `β_0 = 0`, `β_{j+1} = e^{μΔt_j} β_j + √b ε'_j`. -/
def Krylov.restartedBetaFloat (q : ℕ) (root rate : 𝕋) (Δt ε : ℕ → 𝕋) : ℕ → 𝕋
  | 0 => zero
  | j + 1 =>
    addUp (mulUp (expUp q (mulUp rate (Δt j))) (Krylov.restartedBetaFloat q root rate Δt ε j))
      (mulUp root (ε j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
