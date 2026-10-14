module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
public import CORALean.ContSet.Zonotope.Float.Operations.ErrUp
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `Δε^{U,τ}_k(Δt, η)`, eq. (26), in floats

[1]'s eq. (26), `Real.MatExp.particularSolutionTauError`, computed in `𝕋`: the Euclidean `err` of
`[e^{At_k}] bPU(Δt)`, `bPU` the whole particular solution from order `0`, which is
`inputSolutionFloat`. `err` is `Zonotope.errUp`, the Euclidean radius of the box from above.
A tuning quantity: the step is sound at any value this takes.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. (26): `Δε^{U,τ}_k(Δt, η) = err([e^{At_k}] bPU(Δt))`, from above. -/
def LinearSys.particularSolutionTauErrorFloat (sys : LinearSys 𝕋 n)
    (eAtk : Interval (Mat 𝕋 n n)) (U₀ : Zonotope (Vec 𝕋 n)) (Δt : 𝕋) (η : ℕ) : 𝕋 :=
  (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eAtk
    (sys.inputSolutionFloat Δt η U₀)).errUp                               -- err([e^{At_k}] bPU(Δt))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
