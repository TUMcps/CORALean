module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSumFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContSet.Zonotope.Float.Operations.ErrUp
public import CORALean.ContSet.Zonotope.Float.Instances

@[expose] public section

/-!
# `Δε^U_k(Δt, η)`, eq. (25), in floats

[1]'s eq. (25), `Real.MatExp.particularSolutionError`, computed in `𝕋`: the Euclidean `err` of
the correlated and the decorrelated summands of the particular solution's outer approximation,
both mapped by `[e^{At_k}]`, added upward. The correlated summand is `(Σᵢ Ãᵢ)U₀ ⊕ E Δt U₀` with
`Σᵢ Ãᵢ` one interval matrix (`particularCoeffSum`), the decorrelated `⊕ᵢ ÃᵢU₀ ⊕ E Δt U₀`
(`inputTaylorSumTailFloat`), each from order `1`. `err` is `Zonotope.errUp`, the Euclidean
radius of the float zonotope's box from above, as eq. (11) has it, and not the sup-norm `errOp`
of CDC'20. A tuning quantity: the step is sound at any value this takes.

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

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. (25): `Δε^U_k(Δt, η) = err([e^{At_k}] ((Σᵢ Ãᵢ) U₀ ⊕ E Δt U₀))
+ err([e^{At_k}] (⊕ᵢ ÃᵢU₀ ⊕ E Δt U₀))`, orders `1 … η`, from above. -/
def LinearSys.particularSolutionErrorFloat (sys : LinearSys 𝕋 n) (eAtk : Interval (Mat 𝕋 n n))
    (U₀ : Zonotope (Vec 𝕋 n)) (Δt : 𝕋) (η : ℕ) : 𝕋 :=
  let eA := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- [e^{At_k}] ·
    (S := fun k => Zonotope (Vec 𝕋 k)) eAtk
  let rem := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.intervalInputRemainder (Interval.point sys.A) Δt η) U₀           -- E(Δt,η) Δt U₀
  let corr := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k))
    (MatExp.particularCoeffSum (Interval.point sys.A) Δt 1 η) U₀ ⊞ rem        -- (Σᵢ Ãᵢ)U₀ ⊕ E Δt U₀
  let decorr := sys.inputTaylorSumTailFloat Δt U₀ η ⊞ rem                      -- ⊕ᵢ ÃᵢU₀ ⊕ E Δt U₀
  addUp (eA corr).errUp (eA decorr).errUp                                      -- err(·) + err(·)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
