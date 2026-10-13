import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope

/-!
# One step of a linearization, in deviation coordinates

CORA's `oneStep(linsys, Rdelta, ...)` and `Rti + p.x` in `linReach`, computed in `𝕋`:
the linearized system `δ̇ = A δ + ũ`, `ũ ∈ V` entering through the identity, run one
step of `LinearSys.reachFloatInput` from `R - x✱`, and both sets it returns shifted
back by `x✱`. It returns `R(τ_k)` and `R(t_{k+1})`.

What `V` holds is the caller's: `oneStepFloat_outer` asks that the field less its
linear part, `f(x, u) - A(x - x✱)`, lie in `V` along the run. The `'lin'` and `'poly'`
variants differ only in the `V` they build; this is [1, Alg. 1]'s line 13 at either.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}))` of `δ̇ = A δ + ũ`, `ũ ∈ V`, from `R - x✱`, shifted back by
`x✱`; `none` if the linear step fails. -/
def NonlinearSys.oneStepFloat (A : Mat 𝕋 n n) (xs : Vec 𝕋 n) (V R : Zonotope (Vec 𝕋 n))
    (options : LinearSys.ReachOptions 𝕋) : Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) := do
  let pt := fun v => (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n))
  let lin : LinearSys 𝕋 n := ⟨A⟩                                    -- δ̇ = A δ + ũ, ũ ∈ V
  let S ← lin.reachFloatInput (identityMat 𝕋 n)                     -- one step from R - x✱
    ⟨R ⊞ pt fun i => neg (xs i), V, 0, ToRat.toRat options.Δt⟩ options
  let Δτ ← S.1.head?                                                -- R(τ_k) - x✱
  let Δ₁ ← S.2[1]?                                                  -- R(t_{k+1}) - x✱
  pure (Δτ ⊞ pt xs, Δ₁ ⊞ pt xs)                                     -- Rti + p.x, Rtp + p.x

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
