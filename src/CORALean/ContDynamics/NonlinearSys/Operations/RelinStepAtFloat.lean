import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInput
import CORALean.ContDynamics.NonlinearSys.Operations.LinInputFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RegionFloat
import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

/-!
# One step of the float re-linearization loop, at a given point

CORA's `linReach` at `alg = 'lin'`, computed in `𝕋`, which is one pass of [1, Alg. 1]:
from the set `R(t_k)` the step starts at, a region `Ω` it provably stays in
(`regionFloat`), the expansion point (`linPointFloat`), the matrices
(`linearizeFloat`), the input set holding the abstraction error over `Ω`
(`linInputFloat`), and then exactly one step of `LinearSys.reachFloatInput` of the
linearized system `δ̇ = A δ + ũ`, `ũ ∈ V`, `V` entering through the identity, in
CORA's deviation coordinates `δ = x - x✱`, shifted back after. It returns
`R(τ_k)`, the set over the whole step (line 13), and `R(t_{k+1})`.

CORA computes the error *after* the linear step, from the time-interval set it
encloses, and enlarges it until it holds; here the region comes first and is
checked, so one pass suffices and no loop over a growing error is needed. `Ω` and
the input box are widened by `x✱` and `u✱`, the remainder's expansion point having
to lie in the box its slopes are taken over.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}))` from `R = R(t_k)` under inputs in `U`, linearizing at the
expansion point `xs` the caller names, or `none` if the region check or the linear step
fails. -/
def NonlinearSys.FloatModel.relinStepAtFloat (fm : NonlinearSys.FloatModel 𝕋 n m)
    (U : Zonotope 𝕋 m) (options : LinearSys.ReachOptions 𝕋) (R : Zonotope 𝕋 n)
    (xs : Vec 𝕋 n) : Option (Zonotope 𝕋 n × Zonotope 𝕋 n) := do
  let Δt := options.timeStep                                        -- the paper's symbols
  let Ub := U.interval                                              -- U's box
  let Ω ← fm.regionFloat Δt R.interval Ub                           -- where the step stays
  let us := U.c                                                     -- u✱
  let X : Interval (Vec 𝕋 n) :=                                     -- Ω, holding x✱ too
    ⟨fun i => minimum (Ω.inf i) (xs i), fun i => maximum (Ω.sup i) (xs i)⟩
  let U' : Interval (Vec 𝕋 m) :=                                    -- U's box, holding u✱
    ⟨fun i => minimum (Ub.inf i) (us i), fun i => maximum (Ub.sup i) (us i)⟩
  let AB := fm.linearizeFloat xs us                                 -- A, B
  let V := fm.linInputFloat AB.1 AB.2 xs X U U'                     -- f(z✱) - A x✱ ⊕ B U ⊕ L
  let pt := fun v => (⟨0, v, fun j => j.elim0, ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope 𝕋 n)
  let lin : LinearSys 𝕋 n := ⟨AB.1⟩                                 -- δ̇ = A δ + ũ, ũ ∈ V
  let S ← lin.reachFloatInput (identityMat 𝕋 n)                     -- one step from R - x✱
    ⟨R ⊞ pt fun i => neg (xs i), V, 0, ToRat.toRat Δt⟩ options
  let Δτ ← S.1.head?                                                -- 13. R(τ_k) - x✱
  let Δ₁ ← S.2[1]?                                                  -- R(t_{k+1}) - x✱
  pure (Δτ ⊞ pt xs, Δ₁ ⊞ pt xs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
