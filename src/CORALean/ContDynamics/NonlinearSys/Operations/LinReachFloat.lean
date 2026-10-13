import CORALean.ContDynamics.LinearSys.Operations.PostDeltaFloat
import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAlg
import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyFloat
import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
import CORALean.ContDynamics.NonlinearSys.Operations.LinPointFloat
import CORALean.ContDynamics.NonlinearSys.Operations.LinearizeFloat
import CORALean.ContDynamics.NonlinearSys.Operations.OneStepFloat
import CORALean.ContDynamics.NonlinearSys.Operations.RegionFloat

/-!
# One step of `linReach` at `alg = 'lin'` or `'poly'`, in floats

CORA's `linReach`, [1, Alg. 1] lines 3-14, computed in `𝕋` from a `FloatHessModel`:
the checked region `Ω` (`regionFloat`), the expansion point, `A` and `B`, and then the
input set `V = f(z✱) ⊕ B(U - u✱) ⊕ L` one linearized step is run with
(`oneStepFloat`). `L` is what `alg` selects. At `'lin'` it is `hessRemainder` over
`Ω × U`, CORA's `priv_abstrerr_lin` at `tensorOrder = 2`. At `'poly'` it is
`abstrErrPolyFloat`: `Rdiff`, CORA's `aux_deltaReach`, is `postDeltaFloat` of the
`'lin'` linearization from `Rdelta = R - x✱`, and the static error is taken over
`Rdelta` reduced to `errorOrder`, CORA's `Zdelta`.

As in `relinStepFloat`, the region is checked before the error rather than the
error enlarged until it holds, so CORA's `while perfIndCurr > 1` loop is a
single pass that cannot fail to terminate.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}))` from `R = R(t_k)` under inputs in `U`, abstracting by `alg`,
or `none` if the region check, the order search or the linear step fails. -/
def NonlinearSys.FloatHessModel.linReachFloat (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (alg : NonlinearSys.LinReachAlg) (U : Zonotope (Vec 𝕋 m)) (options : LinearSys.ReachOptions 𝕋)
    (R : Zonotope (Vec 𝕋 n)) : Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) := do
  let Δt := options.Δt                                        -- the paper's symbols
  let Ub := U.interval                                              -- U's box
  let Ω ← fm.regionFloat Δt R.interval Ub                           -- where the step stays
  let xs := (fm.linPointFloat Δt R U).1                             -- 3. x✱
  let us := U.c                                                     -- u✱
  let X : Interval (Vec 𝕋 n) :=                                     -- Ω, holding x✱ too
    ⟨fun i => minimum (Ω.inf i) (xs i), fun i => maximum (Ω.sup i) (xs i)⟩
  let U' : Interval (Vec 𝕋 m) :=                                    -- U's box, holding u✱
    ⟨fun i => minimum (Ub.inf i) (us i), fun i => maximum (Ub.sup i) (us i)⟩
  let A := (fm.linearizeFloat xs us).1                              -- 3. A
  let B := (fm.linearizeFloat xs us).2                              -- 3. B
  let f₀ := fm.f (Interval.point xs) (Interval.point us)            -- [f(x✱, u✱)]
  let V := fun (L : Zonotope (Vec 𝕋 n)) =>                                -- f(z✱) ⊕ B(U - u✱) ⊕ L
    (f₀.zonotope ⊞ Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B
      (Recentre.recentre U)) ⊞ L
  let Vlin := V (fm.hessRemainder A B xs us X U').zonotope          -- priv_abstrerr_lin
  match alg with
  | .lin => NonlinearSys.oneStepFloat A xs Vlin R options
  | .poly errorOrder => do
    let lin : LinearSys 𝕋 n := ⟨A⟩                                  -- linsys
    let η ← lin.reachOrderFloat Δt Δt options.η           -- η, admissible
    let Rdelta := R ⊞ (⟨0, fun i => neg (xs i), fun j => j.elim0,  -- Rinit + (-p.x)
      ⟨fun _ => zero, fun _ => zero⟩⟩ : Zonotope (Vec 𝕋 n))
    let Rdiff := lin.postDeltaFloat Δt η Rdelta Vlin                -- aux_deltaReach
    let Zdelta := Reduce.reduce Rdelta errorOrder                   -- reduce(Rdelta, errorOrder)
    let Vpoly := V (fm.abstrErrPolyFloat A B xs us X U' Zdelta Rdiff)  -- priv_abstrerr_poly
    NonlinearSys.oneStepFloat A xs Vpoly R options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
