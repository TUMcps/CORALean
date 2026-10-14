module

public import CORALean.HybridDynamics.HybridAutomaton
public import CORALean.HybridDynamics.Operations.GuardIntersectFloat
public import CORALean.HybridDynamics.Operations.JumpFloat
public import CORALean.HybridDynamics.Operations.LocationReachFloat

@[expose] public section

/-!
# `HybridAutomaton.reachFloat`

CORA's `hybridAutomaton/reach`, at float zonotopes and with halfspace guards
and invariants: the stay in `ℓ` from `X₀` is enclosed by `Location.reachFloat`;
every outgoing transition cuts those sets to its guard by
`Location.guardIntersectFloat` and, where the guard is met, resets the cut by
`Transition.jumpFloat` and continues in the target location from there. The
result lists every time-interval set with the location it belongs to.

Bounded twice: at most `K` jumps, a depth CORA leaves to the horizon, and every
stay to `tFinal`. CORA shortens a later stay by the time already spent; here
each stay is taken over the whole `tFinal`, which encloses more and is no less
sound, a run of duration at most `tFinal` having no stay longer than that.
One branch per transition and jump depth, CORA's `'box'` hull standing for all
the time steps that meet the guard.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The time-interval sets of every run from `X₀` at `ℓ` with at most `K` jumps and
stays of at most `tFinal`, each paired with its location. -/
def HybridAutomaton.reachFloat
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) :
    ℕ → L → Zonotope (Vec 𝕋 n) → Option (List (L × Zonotope (Vec 𝕋 n)))
  | K, ℓ, X₀ => do
    let Rs ← (HA.loc ℓ).reachFloat tFinal options X₀               -- the stay in ℓ
    let here := Rs.map fun R => (ℓ, R)
    match K with
    | 0 => pure here                                                -- no jump left
    | K + 1 =>
      let next ← (HA.loc ℓ).trans.mapM fun e =>                     -- every transition out
        match (HA.loc ℓ).guardIntersectFloat e.guard Rs with        -- R ∩ inv ∩ guard
        | none => pure []                                           -- the guard is never met
        | some Rg => HA.reachFloat tFinal options K e.target        -- on from the reset image
            (e.jumpFloat Rg.zonotope)
      pure (here ++ next.flatten)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
