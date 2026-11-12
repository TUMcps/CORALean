module

public import CORALean.HybridDynamics.Definitions.ReachQueue
public import CORALean.HybridDynamics.HybridAutomaton
public import CORALean.HybridDynamics.Operations.JumpFloat
public import CORALean.HybridDynamics.Operations.ZonoGirardBoxFloat
public import CORALean.ContSet.HPolytope.Float.Operations.Hyperplane
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Location.queueJumpFloat`

The jump of one crossing of a guard in CORA's `hybridAutomaton/reach`: the sets of the group are
cut by the hyperplane guard and boxed along the basis `B` (`Location.zonoGirardBoxFloat`), a box
with `sup < inf` is an empty cut and gives no jump (CORA's `aux_removeEmptySets`), and the reset
maps the box to the set that waits for the target location. The jump time is from
`tlo + first Δt` to `thi + (last + 1) Δt`. `none` where the guard is not a bare hyperplane.

## Inputs
* `ℓ` – location
* `B` – basis
* `Δ` – time step
* `idx` – branch number
* `tlo` – lower end of the start time
* `thi` – upper end of the start time
* `Rs` – time-interval sets of the stay
* `grp` – transition and the set indices of one crossing

## Output
* the entry for the target location, none for an empty cut; none on failure
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The queue entry of a crossing, none for an empty cut, `none` at the outer level for a guard
that is not a hyperplane. -/
def Location.queueJumpFloat
    (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (B : Mat 𝕋 n n) (Δ : ℚ)
    (idx : ℕ) (tlo thi : ℚ) (Rs : List (Zonotope (Vec 𝕋 n))) (grp : ℕ × List ℕ) :
    Option (Option (HybridPending L 𝕋 n)) := do
  let e ← ℓ.trans[grp.1]?                                           -- the transition
  let (nv, γ) ← e.guard.hyperplane?                                 -- n·x = γ
  match grp.2, grp.2.filterMap (fun j => Rs[j]?) with
  | j₀ :: _, R₀ :: Rr =>
    let box := Location.zonoGirardBoxFloat B R₀ Rr nv γ             -- the cuts, joined
    if box.representsa_emptySet then pure none                      -- an empty cut
    else pure (some ⟨e.target,
      e.jumpFloat (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B box.zonotope),
      tlo + j₀ * Δ, thi + ((grp.2.getLastD j₀ : ℕ) + 1) * Δ, some idx⟩)
  | _, _ => pure none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
