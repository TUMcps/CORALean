import CORALean.HybridDynamics.Operations.TransitionConvGuard

/-!
# `Transition.convGuard` is exactly guard and invariant

The new guard denotes the intersection of the old one and the invariant, with equality: stacking
the rows loses nothing. The reset and the target are untouched.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `construct` of the cut guard is the guard's intersection with the invariant. -/
theorem Transition.convGuard_guard_exact (e : Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (inv : HPolytope 𝕋 (Vec 𝕋 n)) :
    (e.convGuard inv).guard.construct = e.guard.construct ∩ inv.construct :=
  (HPolytope.intersection_exact e.guard inv).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
