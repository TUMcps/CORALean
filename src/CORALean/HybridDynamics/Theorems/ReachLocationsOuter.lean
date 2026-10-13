module

public import CORALean.HybridDynamics.Theorems.ReachSetOuter

@[expose] public section

/-!
# `reachLocations` contains every location a run ends in

`reachSet_outer`'s discrete counterpart: the location a run reaches has a
state in `reachSet` by construction, namely the one the run ends at, and that
is exactly what `reachLocations` asks for.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this to say a location is visited at all; reach for
`reachSet_outer` to say by which state. -/
theorem HybridAutomaton.Run.reachLocations_outer {HA : HybridAutomaton S G L 𝕋 n} {R₀ : S n}
    {ℓ₀ ℓ : L} {x y : Vec ℝ n} (run : HA.Run ℓ₀ x ℓ y) (hx : x ∈ construct R₀) :
    ℓ ∈ HA.reachLocations R₀ ℓ₀ :=
  ⟨y, run.reachSet_outer hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
