import CORALean.HybridDynamics.HybridAutomaton

/-!
# The states and locations a hybrid run actually reaches

The definition is [1, Def. 3.4], `LinearSys.reachSet`'s shape at a `Run`
instead of a `Trajectory`: `reachSet` is every state some run from `ℓ₀` with an
initial state in `R₀` reaches at `ℓ`, the continuous part; `reachLocations` is
every `ℓ` it reaches at all, the discrete part — read off `reachSet` rather
than built separately, since a location is reached exactly when something is.

Not indexed by the thesis's real `r`: no `Run` here carries elapsed global
time at all, so both sets are read across every run, unbounded, the way
`Invariant` is rather than the way `InvariantOn` indexes by jump count.

`Theorems.ReachSetOuter`/`ReachLocationsOuter` put every run into these;
`ReachSetSubsetInvariant` puts `reachSet` inside what an `Invariant` supplies.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       11-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state some run of `HA` from `ℓ₀` with an initial state in `R₀`
reaches at `ℓ`: the exact reachable set, and not an enclosure of it. -/
def HybridAutomaton.reachSet (HA : HybridAutomaton S G L 𝕋 n) (R₀ : S n) (ℓ₀ ℓ : L) :
    Set (Vec ℝ n) :=
  {y | ∃ x, x ∈ construct R₀ ∧ HA.Run ℓ₀ x ℓ y}

/-- Every location some run from `ℓ₀` with an initial state in `R₀` reaches:
[1, Def. 3.4]'s discrete reachable set, as the locations `reachSet` is
nonempty at. -/
def HybridAutomaton.reachLocations (HA : HybridAutomaton S G L 𝕋 n) (R₀ : S n) (ℓ₀ : L) :
    Set L :=
  {ℓ | (HA.reachSet R₀ ℓ₀ ℓ).Nonempty}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
