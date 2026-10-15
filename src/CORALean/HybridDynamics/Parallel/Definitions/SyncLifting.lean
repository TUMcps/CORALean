module

public import CORALean.HybridDynamics.Parallel.Definitions.Lifting

@[expose] public section

/-!
# A `Lifting` that can also conjoin guards

A synchronized transition fires when the guards of every participating component hold at once:
CORA's `synchronize` intersects the lifted guards. `ContSet` has no intersection, so the caller
supplies it, as `Lifting`'s sets are supplied: `guardAll gs` is a set in the product space for a
guard `gs i` (or none) on each component, containing every stack whose blocks meet theirs; an outer
bargain, as `Lifting`'s fields are.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ParallelHybridAutomaton.SyncLifting (S G : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] (n : Fin k → ℕ) (m : ℕ) extends
    ParallelHybridAutomaton.Lifting S G n m where
  guardAll : (∀ i, Option (G (n i))) → G (∑ i, n i)
  mem_guardAll (gs : ∀ i, Option (G (n i))) (x : ∀ i, Vec ℝ (n i))
    (hx : ∀ i g, gs i = some g → x i ∈ construct g) : stack x ∈ construct (guardAll gs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
