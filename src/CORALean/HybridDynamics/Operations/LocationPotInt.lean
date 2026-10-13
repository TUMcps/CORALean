import CORALean.HybridDynamics.Definitions.Location

/-!
# `Location.potInt`

CORA's `potInt`, its scan: every pair of a transition and a reach set that may meet. A pair
`(i, j)` is listed unless the transition leads to `finalLoc` or `IsDisjoint` certifies guard `i`
and set `j` disjoint. CORA's test is `isIntersecting_` at `'approx'`; `IsDisjoint` is its
conservative negation, so an indeterminate pair is listed, which is the safe direction.

Indices are 0-based, transitions in order and sets inside each transition, as CORA's loops.
Not modelled: the final step, which swaps a lone hit on a hyperplane guard for the following
time-point set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `(transition, set)` index pairs of `ℓ` whose guard may meet the set, `finalLoc` skipped. -/
def Location.potInt [DecidableEq L] [∀ n, IsDisjoint (G n) (S n)] (ℓ : Location S G L 𝕋 n)
    (Rs : List (S n)) (finalLoc : L) : List (ℕ × ℕ) :=
  ℓ.trans.zipIdx.flatMap fun (e, i) =>
    if e.target = finalLoc then []   -- transitions into the final location are not scanned
    else Rs.zipIdx.filterMap fun (R, j) =>
      if IsDisjoint.isDisjoint e.guard R then none else some (i, j)  -- keep unless disjoint

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
