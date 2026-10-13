module

public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.potOut`

CORA's `potOut`: the reach sets in the index ranges `minInd(i)..maxInd(i)` are cut to the
invariant, and the last set is dropped when it no longer meets the invariant. CORA runs it on the
time-interval and on the time-point sets alike, so here it takes one list of sets.

Indices are CORA's 1-based ones, with `minInd` clipped to `1`. The test is `IsDisjoint`, the
conservative negation of CORA's `isIntersecting_`, so an uncertain last set is kept. Not
modelled: the matching `time` and `error` lists CORA truncates, and the polytope conversion.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Rs` with the indexed sets cut to the invariant, the last one dropped if it misses it. -/
def Location.potOut [∀ n, Intersection (S n) (Vec ℝ n)] [∀ n, IsDisjoint (S n) (S n)]
    (ℓ : Location S S L 𝕋 n) (Rs : List (S n)) (minInd maxInd : List ℕ) : List (S n) :=
  -- set `k` (0-based) is cut when `minInd(i) ≤ k + 1 ≤ maxInd(i)` for some `i`
  let cut := Rs.mapIdx fun k R =>
    if (minInd.zip maxInd).any (fun (a, b) => max a 1 ≤ k + 1 && k + 1 ≤ b)
    then Intersection.intersection ℓ.inv R else R
  match cut.getLast? with
  | some last => if IsDisjoint.isDisjoint ℓ.inv last then cut.dropLast else cut
  | none => cut

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
