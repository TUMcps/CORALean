module

public import CORALean.Specification.AtomicProposition.Operations.CanBeTrue
public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Covers
public import CORALean.Specification.ReachSetAnalyzer.Operations.MaskOk

@[expose] public section

/-!
# What marks a time as possibly true

Proposition `k` is marked as possibly true at the time `t` of a signal of duration `d` by the set
`set` at location `loc` in the time interval `[lo,hi]` when the mask lets the proposition through,
the proposition can be true on the set, and the interval covers `t`.

## Inputs
* `obj` – analyzer
* `k` – proposition key
* `set` – reachable set
* `loc` – location
* `lo` – interval lower bound
* `hi` – interval upper bound
* `d` – signal duration
* `t` – time

## Output
* the set marks the time as possibly true for the proposition
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, IsDisjoint (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `set` in `[lo,hi]` marks `t` as a time where proposition `k` can be true. -/
def ReachSetAnalyzer.IsTrueMark (obj : ReachSetAnalyzer ℝ S n) (k : String) (set : S n) (loc : ℕ)
    (lo hi d t : ℝ) : Prop :=
  ∃ ap, (k, ap) ∈ obj.aps ∧ obj.maskOk k lo hi = true ∧
    ap.canBeTrue (𝕋 := 𝕋) set loc = true ∧ FiniteKleeneSignalBuilder.Covers d t lo hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
