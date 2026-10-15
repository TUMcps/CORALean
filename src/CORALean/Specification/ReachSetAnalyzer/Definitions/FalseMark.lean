module

public import CORALean.Specification.AtomicProposition.Operations.CanBeFalse
public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Covers
public import CORALean.Specification.ReachSetAnalyzer.Operations.MaskOk

@[expose] public section

/-!
# What marks a time as possibly false

Proposition `k` is marked as possibly false at the time `t` of a signal of duration `d` by the set
`set` at location `loc` in the time interval `[lo,hi]` when the mask lets the proposition through,
the proposition can be false on the set, and the interval covers `t`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `set` in `[lo,hi]` marks `t` as a time where proposition `k` can be false. -/
def ReachSetAnalyzer.FalseMark (obj : ReachSetAnalyzer S n) (k : String) (set : S n) (loc : ℕ)
    (lo hi d t : ℝ) : Prop :=
  ∃ ap, (k, ap) ∈ obj.aps ∧ obj.maskOk k lo hi = true ∧
    ap.canBeFalse (𝕋 := 𝕋) set loc = true ∧ FiniteKleeneSignalBuilder.Covers d t lo hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
