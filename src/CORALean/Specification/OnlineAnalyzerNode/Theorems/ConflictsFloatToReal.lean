module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.Conflicts
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ConflictsFloat
public import CORALean.Specification.STLInterval.Operations.ToRealInterval
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.WithinTolFloatIff

@[expose] public section

/-!
# `conflictsFloat` is `conflicts` on the intervals read as reals

Over a float scalar `conflictsFloat` compares the bounds and tests `withinTol` exactly on the reals
they denote, so it gives what `conflicts` gives on the tolerance, the bound and the intervals read
as reals.

## Inputs
* `eps` – machine epsilon
* `lb` – lower bound of the observation
* `lc` – lower bound is closed
* `ps` – propagated intervals

## Hypotheses
* none

## Conclusion
* the float test is the exact one on the reals denoted
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.conflictsFloat_toReal (eps : 𝕋) (lb : Option (WithTop 𝕋)) (lc : Bool)
    (ps : List (STLInterval 𝕋)) : -- --- CONCL ---
    OnlineAnalyzerNode.conflictsFloat eps lb lc ps = OnlineAnalyzerNode.conflicts (toReal eps)
      (lb.map (·.map toReal)) lc (ps.map STLInterval.toRealInterval) := by -- --- PROOF ---
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rcases p with _ | ⟨l, u, lc', rc', _, _, _⟩
    · -- nothing propagated to that parent
      simpa [OnlineAnalyzerNode.conflictsFloat, OnlineAnalyzerNode.conflicts,
        STLInterval.supremum, STLInterval.toRealInterval] using ih
    · -- the upper bound and the observation compared exactly
      have hsup : (STLInterval.toRealInterval
          (STLInterval.nonempty l u lc' rc' ‹_› ‹_› ‹_›)).supremum =
            ⟨some (u.map toReal), rc'⟩ := by
        rcases u with _ | u <;> rfl
      rw [List.map_cons]
      conv_rhs => unfold OnlineAnalyzerNode.conflicts
      rw [hsup]
      conv_lhs => unfold OnlineAnalyzerNode.conflictsFloat
      simp only [STLInterval.supremum]
      rcases lb with _ | lb'
      · rfl
      · simp only [Option.map_some]
        open Classical in
        by_cases hc : STLInterval.toEReal u > STLInterval.toEReal lb' ∨
            (STLInterval.withinTolFloat eps u lb' = true ∧ rc' = true ∧ lc = true)
        · rw [if_pos hc, if_pos (by simpa [STLInterval.withinTolFloat_iff] using hc)]
        · rw [if_neg hc, if_neg (by simpa [STLInterval.withinTolFloat_iff] using hc)]
          exact ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
