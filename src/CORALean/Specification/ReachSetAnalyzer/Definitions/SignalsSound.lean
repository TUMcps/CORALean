module

public import CORALean.Specification.AtomicProposition.Definitions.Holds
public import CORALean.Specification.FiniteKleeneSignalBuilder.Definitions.Covers
public import CORALean.Specification.FiniteSignal.Definitions.IsValid
public import CORALean.Specification.FiniteSignal.Operations.At
public import CORALean.Specification.Kleene.Kleene
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Entry
public import CORALean.Specification.ReachSetAnalyzer.Operations.MaskOk

@[expose] public section

/-!
# When the signals are sound for a branch

The signals `out` of an analyzer are sound for the entries `w` of `R` (a branch of the tree of
reach sets) when each is a valid three-valued signal of duration `d` and, at every time `t` of
`[0,d]` where it is true, every state of every set of those entries that the mask lets through and
whose time interval covers `t` satisfies the proposition, and where it is false, none does. This is
the meaning of a Kleene value for a set of states: true if all of them satisfy the proposition,
false if none does.

## Inputs
* `obj` – analyzer
* `d` – signal duration
* `R` – tree of reach sets
* `w` – branch entries
* `out` – signal of each proposition

## Output
* the signals are valid and sound for the branch's entries
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The signals `out` are sound for the entries `w` of `R` of the analyzer `obj`. -/
def ReachSetAnalyzer.SignalsSound (obj : ReachSetAnalyzer S n) (d : ℝ)
    (R : List (ReachSetAnalyzer.Entry S n)) (w : List ℕ)
    (out : List (String × FiniteSignal ℝ Kleene)) : Prop :=
  ∀ k s, (k, s) ∈ out → ∀ ap, (k, ap) ∈ obj.aps → s.IsValid ∧ s.duration = d ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ d → ∃ v, s.at? t = some v ∧
      (v = Kleene.tt → ∀ j ∈ w, ∀ e, R[j - 1]? = some e → ∀ st ∈ e.timeInterval,
        obj.maskOk k st.time.inf st.time.sup = true →
          FiniteKleeneSignalBuilder.Covers d t st.time.inf st.time.sup →
          ∀ x ∈ construct st.set, ap.Holds x e.loc) ∧
      (v = Kleene.ff → ∀ j ∈ w, ∀ e, R[j - 1]? = some e → ∀ st ∈ e.timeInterval,
        obj.maskOk k st.time.inf st.time.sup = true →
          FiniteKleeneSignalBuilder.Covers d t st.time.inf st.time.sup →
          ∀ x ∈ construct st.set, ¬ ap.Holds x e.loc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
