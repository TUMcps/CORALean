module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Operations.Basic
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Entry
public import CORALean.Specification.ReachSetAnalyzer.ReachSetAnalyzer

@[expose] public section

/-!
# `ReachSetAnalyzer/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {T : Type} {S : ℕ → Type} {n : ℕ}


-- ===============================  `ReachSetAnalyzer.children`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `out = children(R,parent)` of `reachSet`: the indices `1,2,…` of the entries with that
parent. -/
def ReachSetAnalyzer.children (R : List (ReachSetAnalyzer.Entry T S n)) (parent : ℕ) : List ℕ :=
  (List.range R.length).filterMap fun i =>
    if R[i]?.map (·.parent) = some parent then some (i + 1) else none


-- ================================  `ReachSetAnalyzer.mapTime`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The analyzer with the time stamps of its builders and masks mapped by `f`. -/
def ReachSetAnalyzer.mapTime {T' : Type} (f : T → T') (obj : ReachSetAnalyzer T S n) :
    ReachSetAnalyzer T' S n :=
  ⟨obj.aps, obj.sigBuilder.map fun p => (p.1, p.2.mapTime f),
    obj.masks.map fun p => (p.1, p.2.mapTime f)⟩


-- ===========================  `ReachSetAnalyzer.TimedSet.mapTime`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The timed set with the bounds of its time interval mapped by `f`. -/
def ReachSetAnalyzer.TimedSet.mapTime {T' : Type} (f : T → T')
    (st : ReachSetAnalyzer.TimedSet T S n) : ReachSetAnalyzer.TimedSet T' S n :=
  ⟨st.set, ⟨f st.time.inf, f st.time.sup⟩⟩


-- =============================  `ReachSetAnalyzer.Entry.mapTime`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The entry with the time interval of each of its sets mapped by `f`. -/
def ReachSetAnalyzer.Entry.mapTime {T' : Type} (f : T → T') (e : ReachSetAnalyzer.Entry T S n) :
    ReachSetAnalyzer.Entry T' S n :=
  ⟨e.parent, e.loc, e.timeInterval.map (ReachSetAnalyzer.TimedSet.mapTime f)⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
