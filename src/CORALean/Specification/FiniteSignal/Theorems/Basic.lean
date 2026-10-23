module

public import CORALean.Specification.FiniteSignal.Operations.Basic
public import CORALean.Specification.FiniteSignal.Operations.CellsFrom
public import CORALean.Specification.FiniteSignal.Operations.ValueAt

@[expose] public section

/-!
# `FiniteSignal/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- =============================  `FiniteSignal.duration_mapTime`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Mapping the time stamps by an `f` that keeps `0` maps the duration. -/
theorem FiniteSignal.duration_mapTime {T T' V : Type} [Zero T] [Zero T'] (f : T → T')
    (hf : f 0 = 0) (s : FiniteSignal T V) : (s.mapTime f).duration = f s.duration := by
  rw [FiniteSignal.duration, FiniteSignal.duration, FiniteSignal.mapTime, ← hf, List.getLastD_map]


-- =============================  `FiniteSignal.length_cellsFrom`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- There is one cell per breakpoint. -/
theorem FiniteSignal.length_cellsFrom {T V : Type} :
    ∀ (a : T) (L : List (T × V)), (FiniteSignal.cellsFrom a L).length = L.length
  | _, [] => rfl
  | a, (b, v) :: rest => by simp [FiniteSignal.cellsFrom, FiniteSignal.length_cellsFrom b rest]


-- ============================  `FiniteSignal.valueAt_cons_of_lt`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Before the first breakpoint, the value is the first breakpoint's. -/
theorem FiniteSignal.valueAt_cons_of_lt {T V : Type} [LinearOrder T] (p : T × V) (q : List (T × V))
    (t : T) (h : t < p.1) : FiniteSignal.valueAt (p :: q) t = some p.2 := by
  cases q <;> simp [FiniteSignal.valueAt, h]


-- =============================  `FiniteSignal.valueAt_singleton`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A single breakpoint holds its value everywhere. -/
theorem FiniteSignal.valueAt_singleton {T V : Type} [LinearOrder T] (p : T × V) (t : T) :
    FiniteSignal.valueAt [p] t = some p.2 := by
  obtain ⟨b, v⟩ := p
  simp [FiniteSignal.valueAt]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
