module

public import CORALean.Specification.FiniteSignal.Operations.CellsFrom
public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Algebra.Group.Defs

@[expose] public section

/-!
# `FiniteSignal/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ===================================  `FiniteSignal.cells`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The cells of a signal, from `0`. -/
def FiniteSignal.cells {T V : Type} [Zero T] (s : FiniteSignal T V) : List ((T × T) × V) :=
  FiniteSignal.cellsFrom 0 (s.time.zip s.value)


-- =================================  `FiniteSignal.duration`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `duration(sig)`: the last time. -/
def FiniteSignal.duration {T V : Type} [Zero T] (s : FiniteSignal T V) : T := s.time.getLastD 0


-- ==================================  `FiniteSignal.length`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `length(sig)`: the number of breakpoints. -/
def FiniteSignal.length {T V : Type} (s : FiniteSignal T V) : ℕ := s.time.length


-- ==================================  `FiniteSignal.mapTime`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The signal with every time stamp mapped by `f`, as a float signal is read by `toReal`. -/
def FiniteSignal.mapTime {T T' V : Type} (f : T → T') (s : FiniteSignal T V) : FiniteSignal T' V :=
  ⟨s.time.map f, s.value⟩


-- ===================================  `FiniteSignal.pairs`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The breakpoints `(time(i),value(i))`. -/
def FiniteSignal.pairs {T V : Type} (s : FiniteSignal T V) : List (T × V) := s.time.zip s.value


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
