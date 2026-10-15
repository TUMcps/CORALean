module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.STLInterval
public import CORALean.Specification.STLInterval.Theorems.RawSetNonemptyOf

@[expose] public section

/-!
# `Specification/STLInterval/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- =================================  `STLInterval.dim_eq_one`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `dim` of an STL interval is `1`: its times are a subset of `ℝ`. -/
theorem STLInterval.dim_eq_one (I : STLInterval) : I.dim = 1 := rfl


-- =============================  `STLInterval.rawSet_closed_coe`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `rawSet ↑a ↑b true true` is `Set.Icc a b`. -/
theorem STLInterval.rawSet_closed_coe (a b : ℝ) :
    rawSet (a : EReal) (b : EReal) true true = Set.Icc a b := by
  ext t
  simp [rawSet, le_iff_lt_or_eq, eq_comm]


-- ===========================  `STLInterval.rawSet_closed_nonempty`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `rawSet ↑a ↑b true true` is nonempty for `a ≤ b`. -/
theorem STLInterval.rawSet_closed_nonempty {a b : ℝ} (h : a ≤ b) :
    (rawSet (a : EReal) b true true).Nonempty := by
  rw [rawSet_closed_coe]; exact Set.nonempty_Icc.2 h


-- ==========================  `STLInterval.representsa_stlInterval`  =========================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every STL interval represents an `stlInterval`. -/
theorem STLInterval.representsa_stlInterval (tol : ℝ) (I : STLInterval) :
    I.representsa_ tol .stlInterval := by
  cases I <;> trivial


-- =================================  `STLInterval.set_empty`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `stlInterval()`, the empty interval, denotes no time. -/
theorem STLInterval.set_empty : STLInterval.empty.set = ∅ := rfl


-- =============================  `STLInterval.zero_le_lowerBound`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The real `lowerBound` of an interval is `≥ 0`, as CORA's constructor checks. -/
theorem STLInterval.zero_le_lowerBound (I : STLInterval) : 0 ≤ I.lowerBound := by
  cases I with
  | empty => exact le_rfl
  | nonempty l u lc rc h1 h2 h3 z => exact EReal.toReal_nonneg z

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
