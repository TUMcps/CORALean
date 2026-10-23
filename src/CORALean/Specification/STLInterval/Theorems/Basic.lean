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
theorem STLInterval.dim_eq_one (I : STLInterval ℝ) : I.dim = 1 := rfl


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
theorem STLInterval.representsa_stlInterval {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (tol : ℝ) (I : STLInterval 𝕋) :
    I.representsa_ tol .stlInterval := by
  cases I <;> trivial


-- =================================  `STLInterval.set_empty`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `stlInterval()`, the empty interval, denotes no time. -/
theorem STLInterval.set_empty {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] :
    (STLInterval.empty : STLInterval 𝕋).set = ∅ := rfl


-- ================================  `STLInterval.toEReal_coe`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A stored upper bound reads as the real it denotes. -/
@[simp] theorem STLInterval.toEReal_coe {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (x : 𝕋) :
    STLInterval.toEReal (x : WithTop 𝕋) = ((Float.SoundFloatArithmetic.toReal x : ℝ) : EReal) := rfl


-- ================================  `STLInterval.toEReal_none`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `inf`, written `none`, reads as `⊤`. -/
@[simp] theorem STLInterval.toEReal_none {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] :
    STLInterval.toEReal (none : WithTop 𝕋) = ⊤ := rfl


-- ================================  `STLInterval.toEReal_some`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A stored upper bound, written `some x`, reads as the real it denotes. -/
@[simp] theorem STLInterval.toEReal_some {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (x : 𝕋) : STLInterval.toEReal (some x : WithTop 𝕋) =
      ((Float.SoundFloatArithmetic.toReal x : ℝ) : EReal) := rfl


-- ================================  `STLInterval.toEReal_top`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `inf` reads as `⊤`. -/
@[simp] theorem STLInterval.toEReal_top {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] : STLInterval.toEReal (⊤ : WithTop 𝕋) = ⊤ := rfl


-- ==============================  `STLInterval.toEReal_addUpTop`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Over ℝ the sum of two upper bounds reads as the sum of the extended reals. -/
theorem STLInterval.toEReal_addUpTop (u₁ u₂ : WithTop ℝ) : STLInterval.toEReal
    (STLInterval.addUpTop u₁ u₂) = STLInterval.toEReal u₁ + STLInterval.toEReal u₂ := by
  cases u₁ <;> cases u₂ <;> simp [STLInterval.addUpTop, STLInterval.toEReal_top,
    STLInterval.toEReal_coe, ← EReal.coe_add]


-- =============================  `STLInterval.toEReal_eq_top_iff`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An upper bound reads as `⊤` exactly when it is `inf`. -/
@[simp] theorem STLInterval.toEReal_eq_top_iff {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (u : WithTop 𝕋) :
    STLInterval.toEReal u = ⊤ ↔ u = ⊤ := by
  cases u <;> simp [STLInterval.toEReal_top, STLInterval.toEReal_coe]


-- =============================  `STLInterval.toEReal_map_addUp`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Over ℝ an upper bound moved up by `c` reads as the extended real plus `c`. -/
theorem STLInterval.toEReal_map_addUp (u : WithTop ℝ) (c : ℝ) :
    STLInterval.toEReal (u.map (Float.FloatOps.addUp · c)) = STLInterval.toEReal u + c := by
  cases u <;> simp only [WithTop.map_top, WithTop.map_coe, STLInterval.toEReal_top,
    STLInterval.toEReal_coe, Float.addUp_real, Float.toReal_real, EReal.coe_add, EReal.top_add_coe]


-- =============================  `STLInterval.toEReal_map_subUp`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Over ℝ an upper bound moved down by `c` reads as the extended real minus `c`. -/
theorem STLInterval.toEReal_map_subUp (u : WithTop ℝ) (c : ℝ) :
    STLInterval.toEReal (u.map (Float.subUp · c)) = STLInterval.toEReal u - c := by
  cases u <;> simp only [WithTop.map_top, WithTop.map_coe, STLInterval.toEReal_top,
    STLInterval.toEReal_coe, Float.subUp_real, Float.toReal_real, EReal.coe_sub, EReal.top_sub_coe]


-- ===============================  `STLInterval.toEReal_ne_bot`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An upper bound never reads as `⊥`. -/
theorem STLInterval.toEReal_ne_bot {𝕋 : Type} [Float.FloatOps 𝕋]
    [Float.SoundFloatArithmetic 𝕋] (u : WithTop 𝕋) :
    STLInterval.toEReal u ≠ ⊥ := by
  cases u <;> simp [STLInterval.toEReal_top, STLInterval.toEReal_coe]


-- =============================  `STLInterval.zero_le_lowerBound`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The real `lowerBound` of an interval is `≥ 0`, as CORA's constructor checks. -/
theorem STLInterval.zero_le_lowerBound (I : STLInterval ℝ) : 0 ≤ I.lowerBound := by
  cases I with
  | empty => exact le_rfl
  | nonempty l u lc rc h2 h3 z => simpa [STLInterval.lowerBound] using z

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
