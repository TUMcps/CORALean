module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.IntervalFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsTimes
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesOfSound
public import CORALean.Specification.SyntaxTree.Theorems.EnclosesPower
public import CORALean.Specification.SyntaxTree.Theorems.MinusSound
public import CORALean.Specification.SyntaxTree.Theorems.PlusSound
public import CORALean.Specification.SyntaxTree.Theorems.PowerSound
public import CORALean.Specification.SyntaxTree.Theorems.TimesSound
public import CORALean.Specification.SyntaxTree.Theorems.UminusSound

@[expose] public section

/-!
# `SyntaxTree/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean
open Float.SoundFloatArithmetic
variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}
variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- ==============================  `SyntaxTree.contains_interval`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `interval(c,c)` holds `c`. -/
theorem SyntaxTree.contains_interval {c : ℝ} : Dom.contains (interval c c) c := ⟨le_rfl, le_rfl⟩


-- ===========================  `SyntaxTree.contains_intervalFloat`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `interval(c,c)` holds `c` read as a real. -/
theorem SyntaxTree.contains_intervalFloat {c : 𝕋} :
    (SyntaxTree.intervalFloat c c).contains (toReal c) := ⟨le_rfl, le_rfl⟩


-- ===============================  `SyntaxTree.contains_minus`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `I - J` holds `a - b`. -/
theorem SyntaxTree.contains_minus {I J : Dom} {a b : ℝ} (ha : Dom.contains I a)
    (hb : Dom.contains J b) : Dom.contains (Real.Interval.minus I J) (a - b) :=
  ⟨sub_le_sub ha.1 hb.2, sub_le_sub ha.2 hb.1⟩


-- =============================  `SyntaxTree.contains_minusFloat`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `I - J` holds `a - b`. -/
theorem SyntaxTree.contains_minusFloat {I J : Float.SyntaxTree.Dom 𝕋} {a b : ℝ} (ha : I.contains a)
    (hb : J.contains b) : Float.SyntaxTree.Dom.contains (Float.Interval.minus I J) (a - b) :=
  ⟨(Float.subDown_le_sub _ _).trans (sub_le_sub ha.1 hb.2),
    (sub_le_sub ha.2 hb.1).trans (Float.sub_le_subUp _ _)⟩


-- ===========================  `SyntaxTree.contains_of_outerFloat`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- If the image of `I` under `f` lies in `J`, then `J` holds `f t` where `I` holds `t`. -/
theorem SyntaxTree.contains_of_outerFloat {I J : Float.SyntaxTree.Dom 𝕋} {f : ℝ → ℝ}
    (h : (fun x i => f (x i)) '' I.construct ⊆ J.construct) {t : ℝ} (ht : I.contains t) :
    J.contains (f t) :=
  h ⟨fun _ => t, fun i => by obtain rfl : i = 0 := Subsingleton.elim i 0; exact ht, rfl⟩ 0


-- ================================  `SyntaxTree.contains_plus`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `I + J` holds `a + b`. -/
theorem SyntaxTree.contains_plus {I J : Dom} {a b : ℝ} (ha : Dom.contains I a)
    (hb : Dom.contains J b) : Dom.contains (Real.Interval.plus I J) (a + b) :=
  ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩


-- =============================  `SyntaxTree.contains_plusFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `I + J` holds `a + b`. -/
theorem SyntaxTree.contains_plusFloat {I J : Float.SyntaxTree.Dom 𝕋} {a b : ℝ} (ha : I.contains a)
    (hb : J.contains b) : Float.SyntaxTree.Dom.contains (Float.Interval.plus I J) (a + b) :=
  ⟨(addDown_le_add _ _).trans (add_le_add ha.1 hb.1),
    (add_le_add ha.2 hb.2).trans (add_le_addUp _ _)⟩


-- =============================  `SyntaxTree.contains_timesFloat`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `I * J` holds `a * b`. -/
theorem SyntaxTree.contains_timesFloat {I J : Float.SyntaxTree.Dom 𝕋} {a b : ℝ}
    (ha : I.contains a) (hb : J.contains b) :
    Float.SyntaxTree.Dom.contains (Float.Interval.times I J) (a * b) :=
  Float.Interval.mul_between_corners ha.1 ha.2 hb.1 hb.2


-- ============================  `SyntaxTree.contains_uminusFloat`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `-I` holds `-a`. -/
theorem SyntaxTree.contains_uminusFloat {I : Float.SyntaxTree.Dom 𝕋} {a : ℝ} (ha : I.contains a) :
    Float.SyntaxTree.Dom.contains (Float.Interval.uminus I) (-a) :=
  ⟨by show toReal (-(I.sup 0)) ≤ -a; rw [Float.toReal_neg']; exact neg_le_neg ha.2,
    by show -a ≤ toReal (-(I.inf 0)); rw [Float.toReal_neg']; exact neg_le_neg ha.1⟩


-- ==================================  `SyntaxTree.eval_acos`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `acos(obj)` denotes acos of the operand. -/
theorem SyntaxTree.eval_acos (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.acos).eval x = Real.arccos (t.eval x) := rfl


-- =================================  `SyntaxTree.eval_acosh`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- `acosh(obj)` denotes acosh of the operand. -/
theorem SyntaxTree.eval_acosh (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.acosh).eval x = Real.arcosh (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_asin`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asin(obj)` denotes asin of the operand. -/
theorem SyntaxTree.eval_asin (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.asin).eval x = Real.arcsin (t.eval x) := rfl


-- =================================  `SyntaxTree.eval_asinh`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `asinh(obj)` denotes asinh of the operand. -/
theorem SyntaxTree.eval_asinh (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.asinh).eval x = Real.arsinh (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_atan`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atan(obj)` denotes atan of the operand. -/
theorem SyntaxTree.eval_atan (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.atan).eval x = Real.arctan (t.eval x) := rfl


-- =================================  `SyntaxTree.eval_atanh`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `atanh(obj)` denotes atanh of the operand. -/
theorem SyntaxTree.eval_atanh (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.atanh).eval x = Real.artanh (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_cos`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)

/-- `cos(obj)` denotes cos of the operand. -/
theorem SyntaxTree.eval_cos (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.cos).eval x = Real.cos (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_cosh`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `cosh(obj)` denotes cosh of the operand. -/
theorem SyntaxTree.eval_cosh (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.cosh).eval x = Real.cosh (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_exp`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `exp(obj)` denotes exp of the operand. -/
theorem SyntaxTree.eval_exp (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.exp).eval x = Real.exp (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_log`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `log(obj)` denotes log of the operand. -/
theorem SyntaxTree.eval_log (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.log).eval x = Real.log (t.eval x) := rfl


-- =================================  `SyntaxTree.eval_minus`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,obj2)` denotes the minus of the operands. -/
theorem SyntaxTree.eval_minus (t₁ t₂ : SyntaxTree n) (x : Fin n → ℝ) :
    (t₁.minus t₂).eval x = t₁.eval x - t₂.eval x := rfl


-- ==============================  `SyntaxTree.eval_minusNumLeft`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(c,obj2)` denotes `c -` the operand. -/
theorem SyntaxTree.eval_minusNumLeft (c : ℝ) (t : SyntaxTree n) (x : Fin n → ℝ) :
    (SyntaxTree.minusNumLeft c t).eval x = c - t.eval x := rfl


-- =============================  `SyntaxTree.eval_minusNumRight`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `minus(obj1,c)` denotes the operand `- c`. -/
theorem SyntaxTree.eval_minusNumRight (t : SyntaxTree n) (c : ℝ) (x : Fin n → ℝ) :
    (SyntaxTree.minusNumRight t c).eval x = t.eval x - c := rfl


-- =================================  `SyntaxTree.eval_mpower`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `mpower(obj)` denotes mpower of the operand. -/
theorem SyntaxTree.eval_mpower (t : SyntaxTree n) (k : ℕ) (x : Fin n → ℝ) :
    (t.mpower k).eval x = t.eval x ^ k := rfl


-- ==================================  `SyntaxTree.eval_plus`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,obj2)` denotes the plus of the operands. -/
theorem SyntaxTree.eval_plus (t₁ t₂ : SyntaxTree n) (x : Fin n → ℝ) :
    (t₁.plus t₂).eval x = t₁.eval x + t₂.eval x := rfl


-- ==============================  `SyntaxTree.eval_plusNumLeft`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(c,obj2)` denotes `c +` the operand. -/
theorem SyntaxTree.eval_plusNumLeft (c : ℝ) (t : SyntaxTree n) (x : Fin n → ℝ) :
    (SyntaxTree.plusNumLeft c t).eval x = c + t.eval x := rfl


-- ==============================  `SyntaxTree.eval_plusNumRight`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `plus(obj1,c)` denotes the operand `+ c`. -/
theorem SyntaxTree.eval_plusNumRight (t : SyntaxTree n) (c : ℝ) (x : Fin n → ℝ) :
    (SyntaxTree.plusNumRight t c).eval x = t.eval x + c := rfl


-- =================================  `SyntaxTree.eval_power`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `power(obj)` denotes power of the operand. -/
theorem SyntaxTree.eval_power (t : SyntaxTree n) (k : ℕ) (x : Fin n → ℝ) :
    (t.power k).eval x = t.eval x ^ k := rfl


-- ==================================  `SyntaxTree.eval_sin`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sin(obj)` denotes sin of the operand. -/
theorem SyntaxTree.eval_sin (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.sin).eval x = Real.sin (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_sinh`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sinh(obj)` denotes sinh of the operand. -/
theorem SyntaxTree.eval_sinh (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.sinh).eval x = Real.sinh (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_sqrt`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `sqrt(obj)` denotes sqrt of the operand. -/
theorem SyntaxTree.eval_sqrt (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.sqrt).eval x = Real.sqrt (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_tan`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tan(obj)` denotes tan of the operand. -/
theorem SyntaxTree.eval_tan (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.tan).eval x = Real.tan (t.eval x) := rfl


-- ==================================  `SyntaxTree.eval_tanh`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `tanh(obj)` denotes tanh of the operand. -/
theorem SyntaxTree.eval_tanh (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.tanh).eval x = Real.tanh (t.eval x) := rfl


-- =================================  `SyntaxTree.eval_times`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,obj2)` denotes the times of the operands. -/
theorem SyntaxTree.eval_times (t₁ t₂ : SyntaxTree n) (x : Fin n → ℝ) :
    (t₁.times t₂).eval x = t₁.eval x * t₂.eval x := rfl


-- ==============================  `SyntaxTree.eval_timesNumLeft`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(c,obj2)` denotes `c *` the operand. -/
theorem SyntaxTree.eval_timesNumLeft (c : ℝ) (t : SyntaxTree n) (x : Fin n → ℝ) :
    (SyntaxTree.timesNumLeft c t).eval x = c * t.eval x := rfl


-- =============================  `SyntaxTree.eval_timesNumRight`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `times(obj1,c)` denotes the operand `* c`. -/
theorem SyntaxTree.eval_timesNumRight (t : SyntaxTree n) (c : ℝ) (x : Fin n → ℝ) :
    (SyntaxTree.timesNumRight t c).eval x = t.eval x * c := rfl


-- =================================  `SyntaxTree.eval_uminus`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uminus(obj)` denotes uminus of the operand. -/
theorem SyntaxTree.eval_uminus (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.uminus).eval x = -(t.eval x) := rfl


-- =================================  `SyntaxTree.eval_uplus`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus(obj)` denotes uplus of the operand. -/
theorem SyntaxTree.eval_uplus (t : SyntaxTree n) (x : Fin n → ℝ) :
    (t.uplus).eval x = t.eval x := rfl


-- ==================================  `SyntaxTree.eval_var`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A variable leaf denotes its coordinate. -/
theorem SyntaxTree.eval_var (i : Fin n) (v : SyntaxTree.Dom) (x : Fin n → ℝ) :
    (SyntaxTree.var i v).eval x = x i := rfl


-- ============================  `SyntaxTree.isInBox_intersection`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of both boxes is a point of their intersection. -/
theorem SyntaxTree.isInBox_intersection {B₁ B₂ : Real.Interval (Vec ℝ n)} {x : Fin n → ℝ}
    (h₁ : IsInBox B₁ x) (h₂ : IsInBox B₂ x) : IsInBox (Real.Interval.intersection B₁ B₂) x :=
  fun i => ⟨max_le (h₁ i).1 (h₂ i).1, le_min (h₁ i).2 (h₂ i).2⟩


-- ================================  `SyntaxTree.isSound_minus`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `minus` node over two sound trees is sound. -/
theorem SyntaxTree.isSound_minus {t₁ t₂ : SyntaxTree n} (h₁ : IsSound B t₁) (h₂ : IsSound B t₂) :
    IsSound B (t₁.minus t₂) :=
  ⟨h₁, h₂, fun x hx => SyntaxTree.contains_minus (encloses_of_isSound h₁ x hx)
    (encloses_of_isSound h₂ x hx), minus_sound _ _⟩


-- ============================  `SyntaxTree.isSound_minusNumLeft`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `minus` node with a number first is sound. -/
theorem SyntaxTree.isSound_minusNumLeft (c : ℝ) (h : IsSound B t) :
    IsSound B (SyntaxTree.minusNumLeft c t) :=
  ⟨h, fun x hx => SyntaxTree.contains_minus SyntaxTree.contains_interval (encloses_of_isSound h x
      hx), minus_sound _ _⟩


-- ============================  `SyntaxTree.isSound_minusNumRight`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `minus` node with a number second is sound. -/
theorem SyntaxTree.isSound_minusNumRight (h : IsSound B t) (c : ℝ) :
    IsSound B (SyntaxTree.minusNumRight t c) :=
  ⟨h, fun x hx => SyntaxTree.contains_minus (encloses_of_isSound h x hx)
      SyntaxTree.contains_interval, minus_sound _ _⟩


-- ================================  `SyntaxTree.isSound_plus`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `plus` node over two sound trees is sound. -/
theorem SyntaxTree.isSound_plus {t₁ t₂ : SyntaxTree n} (h₁ : IsSound B t₁) (h₂ : IsSound B t₂) :
    IsSound B (t₁.plus t₂) :=
  ⟨h₁, h₂, fun x hx => SyntaxTree.contains_plus (encloses_of_isSound h₁ x hx)
    (encloses_of_isSound h₂ x hx), plus_sound _ _⟩


-- =============================  `SyntaxTree.isSound_plusNumLeft`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `plus` node with a number first is sound. -/
theorem SyntaxTree.isSound_plusNumLeft (c : ℝ) (h : IsSound B t) :
    IsSound B (SyntaxTree.plusNumLeft c t) :=
  ⟨h, fun x hx => SyntaxTree.contains_plus SyntaxTree.contains_interval
      (encloses_of_isSound h x hx), plus_sound _ _⟩


-- ============================  `SyntaxTree.isSound_plusNumRight`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `plus` node with a number second is sound. -/
theorem SyntaxTree.isSound_plusNumRight (h : IsSound B t) (c : ℝ) :
    IsSound B (SyntaxTree.plusNumRight t c) :=
  ⟨h, fun x hx => SyntaxTree.contains_plus (encloses_of_isSound h x hx)
      SyntaxTree.contains_interval, plus_sound _ _⟩


-- ================================  `SyntaxTree.isSound_power`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `power` node over a sound tree is sound. -/
theorem SyntaxTree.isSound_power (h : IsSound B t) (k : ℕ) : IsSound B (t.power k) :=
  ⟨h, encloses_power (encloses_of_isSound h) k, power_sound k t.value⟩


-- ===============================  `SyntaxTree.isSound_mpower`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `mpower` node over a sound tree is sound. -/
theorem SyntaxTree.isSound_mpower (h : IsSound B t) (k : ℕ) : IsSound B (t.mpower k) :=
  SyntaxTree.isSound_power h k


-- ================================  `SyntaxTree.isSound_times`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `times` node over two sound trees is sound. -/
theorem SyntaxTree.isSound_times {t₁ t₂ : SyntaxTree n} (h₁ : IsSound B t₁) (h₂ : IsSound B t₂) :
    IsSound B (t₁.times t₂) :=
  ⟨h₁, h₂, fun x hx => SyntaxTree.contains_times (encloses_of_isSound h₁ x hx)
    (encloses_of_isSound h₂ x hx), times_sound _ _⟩


-- ============================  `SyntaxTree.isSound_timesNumLeft`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `times` node with a number first is sound. -/
theorem SyntaxTree.isSound_timesNumLeft (c : ℝ) (h : IsSound B t) :
    IsSound B (SyntaxTree.timesNumLeft c t) :=
  ⟨h, fun x hx => SyntaxTree.contains_times SyntaxTree.contains_interval (encloses_of_isSound h x
      hx), times_sound _ _⟩


-- ============================  `SyntaxTree.isSound_timesNumRight`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `times` node with a number second is sound. -/
theorem SyntaxTree.isSound_timesNumRight (h : IsSound B t) (c : ℝ) :
    IsSound B (SyntaxTree.timesNumRight t c) :=
  ⟨h, fun x hx => SyntaxTree.contains_times (encloses_of_isSound h x hx)
      SyntaxTree.contains_interval, times_sound _ _⟩


-- ===============================  `SyntaxTree.isSound_uminus`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `uminus` node over a sound tree is sound. -/
theorem SyntaxTree.isSound_uminus (h : IsSound B t) : IsSound B t.uminus :=
  ⟨h, fun x hx => (by
    have hc := encloses_of_isSound h x hx
    exact ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩), uminus_sound t.value⟩


-- ================================  `SyntaxTree.isSound_uplus`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus` of a sound tree is sound. -/
theorem SyntaxTree.isSound_uplus (h : IsSound B t) : IsSound B t.uplus := h


-- =============================  `SyntaxTree.isSound_uplusFloat`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The `uplus` node over a sound float tree is the tree itself. -/
theorem SyntaxTree.isSound_uplusFloat {n : ℕ} {B : Float.Interval (Vec 𝕋 n)}
    {t : Float.SyntaxTree 𝕋 n} (h : SyntaxTree.IsSoundFloat B t) :
    SyntaxTree.IsSoundFloat B (SyntaxTree.uplusFloat t) := h


-- =================================  `SyntaxTree.isSound_var`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The leaf of a variable holding its coordinate of the box is sound. -/
theorem SyntaxTree.isSound_var {B : Real.Interval (Vec ℝ n)} (i : Fin n) :
    IsSound B (.var i (interval (B.inf i) (B.sup i))) := fun _ hx => hx i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
