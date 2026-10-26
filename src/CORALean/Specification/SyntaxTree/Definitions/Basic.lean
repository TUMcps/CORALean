module

public import CORALean.Specification.SyntaxTree.Definitions.SyntaxTreeFloat
public import CORALean.Specification.SyntaxTree.Operations.ValueFloat
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `SyntaxTree/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the sections each one
uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


section


-- ================================  `SyntaxTree.Dom.contains`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `contains(I,t)`: the interval has `t` between its bounds. -/
def SyntaxTree.Dom.contains (I : Dom) (t : ℝ) : Prop := I.inf 0 ≤ t ∧ t ≤ I.sup 0


-- ===================================  `SyntaxTree.IsInBox`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `x` lies in the box `B`. -/
def SyntaxTree.IsInBox {n : ℕ} (B : Real.Interval (Vec ℝ n)) (x : Fin n → ℝ) : Prop :=
  ∀ i, B.inf i ≤ x i ∧ x i ≤ B.sup i


-- ==================================  `SyntaxTree.Encloses`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `t.value` holds `t.eval x` at every point `x` of the box `B`. -/
def SyntaxTree.Encloses {n : ℕ} (B : Real.Interval (Vec ℝ n)) (t : SyntaxTree n) : Prop :=
  ∀ x, SyntaxTree.IsInBox B x → Dom.contains t.value (t.eval x)

end

section
open Float.SoundFloatArithmetic
variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =============================  `Float.SyntaxTree.Dom.contains`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `contains(I,t)` for a float interval: its bounds, read as reals, enclose `t`. -/
def Float.SyntaxTree.Dom.contains (I : Float.SyntaxTree.Dom 𝕋) (t : ℝ) : Prop :=
  toReal (I.inf 0) ≤ t ∧ t ≤ toReal (I.sup 0)


-- =============================  `Float.SyntaxTree.Dom.IsWithin`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `J` lies inside `I`: `I`'s bounds, read as reals, enclose `J`'s. -/
def Float.SyntaxTree.Dom.IsWithin (J I : Float.SyntaxTree.Dom 𝕋) : Prop :=
  toReal (I.inf 0) ≤ toReal (J.inf 0) ∧ toReal (J.sup 0) ≤ toReal (I.sup 0)


-- ================================  `Float.SyntaxTree.IsInBox`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `x` lies in the float box `B`. -/
def Float.SyntaxTree.IsInBox {n : ℕ} (B : Float.Interval (Vec 𝕋 n)) (x : Fin n → ℝ) : Prop :=
  ∀ i, toReal (B.inf i) ≤ x i ∧ x i ≤ toReal (B.sup i)


-- ===============================  `Float.SyntaxTree.Encloses`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `t.value` holds `t.eval x` at every point `x` of the float box `B`. -/
def Float.SyntaxTree.Encloses {n : ℕ} (B : Float.Interval (Vec 𝕋 n)) (t : Float.SyntaxTree 𝕋 n) :
    Prop :=
  ∀ x, Float.SyntaxTree.IsInBox B x → (t.value).contains (t.eval x)

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
