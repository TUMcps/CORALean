module

public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `SyntaxTree/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
