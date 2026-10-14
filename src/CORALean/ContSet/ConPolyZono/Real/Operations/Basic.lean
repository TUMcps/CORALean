module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Real.Operations.UsedFactors
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `ContSet/ConPolyZono/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {k n : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- ===================================  `ConPolyZono.affine`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The map onto the set, affine in the independent half and polynomial in the
dependent one. -/
def ConPolyZono.affine (cPZ : ConPolyZono α) (ab : (Fin cPZ.p → ℝ) × (Fin cPZ.q → ℝ)) : α :=
  cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E ab.1 i • cPZ.G i + ∑ j, ab.2 j • cPZ.GI j


-- ===================================  `ConPolyZono.centre`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@conPolyZono/center`: the field `c`, with no guarantee that it lies in the set.
`centre_mem_construct` says when it does. -/
def ConPolyZono.centre (cPZ : ConPolyZono α) : α := cPZ.c


-- ==================================  `ConPolyZono.consCol`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Constraint column `l` as a vector, which is the generator the merge adds. -/
def ConPolyZono.consCol {m s : ℕ} (A : Mat ℝ m s) (l : Fin s) : Vec ℝ m := fun i => A i l


-- =================================  `ConPolyZono.factorIdx`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The kept factors, indexed by a plain count, as `PolyZonotope`'s is. -/
def ConPolyZono.factorIdx {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ)
    (k : Fin (ConPolyZono.usedFactors E EC).card) : Fin p :=
  PolyZonotope.factorIdx (ConPolyZono.appendE E EC) k


-- ===============================  `ConPolyZono.mtimes_eq_map`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConPolyZono.mtimes_eq_map (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono.mtimes M cPZ = cPZ.map (Matrix.mulVecLin M) := rfl


-- ===================================  `ConPolyZono.plusB`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The two right-hand sides side by side, each bound concatenated with its
own. -/
def ConPolyZono.plusB {m₁ m₂ : ℕ} (b₁ : Interval (Vec ℝ m₁)) (b₂ : Interval (Vec ℝ m₂)) :
    Interval (Vec ℝ (m₁ + m₂)) :=
  ⟨Fin.append b₁.inf b₂.inf, Fin.append b₁.sup b₂.sup⟩


-- ==================================  `ConPolyZono.unitBox`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The factor box `[-1,1]ᵖ`, which `rescale` contracts. -/
def ConPolyZono.unitBox (p : ℕ) : Interval (Vec ℝ p) where
  inf := fun _ => -1
  sup := fun _ => 1

end CORALean.Real


namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- ===============================  `ConPolyZono.satisfies_map`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The constraint is untouched, and `rfl` is the honest proof of it. -/
theorem ConPolyZono.satisfies_map (f : α →ₗ[ℝ] β) (cPZ : ConPolyZono α)
    (a : Fin cPZ.p → ℝ) : (cPZ.map f).satisfies a ↔ cPZ.satisfies a := Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
