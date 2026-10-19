module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.GetSubset
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

section

open Matrix

variable {k n : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- ===================================  `ConPolyZono.affine`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The map onto the set, affine in the independent half and polynomial in the
dependent one. -/
def ConPolyZono.affine (cPZ : ConPolyZono α) (ab : (Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ)) : α :=
  cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E ab.1 i • cPZ.G i + ∑ j, ab.2 j • cPZ.GI j


-- ===================================  `ConPolyZono.center`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@conPolyZono/center`: the field `c`, with no guarantee that it lies in the set.
`center_mem_construct` says when it does. -/
def ConPolyZono.center (cPZ : ConPolyZono α) : α := cPZ.c


-- ==================================  `ConPolyZono.consCol`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Constraint column `l` as a vector, which is the generator the merge adds. -/
def ConPolyZono.consCol {m q : ℕ} (A : Mat ℝ m q) (l : Fin q) : Vec ℝ m := fun i => A i l


-- =================================  `ConPolyZono.factorIdx`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The kept factors, indexed by a plain count, as `PolyZonotope`'s is. -/
def ConPolyZono.factorIdx {p h q : ℕ} (E : Fin p → Fin h → ℕ) (R : Fin p → Fin q → ℕ)
    (k : Fin (ConPolyZono.usedFactors E R).card) : Fin p :=
  PolyZonotope.factorIdx (ConPolyZono.appendE E R) k


-- ===============================  `ConPolyZono.mtimes_eq_map`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem ConPolyZono.mtimes_eq_map (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    ConPolyZono.mtimes M cPZ = cPZ.map (Matrix.mulVecLin M) := rfl


-- ================================  `ConPolyZono.rescaleStep`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- One factor of `rescale`: factor `r`, if it is a factor of `acc`, re-parametrized onto
`cen r ± rad r` by `getSubset`. -/
def ConPolyZono.rescaleStep (cen rad : ℕ → ℝ) (acc : ConPolyZono α) (r : ℕ) : ConPolyZono α :=
  if h : r < acc.p then acc.getSubset ⟨r, h⟩ (cen r) (rad r) else acc

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
