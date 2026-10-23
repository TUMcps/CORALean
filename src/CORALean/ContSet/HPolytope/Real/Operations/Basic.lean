module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import CORALean.ContSet.HPolytope.Real.Operations.Translate
public import CORALean.Global.LinProg.Duality

@[expose] public section

/-!
# `ContSet/HPolytope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

-- there is no row index to discharge, in either block
variable {α : Type} [AddCommGroup α] [Module ℝ α] {q n : ℕ} {S : Set α}


-- ==================================  `HPolytope.colWeight`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `∑ᵢ |Aᵢ v| + ∑ᵢ |Aeᵢ v|`: how much the rows read along `v`; at a unit vector, the absolute
sum of that coordinate's column, zero exactly when no row reads it. -/
noncomputable def HPolytope.colWeight (P : HPolytope α) (v : α) : ℝ :=
  (∑ i, |P.A i v|) + ∑ i, |P.Ae i v|


-- ===================================  `HPolytope.dropEqs`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `P` without its equality rows: the inequalities kept. -/
def HPolytope.dropEqs (P : HPolytope α) : HPolytope α :=
  { P with me := 0, Ae := Fin.elim0, be := Fin.elim0 }


-- ================================  `HPolytope.dropTrivialEqs`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

open Classical in
/-- `P` without its equality rows `0 = 0`, which every point meets. -/
noncomputable def HPolytope.dropTrivialEqs (P : HPolytope α) : HPolytope α :=
  P.restrict Finset.univ (Finset.univ.filter fun i => ¬(P.Ae i = 0 ∧ P.be i = 0))


-- ====================================  `HPolytope.minus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `polytope/minus.m` accepts a column vector as subtrahend and nothing else
(a set subtrahend is a Minkowski difference, a different method), so `minus P v`
is the translation by `-v`. -/
def HPolytope.minus (P : HPolytope α) (v : α) : HPolytope α :=
  HPolytope.translate (-v) P


-- ====================================  `HPolytope.relax`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Every inequality's bound raised by `s`: `Aᵢ x ≤ bᵢ + sᵢ`, the equalities kept. -/
def HPolytope.relax (P : HPolytope α) (s : Fin P.m → ℝ) : HPolytope α :=
  { P with b := fun i => P.b i + s i }


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
