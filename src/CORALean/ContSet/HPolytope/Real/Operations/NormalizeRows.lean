import CORALean.ContSet.HPolytope.Real.HPolytope
import Mathlib.Analysis.Real.Sqrt

/-!
# `HPolytope.normalizeRows`

CORA's `@polytope/normalizeConstraints` at the types `'A'` and `'Ae'` (`priv_normalizeConstraints`,
both do the same): every row of `A` and of `Ae` whose 2-norm `‖aᵢ‖₂` is nonzero is divided by it,
the right-hand side too, so each such row is a unit vector. A zero row is left alone, CORA's
`withinTol(normA, 0)` being the exact test at tolerance zero.

The 2-norm of a row is that of the functional's coefficients, `√(Σⱼ (a e_j)²)`, so over `Vec ℝ n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every nonzero row, and its right-hand side, divided by the row's 2-norm. -/
noncomputable def HPolytope.normalizeRows (P : HPolytope (Vec ℝ n)) : HPolytope (Vec ℝ n) where
  m := P.m
  A := fun i =>
    if _root_.Real.sqrt (∑ j, (P.A i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2) = 0 then P.A i
    else (_root_.Real.sqrt (∑ j, (P.A i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2))⁻¹ • P.A i
  b := fun i =>
    if _root_.Real.sqrt (∑ j, (P.A i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2) = 0 then P.b i
    else P.b i / _root_.Real.sqrt (∑ j, (P.A i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2)
  me := P.me
  Ae := fun i =>
    if _root_.Real.sqrt (∑ j, (P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2) = 0 then P.Ae i
    else (_root_.Real.sqrt (∑ j, (P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2))⁻¹ • P.Ae i
  be := fun i =>
    if _root_.Real.sqrt (∑ j, (P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2) = 0 then P.be i
    else P.be i / _root_.Real.sqrt (∑ j, (P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
