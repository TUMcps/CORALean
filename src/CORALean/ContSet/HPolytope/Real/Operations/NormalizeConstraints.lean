import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.normalizeConstraints`

CORA's `@polytope/normalizeConstraints` at its default type `'b'` (`priv_normalizeConstraints`):
every inequality row `aᵀx ≤ b` with `b ≠ 0` is divided by `|b|`, so that its right-hand side is
`±1`, and every equality row with `be ≠ 0` is divided by `be`, so that its right-hand side is
`1`. Rows with a zero right-hand side are left alone. Every row is rescaled by a positive number
(a nonzero one, for an equality), so the set is the same (`normalizeConstraints_exact`).

The other types, `'A'` and `'Ae'`, divide a row by its 2-norm: that is `normalizeRows`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every row with a nonzero right-hand side divided by it, up to sign. -/
noncomputable def HPolytope.normalizeConstraints (P : HPolytope α) : HPolytope α where
  m := P.m
  A := fun i => if P.b i = 0 then P.A i else |P.b i|⁻¹ • P.A i
  b := fun i => if P.b i = 0 then 0 else if 0 < P.b i then 1 else -1
  me := P.me
  Ae := fun i => if P.be i = 0 then P.Ae i else (P.be i)⁻¹ • P.Ae i
  be := fun i => if P.be i = 0 then 0 else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
