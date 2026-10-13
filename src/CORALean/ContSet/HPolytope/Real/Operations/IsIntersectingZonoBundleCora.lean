module

public import CORALean.ContSet.HPolytope.Real.Operations.ZonoBundleVar
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `HPolytope.isIntersectingZonoBundleCora`, CORA's polytope/zonotope-bundle intersection test

CORA's `@polytope/isIntersecting_.m`, `aux_isIntersecting_P_zB(P,zB)` (l. 371-438), reached from
l. 122-124 for `type = 'exact'` (the shortcut of l. 93-98 on a single equality row is skipped for a
bundle). Its comment names a polytope `{x | H x <= d}`: the code reads only `H = P.A_.val` and
`d = P.b_.val` (l. 388-389) and never `P.Ae_.val`, `P.be_.val`. The program is over
`(x, y, a₁, …, a_q)`: `H x - y <= d`, `y >= 0`, `x = cᵢ + Gᵢ aᵢ`, `aᵢ ∈ [-1, 1]`, objective
`Σ y`; the verdict is `~(exitflag < 0 || (val > 0 && ~withinTol(val,0)))` (l. 437). One `let` per
printed step. `CORAlinprog` is a caller's argument, given the objective and the feasible set and
answering `(exitflag, val)`. `withinTol(val,0)` is its absolute branch `|val| <= 1e-8` (the
relative branch divides by `min(|val|, 0) = 0`).

## References

* [1] `contSet/@polytope/isIntersecting_.m`, CORA, ll. 93-124, 371-438.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- [1]'s `aux_isIntersecting_P_zB`, with `linprog f S` the pair `(exitflag, val)` that
`CORAlinprog` returns for the objective `f` over the feasible set `S`. -/
noncomputable def HPolytope.isIntersectingZonoBundleCora (P : HPolytope (Vec ℝ n))
    (zB : ZonoBundle (Vec ℝ n))
    (linprog : (HPolytope.ZonoBundleVar P.m zB → ℝ) → Set (HPolytope.ZonoBundleVar P.m zB) →
      ℤ × ℝ) : Bool :=
  -- l. 388-395: `H, d = P.A_.val, P.b_.val` (no equality rows), `Aineq = [H,-I; 0,-I]`
  let rowsH : Set (HPolytope.ZonoBundleVar P.m zB) :=
    {z | ∀ r, P.A r z.1 - z.2.1 r ≤ P.b r ∧ -z.2.1 r ≤ 0}
  -- l. 413-414: per zonotope, `Aineq = blkdiag(Aineq, [eye(m); -eye(m)])`, `bineq = [..; 1]`
  let boxes : Set (HPolytope.ZonoBundleVar P.m zB) :=
    {z | ∀ i j, z.2.2 i j ≤ 1 ∧ -z.2.2 i j ≤ 1}
  -- l. 409-410, 417-418: `Aeq = [eyeRep, 0, blkdiag(-G)]`, `beq = [c₁; …; c_q]`: `x - Gᵢ aᵢ = cᵢ`
  let couple : Set (HPolytope.ZonoBundleVar P.m zB) :=
    {z | ∀ i, z.1 - ∑ j, z.2.2 i j • (zB.Z i).G j = (zB.Z i).c}
  -- l. 421-422: `f = zeros; f(n+1:n+p) = ones(p,1)`, i.e. the objective `Σ y`
  let f : HPolytope.ZonoBundleVar P.m zB → ℝ := fun z => ∑ r, z.2.1 r
  -- l. 434: `[~,val,exitflag] = CORAlinprog(problem)`
  let sol := linprog f (rowsH ∩ boxes ∩ couple)
  let exitflag := sol.1
  let val := sol.2
  -- l. 437: `res = ~(exitflag < 0 || (val > 0 && ~withinTol(val,0)))`
  (decide (¬ (exitflag < 0 ∨ (0 < val ∧ ¬ |val| ≤ 1e-8))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
