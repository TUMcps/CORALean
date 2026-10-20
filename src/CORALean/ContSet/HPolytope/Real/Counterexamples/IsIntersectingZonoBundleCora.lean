module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.ZonoBundleVar
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith

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

# CORA's polytope/zonotope-bundle intersection test ignores equality constraints

`aux_isIntersecting_P_zB` (`@polytope/isIntersecting_.m`, l. 371-438) reads only `P.A_.val` and
`P.b_.val`. For the line `P = {x | x₁ = 5}` (an equality row, no inequality row) and the bundle
of two copies of the box `[-1, 1]²`, the sets are disjoint, but the program has no `y`, no `H`
and constrains only `x = cᵢ + Gᵢ aᵢ`, `aᵢ ∈ [-1, 1]`: it is feasible at `x = 0`, `a = 0`, with the
zero objective. Every `CORAlinprog` that reports success with value `0` on a feasible program
with zero objective makes `isIntersecting(P, zB)` (default `'exact'`) answer `true`. The
shortcut of l. 93-98 (one equality row: range of the support function must contain `be`) would
reject it, but is skipped for a `zonoBundle`. Read from the source, not run. A wrong `true`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* for a line and a disjoint bundle, CORA's intersection test answers `true`

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


-- The model: CORA's code as printed, kept only to be refuted.
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

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isIntersectingZonoBundleCora_counterexample : -- --- CONCL ---
    let P : HPolytope (Vec ℝ 2) := HPolytope.eqs !![1, 0] ![5]
    let Zbox : Zonotope (Vec ℝ 2) := ⟨2, 0, ![![1, 0], ![0, 1]]⟩
    let zB : ZonoBundle (Vec ℝ 2) := ⟨2, ![Zbox, Zbox]⟩
    Disjoint P.construct zB.construct ∧
      ∀ linprog : (HPolytope.ZonoBundleVar P.m zB → ℝ) →
          Set (HPolytope.ZonoBundleVar P.m zB) → ℤ × ℝ,
        (∀ f S, S.Nonempty → (∀ z ∈ S, f z = 0) → 0 ≤ (linprog f S).1 ∧ (linprog f S).2 = 0) →
        P.isIntersectingZonoBundleCora zB linprog = true := by -- --- PROOF ---
  intro P Zbox zB
  refine ⟨Set.disjoint_left.mpr fun x hx hx₂ => ?_, fun linprog hlp => ?_⟩
  -- `x₀ = 5` on the line, `x₀ ≤ 1` in the box
  · have h0 := HPolytope.mem_eqs_iff.mp hx 0
    have hz : x ∈ Zbox.construct := SetIntersection.mem_construct_ofFn.mp hx₂ 0
    obtain ⟨β, hβ, hx'⟩ := hz
    have hb := abs_le.mp (hβ (0 : Fin 2))
    have hx0 := congrFun hx' 0
    simp [mulVec, dotProduct, Fin.sum_univ_two, Zbox] at h0 hx0
    linarith [hb.2]
  -- feasible at `x = 0`, `a = 0`, with objective `0` (`P.m = 0`: no `y`)
  · have hne : ∃ z : HPolytope.ZonoBundleVar P.m zB,
        z ∈ ({z | ∀ r : Fin P.m, P.A r z.1 - z.2.1 r ≤ P.b r ∧ -z.2.1 r ≤ 0} ∩
          {z | ∀ i j, z.2.2 i j ≤ 1 ∧ -z.2.2 i j ≤ 1} ∩
          {z | ∀ i, z.1 - ∑ j, z.2.2 i j • (zB.Z i).G j = (zB.Z i).c} :
            Set (HPolytope.ZonoBundleVar P.m zB)) := by
      refine ⟨(0, fun _ => 0, fun _ _ => 0), ⟨⟨fun r => r.elim0, fun i j => ?_⟩, fun i => ?_⟩⟩
      · simp
      · fin_cases i <;> simp [zB, Zbox]
    obtain ⟨z, hz⟩ := hne
    have h := hlp (fun z : HPolytope.ZonoBundleVar P.m zB => ∑ r, z.2.1 r) _ ⟨z, hz⟩
      (fun z _ => Finset.sum_eq_zero fun r _ => r.elim0)
    simp only [HPolytope.isIntersectingZonoBundleCora, h.2, decide_eq_true_eq]
    exact fun hh => hh.elim (fun h' => absurd h' (not_lt.mpr h.1)) fun h' => lt_irrefl _ h'.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
