module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.representsaHyperplaneCora`: the `'hyperplane'` test as CORA's code computes it

`@polytope/representsa_.m` opens with

```
[emptyObj,res] = representsa_emptyObject(P,type);
if emptyObj; return; end
```

and `@polytope/isemptyobject.m` (l. 36) calls an H-representation without inequality and without
equality rows an "empty object" (it represents `ℝⁿ`). `@contSet/representsa_emptyObject.m` then
treats every such object as the empty set: for `type = 'hyperplane'` it sets `res = true`
(l. 68). Otherwise the branch `'hyperplane'` of `representsa_.m` (l. 259) reads
`res = isempty(P.A_.val) && size(P.Ae_.val,1) == 1`. Read from the source, not run.

# CORA's `polytope/representsa_(P, 'hyperplane')` accepts `ℝⁿ`

The unconstrained H-polytope (`polytope.Inf(n)`, no inequality and no equality rows) denotes
`ℝⁿ`. `isemptyobject` counts it as an empty object, and `representsa_emptyObject` answers
`'hyperplane'` with `true` for every empty object (written for the empty set of a vertex
representation), so `representsa(polytope.Inf(2),'hyperplane')` is `true`, though `ℝ²` is no
hyperplane. A wrong answer, not unsound. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the set is `ℝ²`, which is no hyperplane `{x | f x = c}` with `f ≠ 0`; CORA answers `true`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `res` for `representsa_(P, 'hyperplane')`, H-representation. -/
def HPolytope.representsaHyperplaneCora (P : HPolytope (Fin n → ℝ)) : Bool :=
  -- emptyObj = isemptyobject(P): no inequality and no equality rows
  let emptyObj := P.m == 0 && P.me == 0
  -- representsa_emptyObject, type 'hyperplane': res = true
  if emptyObj then true
  -- res = isempty(P.A_.val) && size(P.Ae_.val,1) == 1
  else P.m == 0 && P.me == 1

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `polytope.Inf(2)`: no rows. -/
def HPolytope.aux_noRows : HPolytope (Fin 2 → ℝ) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

private theorem HPolytope.aux_noRows_construct :
    HPolytope.aux_noRows.construct = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact ⟨fun i => i.elim0, fun i => i.elim0⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is `ℝ²`, which is no hyperplane `{x | f x = c}` with `f ≠ 0`; CORA answers `true`. -/
theorem HPolytope.representsa_hyperplane_cora_counterexample : -- --- CONCL ---
    HPolytope.aux_noRows.construct = Set.univ ∧
      (¬ ∃ (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
        HPolytope.aux_noRows.construct = {x | f x = c}) ∧
      HPolytope.aux_noRows.representsaHyperplaneCora = true := by -- --- PROOF ---
  have hc := HPolytope.aux_noRows_construct
  refine ⟨hc, ?_, by simp [HPolytope.representsaHyperplaneCora, HPolytope.aux_noRows]⟩
  rintro ⟨f, c, hf, h⟩
  rw [hc] at h
  have hall : ∀ x, f x = c := fun x => by
    have : x ∈ ({x | f x = c} : Set (Fin 2 → ℝ)) := by rw [← h]; trivial
    exact this
  apply hf
  have h0 : c = 0 := by rw [← hall 0, map_zero]
  refine LinearMap.ext fun x => ?_
  rw [hall x, h0]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
