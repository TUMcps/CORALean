module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `HPolytope.representsaPointCora`: the `'point'` test as CORA's code computes it

`@polytope/representsa_.m`, branch `'point'` (l. 68-70), for `n ≥ 2`:

```
[fulldim,subspace] = isFullDim(P);
res = ~fulldim && isempty(subspace);
```

`isFullDim` with two outputs, for an H-representation in `n ≥ 2` (`aux_isFullDim_nD_H_subspace`,
`@polytope/isFullDim.m`), starts with `if representsa_(P,'emptySet',tol)`, answering
`res = false; subspace = []`. A point has `fulldim = false` and `subspace = []` (the comment
"if P is just a point, subspace=[]"), so the empty polytope passes as a point. The rest of the
algorithm (a nonempty `P`) is not modelled and is taken as the given pair `rest`. Emptiness is
the set-level test. Read from the source, not run.

# CORA's `polytope/representsa_(P, 'point')` accepts an empty polytope

`P = {x ≤ 0, -x ≤ -1}` in `ℝ²` (an H-representation, nonempty arrays, so
`representsa_emptyObject` does not catch it) is empty. For `'point'` and `n ≥ 2`, CORA reads
`[fulldim,subspace] = isFullDim(P)`, which for an empty polytope returns `false` and `[]`, and
sets `res = ~fulldim && isempty(subspace) = true`. A wrong answer, not unsound.

## Inputs
* `rest` – flag and subspace returned by the rest of `isFullDim`

## Hypotheses
* none

## Conclusion
* the polytope is empty, yet CORA answers `'point'` with `true`
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
/-- CORA's `res` for `representsa_(P, 'point')`, `n ≥ 2`, H-representation; `rest` is the
`isFullDim` pair of a nonempty `P`. -/
noncomputable def HPolytope.representsaPointCora (P : HPolytope (Fin n → ℝ))
    (rest : Bool × List (Fin n → ℝ)) : Bool :=
  -- [fulldim,subspace] = isFullDim(P)
  let r : Bool × List (Fin n → ℝ) := if P.construct = ∅ then (false, []) else rest
  !r.1 && r.2.isEmpty                  -- res = ~fulldim && isempty(subspace)

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The contradictory strip `{x ≤ 0, x ≥ 1}` in `ℝ²`. -/
def HPolytope.aux_emptyStrip : HPolytope (Fin 2 → ℝ) where
  m := 2
  A := let p0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
    ![p0, -p0]
  b := ![0, -1]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

private theorem HPolytope.aux_emptyStrip_construct : -- --- CONCL ---
    HPolytope.aux_emptyStrip.construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h, -⟩
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simp [HPolytope.aux_emptyStrip] at h0 h1
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The polytope is empty, so no single point; CORA answers `'point'` with `true`, whatever the
rest of `isFullDim` would compute. -/
theorem HPolytope.representsa_point_cora_counterexample
    (rest : Bool × List (Fin 2 → ℝ)) : -- --- CONCL ---
    HPolytope.aux_emptyStrip.construct = ∅ ∧
      (¬ ∃ p : Fin 2 → ℝ, HPolytope.aux_emptyStrip.construct = {p}) ∧
      HPolytope.aux_emptyStrip.representsaPointCora rest = true := by -- --- PROOF ---
  have hc := HPolytope.aux_emptyStrip_construct
  refine ⟨hc, ?_, ?_⟩
  · rintro ⟨p, hp⟩
    have : p ∈ HPolytope.aux_emptyStrip.construct := by rw [hp]; rfl
    rw [hc] at this
    exact this
  · simp [HPolytope.representsaPointCora, hc]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
