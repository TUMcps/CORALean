module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Pointwise

@[expose] public section

/-!
# Eroding keeps the inequality rows bounded

The rows of `P.minkDiffOf T u` are `P`'s, each moved inward past `T`'s bound, so any `z ∈ T` carries
their region into `P`'s: `x + z` meets every row of `P`. Stated for the inequality rows alone, the
region `dropEqs` describes: the whole set would not do, an empty `P` (its inequalities and
equalities disjoint) having an unbounded erosion when the shift reaches the equalities' plane.
`T` must be nonempty; for `T = ∅` the bounds `u` are arbitrary.

## Inputs
* `P` – H-polytope
* `T` – set of points
* `u` – a support bound of `T` along each row

## Hypotheses
* `hP` – the inequality rows of `P` bound it
* `hT` – `T` is nonempty

## Conclusion
* the inequality rows of the difference bound it as well
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isBounded_dropEqs_minkDiffOf {P : HPolytope (Vec ℝ n)} {T : Set (Vec ℝ n)}
    (u : ∀ i, SupportBound T (P.A i)) (hP : Bornology.IsBounded P.dropEqs.construct)
    (hT : T.Nonempty) : -- --- CONCL ---
    Bornology.IsBounded (P.minkDiffOf T u).dropEqs.construct := by -- --- PROOF ---
  obtain ⟨z, hz⟩ := hT
  refine (hP.add (Bornology.isBounded_singleton (x := -z))).subset fun x hx =>
    ⟨x + z, ⟨fun i => ?_, fun i => i.elim0⟩, -z, rfl, by simp⟩
  -- the row was moved past `z`'s value, so `x + z` meets it
  have h := hx.1 i
  have hu := (u i).le z hz
  show P.A i (x + z) ≤ P.b i
  change P.A i x ≤ P.b i - (u i).val at h
  rw [map_add]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
