module

public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.CoraVertex
public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.CoraNormalCone
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexInCone
public import CORALean.ContSet.PolyZonotope.Real.Operations.IsPolytopeCexCorners

@[expose] public section

/-!
# The `true` path of CORA's `isPolytope`

The `true` path of `isPolytope` [1], with the linear program replaced by cone membership and
the hull vertices given as corner assignments (`convhulln` is not modelled).

# CORA's `isPolytope` accepts a non-polytope

`PolyZonotope.coraAccepts` holds for `PolyZonotope.isPolytopeCex` and its four hull vertices,
so the `true` path of `isPolytope` [1] fires, though the set is not convex
(`references/coverage/contSet/polyZonotope.md`, row `isPolytope`).

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- The model: CORA's code as printed, kept only to be refuted.
/-- The `true` path of `isPolytope`, given the corners `I` of the hull vertices: no exponent `≥ 2`,
and from every hull vertex `v` the difference to every other one lies in the cone of its inward
derivatives. -/
def PolyZonotope.coraAccepts {m : ℕ} (pZ : PolyZonotope α) (corners : Fin m → Fin pZ.p → ℝ) :
    Prop :=
  (∀ i k, pZ.E i k < 2) ∧
    ∀ s t, pZ.coraVertex (corners s) ≠ pZ.coraVertex (corners t) →
      inCone (pZ.coraNormalCone (corners s))
        (pZ.coraVertex (corners t) - pZ.coraVertex (corners s))

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

set_option simprocs false in
/-- Exponents: the first test of `isPolytope` does not fire. The vertex test: from each of the four
hull vertices the other three lie in the cone (`isPolytopeCex_coraAccepts`). -/
theorem PolyZonotope.isPolytopeCex_coraAccepts : -- --- CONCL ---
    PolyZonotope.isPolytopeCex.coraAccepts PolyZonotope.isPolytopeCexCorners := by -- --- PROOF ---
  refine ⟨fun i k => by fin_cases i <;> fin_cases k <;> decide, ?_⟩
  -- the difference of a corner image with itself is in the cone too (`0`), so `≠` is not used
  intro s t _
  fin_cases s <;> fin_cases t <;>
    (apply PolyZonotope.isPolytopeCex_inCone
     · intro i
       fin_cases i <;> simp [PolyZonotope.isPolytopeCexCorners]
     · norm_num [PolyZonotope.isPolytopeCexCorners, Matrix.cons_val_two, Matrix.head_cons,
         Matrix.tail_cons]
     · norm_num [PolyZonotope.isPolytopeCexCorners, Matrix.cons_val_two, Matrix.head_cons,
         Matrix.tail_cons])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
