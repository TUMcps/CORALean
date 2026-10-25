module

public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.CoraVertex
public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.CoraNormalCone
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.IsPolytopeCexCoraVertex
public import CORALean.ContSet.PolyZonotope.Real.Counterexamples.IsPolytopeCexCoraNormalCone
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import CORALean.ContSet.PolyZonotope.Real.Operations.IsPolytopeCexCorners

@[expose] public section

/-!
# The `true` path of CORA's `isPolytope`

The `true` path of `isPolytope` [1], with the linear program replaced by cone membership and
the hull vertices given as corner assignments (`convhulln` is not modelled).

# CORA's `isPolytope` accepts a non-polytope

`PolyZonotope.AcceptsCora` holds for `PolyZonotope.isPolytopeCex` and its four hull vertices,
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
def PolyZonotope.AcceptsCora {m : ℕ} (pZ : PolyZonotope α) (corners : Fin m → Fin pZ.p → ℝ) :
    Prop :=
  (∀ i k, pZ.E i k < 2) ∧
    ∀ s t, pZ.coraVertex (corners s) ≠ pZ.coraVertex (corners t) →
      IsInCone (pZ.coraNormalCone (corners s))
        (pZ.coraVertex (corners t) - pZ.coraVertex (corners s))

end CORALean.Real

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_isPolytopeCex_sign {x : ℝ} (h : x = 1 ∨ x = -1) :
    ((SignType.sign x : SignType) : ℝ) = x := by
  rcases h with rfl | rfl <;> simp


/-- For corners with factors `±1`, the difference of two corner images is in the cone as soon as
`b` and `a c` of the first corner have the opposite signs of the two coordinates of it. -/
theorem PolyZonotope.aux_isPolytopeCex_inCone (I J : Fin 3 → ℝ) (hI : ∀ i, I i = 1 ∨ I i = -1)
    (hdx : I 1 * (2 * J 0 + J 1 - (2 * I 0 + I 1)) ≤ 0)
    (hdy : I 0 * I 2 * (J 0 * J 2 - I 0 * I 2) ≤ 0) : -- --- CONCL ---
    IsInCone (PolyZonotope.isPolytopeCex.coraNormalCone I)
      (PolyZonotope.isPolytopeCex.coraVertex J -
        PolyZonotope.isPolytopeCex.coraVertex I) := by -- --- PROOF ---
  have h : ∀ i, I i ≠ 0 := fun i => by rcases hI i with h | h <;> simp [h]
  have s0 := aux_isPolytopeCex_sign (hI 0)
  have s1 := aux_isPolytopeCex_sign (hI 1)
  have s2 := aux_isPolytopeCex_sign (hI 2)
  have q1 : I 1 * I 1 = 1 := by rcases hI 1 with h | h <;> simp [h]
  have q2 : I 0 * I 2 * (I 0 * I 2) = 1 := by
    rcases hI 0 with h | h <;> rcases hI 2 with h' | h' <;> simp [h, h']
  -- coefficients: `0` on the first column, `-b dx` on the second, `-(a c) dy` on the third
  refine ⟨![0, -I 1 * (2 * J 0 + J 1 - (2 * I 0 + I 1)), -(I 0 * I 2) * (J 0 * J 2 - I 0 * I 2)],
    ?_, ?_⟩
  · intro j
    fin_cases j
    · show (0 : ℝ) ≤ 0
      exact le_rfl
    · show 0 ≤ -I 1 * (2 * J 0 + J 1 - (2 * I 0 + I 1))
      linarith
    · show 0 ≤ -(I 0 * I 2) * (J 0 * J 2 - I 0 * I 2)
      linarith
  · -- the sum over the three columns, entry by entry
    rw [PolyZonotope.isPolytopeCex_coraNormalCone I h, PolyZonotope.isPolytopeCex_coraVertex,
      PolyZonotope.isPolytopeCex_coraVertex]
    erw [Fin.sum_univ_three]
    funext i
    fin_cases i
    · show 2 * J 0 + J 1 - (2 * I 0 + I 1) = _
      simp [s1]
      linear_combination (-(2 * J 0 + J 1 - (2 * I 0 + I 1))) * q1
    · show J 0 * J 2 - I 0 * I 2 = _
      simp [s2]
      linear_combination (-(J 0 * J 2 - I 0 * I 2)) * q2


-- =======================================  MAIN THEOREM  ======================================= --

set_option simprocs false in
/-- Exponents: the first test of `isPolytope` does not fire. The vertex test: from each of the four
hull vertices the other three lie in the cone (`isPolytopeCex_coraAccepts`). -/
theorem PolyZonotope.isPolytopeCex_coraAccepts : -- --- CONCL ---
    PolyZonotope.isPolytopeCex.AcceptsCora PolyZonotope.isPolytopeCexCorners := by -- --- PROOF ---
  refine ⟨fun i k => by fin_cases i <;> fin_cases k <;> decide, ?_⟩
  -- the difference of a corner image with itself is in the cone too (`0`), so `≠` is not used
  intro s t _
  fin_cases s <;> fin_cases t <;>
    (apply PolyZonotope.aux_isPolytopeCex_inCone
     · intro i
       fin_cases i <;> simp [PolyZonotope.isPolytopeCexCorners]
     · norm_num [PolyZonotope.isPolytopeCexCorners, Matrix.cons_val_two, Matrix.head_cons,
         Matrix.tail_cons]
     · norm_num [PolyZonotope.isPolytopeCexCorners, Matrix.cons_val_two, Matrix.head_cons,
         Matrix.tail_cons])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
