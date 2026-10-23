module

public import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# `[1, Prop. 3]` fails at an empty circumbody

`P₁ = {0}` and `P₂ = {x₁ ≤ -1, -x₁ ≤ -1, x₂ ≤ 0}` in `ℝ²`, the second empty (and bounded,
and `ker H₂ = {0}`, as `[1, Def. 1]` asks). The inbody `Px = {0} × [-1, 0]`, `x̄ = 0`,
`X = I`. Weights `λ = (1, 0)`, `β = 0`, `Γ = (0, I)` meet every line of `[1, Prop. 3, Eq. 25]`:
the second summand's `Γ₂ Px = Px` only has to satisfy `H₂ y ≤ 0`, which `x₁ = 0, x₂ ≤ 0`
does. Yet `conv(P₁ ∪ P₂) = {0}` misses `(0, -1)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `[1, Prop. 3]` fails at an empty circumbody

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ahPolytope_subset_convexHull_of_cert_counterexample : -- --- CONCL ---
    ∃ (Hy : Fin 2 → Mat ℝ 4 2) (hy : Fin 2 → Vec ℝ 4) (Hx : Mat ℝ 4 2) (hx : Vec ℝ 4)
      (Λ : Fin 2 → Mat ℝ 4 4) (lam : Fin 2 → ℝ) (β : Fin 2 → Vec ℝ 2) (Γ : Fin 2 → Mat ℝ 2 2),
      (∀ i v, Hy i *ᵥ v = 0 → v = 0) ∧
      (∀ i, Bornology.IsBounded (HPolytope.ineqs (Hy i) (hy i)).construct) ∧
      (∀ i j k, 0 ≤ Λ i j k) ∧ (∀ i, 0 ≤ lam i) ∧ (∀ i, Λ i * Hx = Hy i * Γ i) ∧
      (∀ i, Λ i *ᵥ hx ≤ lam i • hy i + Hy i *ᵥ β i) ∧ ∑ i, lam i = 1 ∧ ∑ i, -β i = 0 ∧
      ∑ i, Γ i = 1 ∧
      ¬ HPolytope.ahPolytope 0 1 (HPolytope.ineqs Hx hx)
        ⊆ convexHull ℝ (⋃ i, (HPolytope.ineqs (Hy i) (hy i)).construct) := by -- --- PROOF ---
  let H₁ : Mat ℝ 4 2 := !![1, 0; -1, 0; 0, 1; 0, -1]
  let H₂ : Mat ℝ 4 2 := !![1, 0; -1, 0; 0, 1; 0, 1]
  let S : Mat ℝ 4 4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 0]
  -- `P₁ = {0}` and `P₂ = ∅`
  have hP₁ : (HPolytope.ineqs H₁ ![0, 0, 0, 0]).construct ⊆ {0} := by
    intro x hx
    rw [HPolytope.mem_ineqs_iff] at hx
    have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
    simp [H₁, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2 h3
    funext i; fin_cases i <;> simp <;> linarith
  have hP₂ : (HPolytope.ineqs H₂ ![-1, -1, 0, 0]).construct = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    rw [HPolytope.mem_ineqs_iff] at hx
    have h0 := hx 0; have h1 := hx 1
    simp [H₂, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    linarith
  refine ⟨![H₁, H₂], ![![0, 0, 0, 0], ![-1, -1, 0, 0]], H₁, ![0, 0, 0, 1], ![0, S], ![1, 0],
    ![0, 0], ![0, 1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the rows of both polytopes have trivial kernel, as `[1, Def. 1]` asks
  · intro i v hv
    have h0 := congrFun hv 0
    have h2 := congrFun hv 2
    fin_cases i <;> simp [H₁, H₂, mulVec, dotProduct, Fin.sum_univ_two] at h0 h2 <;>
      (funext j; fin_cases j <;> simp [h0, h2])
  · intro i
    fin_cases i
    · exact (Bornology.isBounded_singleton (x := (0 : Vec ℝ 2))).subset hP₁
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hP₂]
      exact Bornology.isBounded_empty
  -- the certificate's rows, checked entry by entry
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [S]
  · intro i; fin_cases i <;> simp
  · intro i
    fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      simp [S, H₁, H₂, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [S, H₁, H₂, mulVec, dotProduct, Fin.sum_univ_four]
  · simp
  · simp
  · simp
  -- `(0, -1)` is in the inbody and not in `conv(P₁ ∪ P₂) = {0}`
  · intro hsub
    have hmem : (![0, -1] : Vec ℝ 2)
        ∈ HPolytope.ahPolytope 0 (1 : Mat ℝ 2 2) (HPolytope.ineqs H₁ ![0, 0, 0, 1]) := by
      refine ⟨![0, -1], HPolytope.mem_ineqs_iff.mpr fun i => ?_, by simp⟩
      fin_cases i <;> simp [H₁, mulVec, dotProduct, Fin.sum_univ_two]
    have hU : (⋃ i, (HPolytope.ineqs (![H₁, H₂] i)
        (![![0, 0, 0, 0], ![-1, -1, 0, 0]] i)).construct) ⊆ {0} := by
      refine Set.iUnion_subset fun i => ?_
      fin_cases i
      · exact hP₁
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hP₂]
        exact Set.empty_subset _
    have := convexHull_min hU (convex_singleton 0) (hsub hmem)
    have h1 := congrFun this 1
    simp at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
