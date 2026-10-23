module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Halfspaces strictly containing an enclosure are redundant

[1, Sec. 4.1 (interval hull)]: "one can remove all halfspaces that strictly contain the interval
hull of the polytope". True for a nonempty polytope and any enclosure `T`, the interval hull
among them: if some point `x` kept by the other halfspaces broke one of the removed ones,
walking from a point of the polytope towards `x` would reach a point of the polytope on a
removed halfspace's boundary, which `T` does not touch. At an empty polytope it fails; see
`ineqs_eq_of_strict_counterexample`.

## Inputs
* `A` – `q × n` matrix
* `b` – offset vector of length `q`
* `J` – `Finset (Fin q)`
* `T` – set of points

## Hypotheses
* `hne` – the polytope `ineqs A b` is nonempty
* `hT` – `(HPolytope.ineqs A b)` lies in `T`
* `hJ` – the rows in `J` are strict on all of `T`

## Conclusion
* halfspaces strictly containing an enclosure are redundant

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_eq_of_strict (A : Mat ℝ q n) (b : Vec ℝ q) (J : Finset (Fin q))
    (T : Set (Vec ℝ n)) (hne : (HPolytope.ineqs A b).construct.Nonempty)
    (hT : (HPolytope.ineqs A b).construct ⊆ T)
    (hJ : ∀ x ∈ T, ∀ j ∈ J, (A *ᵥ x) j < b j) : -- --- CONCL ---
    {x | ∀ i, i ∉ J → (A *ᵥ x) i ≤ b i} = (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  obtain ⟨p, hp⟩ := hne
  have hpr := HPolytope.mem_ineqs_iff.mp hp
  refine Set.Subset.antisymm (fun x hx => ?_)
    (fun x hx _ _ => HPolytope.mem_ineqs_iff.mp hx _)
  rw [Set.mem_setOf_eq] at hx
  by_contra hxP
  -- the rows `x` breaks, all of them removed ones
  set V := J.filter fun j => b j < (A *ᵥ x) j with hV
  have hVne : V.Nonempty := by
    by_contra hV0
    rw [Finset.not_nonempty_iff_eq_empty] at hV0
    refine hxP (HPolytope.mem_ineqs_iff.mpr fun i => ?_)
    by_cases hi : i ∈ J
    · by_contra hlt
      have : i ∈ V := Finset.mem_filter.mpr ⟨hi, not_le.mp hlt⟩
      rw [hV0] at this
      exact Finset.notMem_empty i this
    · exact hx i hi
  -- the row `x` breaks first along the segment from `p`
  let t : Fin q → ℝ := fun j => (b j - (A *ᵥ p) j) / ((A *ᵥ x) j - (A *ᵥ p) j)
  obtain ⟨j₀, hj₀V, hmin⟩ := V.exists_min_image t hVne
  have hj₀ := Finset.mem_filter.mp hj₀V
  have hpos : ∀ j ∈ V, 0 < (A *ᵥ x) j - (A *ᵥ p) j := fun j hj => by
    have := (Finset.mem_filter.mp hj).2
    linarith [hpr j]
  let z := p + t j₀ • (x - p)
  have hz : ∀ i, (A *ᵥ z) i = (A *ᵥ p) i + t j₀ * ((A *ᵥ x) i - (A *ᵥ p) i) := fun i => by
    simp only [z, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have ht0 : 0 ≤ t j₀ := div_nonneg (by linarith [hpr j₀]) (hpos j₀ hj₀V).le
  have ht1 : t j₀ ≤ 1 := by
    rw [div_le_one (hpos j₀ hj₀V)]
    linarith [hj₀.2]
  -- `z` is a point of the polytope: rows kept hold along the segment, broken rows not yet
  have hzP : z ∈ (HPolytope.ineqs A b).construct := by
    refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
    rw [hz]
    by_cases hiV : i ∈ V
    · have hle := hmin i hiV
      have hpi := hpos i hiV
      have : t j₀ * ((A *ᵥ x) i - (A *ᵥ p) i) ≤ t i * ((A *ᵥ x) i - (A *ᵥ p) i) :=
        mul_le_mul_of_nonneg_right hle hpi.le
      have hti : t i * ((A *ᵥ x) i - (A *ᵥ p) i) = b i - (A *ᵥ p) i := by
        simp only [t]
        field_simp
      linarith
    · -- a row `x` keeps: a convex combination of two values below `b i`
      have hxi : (A *ᵥ x) i ≤ b i := by
        by_cases hi : i ∈ J
        · by_contra hlt
          exact hiV (Finset.mem_filter.mpr ⟨hi, not_le.mp hlt⟩)
        · exact hx i hi
      nlinarith [hpr i]
  -- yet `z` sits on the boundary of the removed row `j₀`, which `T` stays strictly inside
  have hbd : (A *ᵥ z) j₀ = b j₀ := by
    rw [hz]
    simp only [t]
    field_simp [(hpos j₀ hj₀V).ne']
    ring
  exact absurd hbd (hJ z (hT hzP) j₀ hj₀.1).ne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
