module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.VPolytopeMemSimplexIff
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A hull as a constrained zonotope, over a floating-point scalar

Exact, and nothing rounds: the vertices become the generators unchanged, the
centre is zero, the error box is carried over, and the constraint polytope is
the standard simplex — whose entries are `one` and `zero` and whose right-hand
side is `one`.

The unit box a constrained zonotope also imposes costs nothing, a nonnegative
coefficient in a family summing to one being at most one already.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conZonotope_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.conZonotope.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hnn, hsum, hval⟩ := hx
  -- a convex coefficient already lies inside the unit box, so that constraint costs nothing
  refine ConZonotope.mem_nominalSet_iff.mpr ⟨β, fun j => ?_, ?_, fun i => ?_⟩
  · rw [abs_of_nonneg (hnn j)]
    exact hsum ▸ Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ j)
  · exact (HPolytope.mem_nominal_of_origin (P := VPolytope.simplex 𝕋 P.k) rfl).mp
      (VPolytope.mem_simplex_iff.mpr ⟨hnn, hsum⟩)
  · have h : x i = ∑ l, β l * toReal (P.V l i) := by
      rw [hval]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [h]
    show ∑ l, β l * toReal (P.V l i) = toReal (zero : 𝕋) + ∑ l, toReal (P.V l i) * β l
    rw [toReal_zero, zero_add]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
