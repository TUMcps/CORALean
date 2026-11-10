module

public import CORALean.ContSet.ConZonotope.Float.Operations.IntersectHPolytope
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.LeErrUp
public import CORALean.ContSet.HPolytope.Float.Theorems.MemIneqsIff
public import CORALean.ContSet.HPolytope.Float.Theorems.MemStackRowsNominalIff

@[expose] public section

/-!
# `ConZonotope.intersectHPolytope` holds the intersection

A point `y + e` of the set that lies in the polytope has its nominal part `y = c + G β` meet every
carried row: the polytope's row reads `y + e`, so `y` reads it at most the right-hand side less what
`e` adds, which `HPolytope.le_errUp` bounds, and the product `aᵀ G β` is the carried one up to
`radius (matMulDiff …)`. The point keeps its coefficients and its error point. Outer only.

## Inputs
* `cZ` – float constrained zonotope
* `P` – halfspace polytope
* `x` – point

## Hypotheses
* `hx` – the point lies in the set
* `hP` – the point lies in the polytope

## Conclusion
* the point lies in the intersection
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersectHPolytope_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (P : HPolytope 𝕋 (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ cZ.toSet)
    (hP : x ∈ P.toSet) : -- --- CONCL ---
    x ∈ (cZ.intersectHPolytope P).toSet := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  obtain ⟨β, hβ, hβP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hy
  -- the polytope's rows with the slacks folded in, read at `y + e`
  have hrows := ((HPolytope.mem_toSet_iff (HPolytope.isErrFree_of_origin rfl rfl rfl)).mp
    (HPolytope.absorbRounding_outer P hP)).1
  refine ⟨y, ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, ?_, hval⟩, e, he, rfl⟩
  refine HPolytope.mem_stackRows_nominal_iff.mpr ⟨hβP, HPolytope.mem_nominal_iff.mpr
    ⟨fun i => le_add_of_le_of_nonneg ?_ (abs_nonneg _), fun i => i.elim0⟩⟩
  -- one carried row: the split of the product, its carrying error, the center, the error box
  have hsplit := HPolytope.rowSplit P.absorbRounding.A (fun i j => cZ.G j i) cZ.c β y hval i
  have herr := abs_le.mp (HPolytope.prodError P.absorbRounding.A (fun i j => cZ.G j i) β hβ i)
  have hc := dotDown_le (P.absorbRounding.A i) cZ.c
  have hb := sub_le_subUp (P.absorbRounding.b i) (dotDown (P.absorbRounding.A i) cZ.c)
  have hadd := add_le_addUp (subUp (P.absorbRounding.b i) (dotDown (P.absorbRounding.A i) cZ.c))
    (radius (matMulDiff P.absorbRounding.A (fun i j => cZ.G j i)) i)
  have herrU := HPolytope.le_errUp
    ({ P.absorbRounding with I_error := cZ.I_error } : HPolytope 𝕋 (Vec 𝕋 n))
    (-(P.absorbRounding.A i)) he
  have hadd2 := add_le_addUp
    (addUp (subUp (P.absorbRounding.b i) (dotDown (P.absorbRounding.A i) cZ.c))
      (radius (matMulDiff P.absorbRounding.A (fun i j => cZ.G j i)) i))
    ((({ P.absorbRounding with I_error := cZ.I_error } : HPolytope 𝕋 (Vec 𝕋 n))).errUp
      (-(P.absorbRounding.A i)))
  -- the polytope's row at `y + e`, split into the row at `y` and at `e`
  have hxrow := hrows i
  rw [Matrix.mulVec_add, Pi.add_apply] at hxrow
  have hmul : (toRealMat P.absorbRounding.A *ᵥ e) i
      = ∑ j, toReal (P.absorbRounding.A i j) * e j := rfl
  simp only [Pi.neg_apply, toReal_neg', neg_mul, Finset.sum_neg_distrib] at herrU
  rw [hmul] at hxrow
  rw [hsplit] at hxrow
  -- the bound the construction writes, and the row at `β`
  show (toRealMat (matMulDown P.absorbRounding.A fun i j => cZ.G j i) *ᵥ β) i ≤
    toReal (addUp (addUp _ _) _)
  linarith [herr.1, herr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
