module

public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEmptySet

@[expose] public section

/-!
# A halfspace description as a constrained zonotope from the inside, over a floating-point scalar

`HPolytope.conZonotope` widens the carried rows by what carrying them rounds off, so it encloses.
`conZonotopeInner` tightens them by the same amount instead, so every coefficient vector meeting
the stored rows meets the exact ones: the stored center and generators are used as they are,
with the polytope's own error box, and whatever box they are taken at, every point stays in the
polytope. (A polytope with an equality row is carried as the empty set.) The
box decides only how much of the polytope is covered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the tightened conversion is a point of `P`: its coefficients meet the exact rows
because the tightening covers the carrying error. -/
theorem HPolytope.conZonotopeInnerOf_subset (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) :
    (P.conZonotopeInnerOf Z).construct ⊆ P.construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, e, he, rfl⟩
  -- a polytope with an equality is carried as the empty set
  by_cases hme : P.me = 0
  swap
  · obtain ⟨β, -, hP, -⟩ := ConZonotope.mem_nominalSet_iff.mp hx
    have hP' : β ∈ (HPolytope.emptySet 𝕋 Z.h).nominal.construct := by
      have : P.onCoefficientsInner Z = HPolytope.emptySet 𝕋 Z.h := by
        simp [HPolytope.onCoefficientsInner, hme]
      rw [show (P.conZonotopeInnerOf Z).P = P.onCoefficientsInner Z from rfl, this] at hP
      exact hP
    have := (HPolytope.mem_nominal_of_origin (P := HPolytope.emptySet 𝕋 Z.h) rfl).mpr hP'
    rw [HPolytope.construct_emptySet] at this
    exact this.elim
  obtain ⟨β, hβ, hP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  have hP' : β ∈ (P.onCoefficientsInner Z).nominal.construct := hP
  simp only [HPolytope.onCoefficientsInner, hme, if_true] at hP'
  obtain ⟨hle, -⟩ := HPolytope.mem_nominal_iff.mp hP'
  refine ⟨x, ?_, e, he, rfl⟩
  refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => absurd i.isLt (by omega)⟩
  -- an inequality row: the tightened bound covers the carrying error and the center
  have hsplit := HPolytope.rowSplit P.A (fun i j => Z.G j i) Z.c β x hval i
  have herr := abs_le.mp (HPolytope.prodError P.A (fun i j => Z.G j i) β hβ i)
  have hc := le_dotUp (P.A i) Z.c
  have h1 := subDown_le_sub (P.b i) (dotUp (P.A i) Z.c)
  have h2 := subDown_le_sub (subDown (P.b i) (dotUp (P.A i) Z.c))
    (radius (matMulDiff P.A (fun i j => Z.G j i)) i)
  have h := hle i
  change (toRealMat (matMulDown P.A (fun i j => Z.G j i)) *ᵥ β) i ≤ toReal (subDown (subDown
    (P.b i) (dotUp (P.A i) Z.c)) (radius (matMulDiff P.A (fun i j => Z.G j i)) i)) at h
  rw [hsplit]
  linarith [herr.1, herr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
