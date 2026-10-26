module

public import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachCZFloat
public import CORALean.ContSet.HPolytope.Float.Theorems.MinkDiffOfInner
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIffExact
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner
public import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEmptySet

@[expose] public section

/-!
# The float `CZ(P ⊖ Ẑ_W(τ_k))` is inside the eroded polytope

`maxBackReachCZFloat` is `HPolytope.conZonotopeInner` of `P.minkDiffOf Ẑ_W`: the first is inside
`P ⊖ Ẑ_W` by `minkDiffOf_inner`, whose equality-row condition is asked of the subtrahend, and the
second is inside the polytope it converts, wherever its box lies.
The lines are those of [1, Alg. 3].

## Inputs
* `Bx` – conversion box
* `P` – float polytope
* `ZW` – float disturbance zonotope

## Hypotheses
* `hker` – equality rows of the polytope vanish on the zonotope

## Conclusion
* the float conversion lies inside the eroded polytope

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed Continuous-Time
      Linear Systems Using Set Propagation". IEEE Transactions on Automatic Control, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Float
section
open Pointwise Matrix InflatedContSet
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- A point of the tightened conversion is a point of `P`: its coefficients meet the exact rows
because the tightening covers the carrying error. -/
private theorem HPolytope.aux_conZonotopeInnerOf_subset (P : HPolytope 𝕋 (Vec 𝕋 n))
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
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
  obtain ⟨hle, -⟩ := (HPolytope.mem_nominal_iff_exact
    ⟨fun _ => toReal_zero, fun _ => toReal_zero⟩).mp hP'
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
  linarith [herr.1, herr.2, abs_nonneg (toReal (P.b_error i))]


/-- Inside `P`, whatever box the conversion is taken at. -/
private theorem HPolytope.aux_conZonotopeInner_subset (P : HPolytope 𝕋 (Vec 𝕋 n))
    (Bx : Interval (Vec 𝕋 n)) :
    (P.conZonotopeInner Bx).construct ⊆ P.construct :=
  P.aux_conZonotopeInnerOf_subset Bx.zonotope

end
end Float


-- =======================================  MAIN THEOREM  ======================================= --

/-- Line 11 in floats is inside `P ⊖ Ẑ_W`, at every conversion box. -/
theorem LinearSys.maxBackReachCZFloat_inner (Bx : Interval (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (ZW : Zonotope (Vec 𝕋 n)) (hker : ∀ i, ∀ y ∈ ZW.construct, (toRealMat P.Ae *ᵥ y) i = 0) :
    (LinearSys.maxBackReachCZFloat Bx P ZW).construct ⊆
      minkowskiDiff P.construct ZW.construct := fun _ hx =>
  HPolytope.minkDiffOf_inner _ _ _ hker (HPolytope.aux_conZonotopeInner_subset _ Bx hx)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
