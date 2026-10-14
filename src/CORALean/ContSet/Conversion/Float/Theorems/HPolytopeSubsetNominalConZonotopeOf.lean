module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError

@[expose] public section

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the coefficients meet the carried rows because the widening covers the carrying error
theorem HPolytope.subset_nominal_conZonotopeOf (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n))
    (hZ : P.construct ⊆ nominalSet Z) :
    P.construct ⊆ nominalSet (P.conZonotopeOf Z) := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hval⟩ := Zonotope.mem_nominalSet_iff.mp (hZ hx)
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hx
  refine ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, ?_, hval⟩
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · show (toRealMat (matMulDown P.A (fun i j => Z.G j i)) *ᵥ β) i
        ≤ toReal (addUp (subUp (P.b i) (dotDown (P.A i) Z.c))
          (radius (matMulDiff P.A (fun i j => Z.G j i)) i))
    have hsplit := HPolytope.rowSplit P.A (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError P.A (fun i j => Z.G j i) β hβ i)
    have hc := dotDown_le (P.A i) Z.c
    have hb := sub_le_subUp (P.b i) (dotDown (P.A i) Z.c)
    have hadd := add_le_addUp (subUp (P.b i) (dotDown (P.A i) Z.c))
      (radius (matMulDiff P.A (fun i j => Z.G j i)) i)
    have h := hle i
    rw [hsplit] at h
    linarith [herr.1, herr.2]
  -- an equality's lower end, widened downward
  · show toReal (subDown (subDown (P.be.inf i) (dotUp (P.Ae i) Z.c))
          (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i))
        ≤ (toRealMat (matMulDown P.Ae (fun i j => Z.G j i)) *ᵥ β) i
    have hsplit := HPolytope.rowSplit P.Ae (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError P.Ae (fun i j => Z.G j i) β hβ i)
    have hc := le_dotUp (P.Ae i) Z.c
    have hb := subDown_le_sub (P.be.inf i) (dotUp (P.Ae i) Z.c)
    have hsub := subDown_le_sub (subDown (P.be.inf i) (dotUp (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)
    have h := (heq i).1
    rw [hsplit] at h
    linarith [herr.1, herr.2]
  -- and its upper end, widened upward
  · show (toRealMat (matMulDown P.Ae (fun i j => Z.G j i)) *ᵥ β) i
        ≤ toReal (addUp (subUp (P.be.sup i) (dotDown (P.Ae i) Z.c))
          (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i))
    have hsplit := HPolytope.rowSplit P.Ae (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError P.Ae (fun i j => Z.G j i) β hβ i)
    have hc := dotDown_le (P.Ae i) Z.c
    have hb := sub_le_subUp (P.be.sup i) (dotDown (P.Ae i) Z.c)
    have hadd := add_le_addUp (subUp (P.be.sup i) (dotDown (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)
    have h := (heq i).2
    rw [hsplit] at h
    linarith [herr.1, herr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
