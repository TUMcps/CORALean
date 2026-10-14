module

public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotopeInner

@[expose] public section

/-!
# A halfspace description as a constrained zonotope from the inside, over a floating-point scalar

`HPolytope.conZonotope` widens the carried rows by what carrying them rounds off, so it encloses.
`conZonotopeInner` tightens them by the same amount instead, so every coefficient vector meeting
the stored rows meets the exact ones: the stored centre and generators are used as they are,
with no error box, and whatever box they are taken at, every point stays in the polytope. The
box decides only how much of the polytope is covered.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the tightened conversion is a point of `P`: its coefficients meet the exact rows
because the tightening covers the carrying error. -/
theorem HPolytope.conZonotopeInnerOf_subset (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) :
    (P.conZonotopeInnerOf Z).construct ⊆ P.construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, e, he, rfl⟩
  -- the error box is the point `0`
  have he0 : e = 0 := funext fun i => by
    have h : toReal (zero : 𝕋) ≤ e i ∧ e i ≤ toReal (zero : 𝕋) := he i
    rw [toReal_zero] at h
    exact le_antisymm h.2 h.1
  subst he0
  show x + 0 ∈ P.construct
  rw [add_zero]
  obtain ⟨β, hβ, hP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hP
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  -- an inequality row: the tightened bound covers the carrying error and the centre
  · have hsplit := HPolytope.rowSplit P.A (fun i j => Z.G j i) Z.c β x hval i
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
  -- an equality's lower end, moved inward
  · have hsplit := HPolytope.rowSplit P.Ae (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError P.Ae (fun i j => Z.G j i) β hβ i)
    have hc := dotDown_le (P.Ae i) Z.c
    have h1 := sub_le_subUp (P.be.inf i) (dotDown (P.Ae i) Z.c)
    have h2 := add_le_addUp (subUp (P.be.inf i) (dotDown (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)
    have h := (heq i).1
    change toReal (addUp (subUp (P.be.inf i) (dotDown (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)) ≤
      (toRealMat (matMulDown P.Ae (fun i j => Z.G j i)) *ᵥ β) i at h
    rw [hsplit]
    linarith [herr.1, herr.2]
  -- and its upper end
  · have hsplit := HPolytope.rowSplit P.Ae (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError P.Ae (fun i j => Z.G j i) β hβ i)
    have hc := le_dotUp (P.Ae i) Z.c
    have h1 := subDown_le_sub (P.be.sup i) (dotUp (P.Ae i) Z.c)
    have h2 := subDown_le_sub (subDown (P.be.sup i) (dotUp (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)
    have h := (heq i).2
    change (toRealMat (matMulDown P.Ae (fun i j => Z.G j i)) *ᵥ β) i ≤ toReal (subDown (subDown
      (P.be.sup i) (dotUp (P.Ae i) Z.c)) (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)) at h
    rw [hsplit]
    linarith [herr.1, herr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
