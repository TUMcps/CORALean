module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Theorems.AnchorSlabOuter
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.ErrFreeOfIsErrFree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalSubsetNominalZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar

The rows are carried onto the coefficients by composing with the generators,
which is a matrix product and so rounds. That is the difficulty this pair has
and the others do not: a rounded product does not merely shift a bound, it says
something *different* about the coefficients, and a constraint that says
something different can cut off points the original kept.

So the composed rows are stored rounded down and the bounds are widened by what
the rounding can reach — `matMulDiff` records the gap entrywise, and `radius`
sums it over a row, which is the most a coefficient vector in the unit box can
turn that gap into. An equality row of a polytope without an error box reads between two such
bounds, and `ConZonotope.anchorSlab` keeps it an equality where it can certify one
(`ConZonotope.anchorSlab_outer`); a polytope with an error box is carried with the box folded
into its rows, each equality as the two inequalities it stands for, both moved outward.

The lemma holds for any zonotope containing the polytope; `conZonotope` uses the
box because that is what the certificates already give.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The coefficients of a point of the polytope meet the carried rows, because the widening
covers the carrying error, and so does the point, with its error-box point `0`. -/
private theorem HPolytope.subset_conZonotopeOf (P : HPolytope 𝕋 (Vec 𝕋 n))
    (Z : Zonotope (Vec 𝕋 n)) (hZ : P.construct ⊆ nominalSet Z)
    (h0 : (0 : Vec ℝ n) ∈ Z.I_error.construct) :
    P.construct ⊆ (P.conZonotopeOf Z).construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨β, hβ, hval⟩ := Zonotope.mem_nominalSet_iff.mp (hZ hx)
  -- carried inequalities hold at `β` wherever they held at `x`
  have hcarry : ∀ {Q : HPolytope 𝕋 (Vec 𝕋 n)} (i : Fin Q.m),
      (toRealMat Q.A *ᵥ x) i ≤ toReal (Q.b i) →
      (toRealMat (matMulDown Q.A (fun i j => Z.G j i)) *ᵥ β) i
        ≤ toReal (addUp (subUp (Q.b i) (dotDown (Q.A i) Z.c))
          (radius (matMulDiff Q.A (fun i j => Z.G j i)) i)) := by
    intro Q i h
    have hsplit := HPolytope.rowSplit Q.A (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError Q.A (fun i j => Z.G j i) β hβ i)
    have hc := dotDown_le (Q.A i) Z.c
    have hb := sub_le_subUp (Q.b i) (dotDown (Q.A i) Z.c)
    have hadd := add_le_addUp (subUp (Q.b i) (dotDown (Q.A i) Z.c))
      (radius (matMulDiff Q.A (fun i j => Z.G j i)) i)
    rw [hsplit] at h
    linarith [herr.1, herr.2]
  rw [← add_zero x]
  unfold HPolytope.conZonotopeOf
  split_ifs with hP
  -- error-free: the equalities carried too, between their two bounds, then anchored
  · obtain ⟨hle, heq⟩ := (HPolytope.mem_construct_iff (HPolytope.errFree_of_isErrFree hP)).mp hx
    refine ConZonotope.anchorSlab_outer _ _ _ _ (Set.add_mem_add
      (ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, HPolytope.mem_stackRows_nominal_iff.mpr
        ⟨HPolytope.mem_nominal_iff.mpr
          ⟨fun i => le_add_of_le_of_nonneg (hcarry i (hle i)) (abs_nonneg _), fun i => i.elim0⟩,
          HPolytope.mem_slab_nominal_iff.mpr fun i => ?_⟩, hval⟩) h0)
    have hsplit := HPolytope.rowSplit P.Ae (fun i j => Z.G j i) Z.c β x hval i
    have herr := abs_le.mp (HPolytope.prodError P.Ae (fun i j => Z.G j i) β hβ i)
    have hd := dotDown_le (P.Ae i) Z.c
    have hu := le_dotUp (P.Ae i) Z.c
    have h1 := sub_le_subUp (P.be i) (dotDown (P.Ae i) Z.c)
    have h2 := add_le_addUp (subUp (P.be i) (dotDown (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)
    have h3 := subDown_le_sub (P.be i) (dotUp (P.Ae i) Z.c)
    have h4 := subDown_le_sub (subDown (P.be i) (dotUp (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae (fun i j => Z.G j i)) i)
    have h := heq i
    rw [hsplit] at h
    constructor <;> linarith [herr.1, herr.2]
  -- with a box: the rows with the box folded in, which hold at `x`
  · obtain ⟨hle, -⟩ := (HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mp
      (HPolytope.absorbRounding_outer P hx)
    exact Set.add_mem_add (ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ,
      HPolytope.mem_nominal_iff.mpr
          ⟨fun i => le_add_of_le_of_nonneg (hcarry i (hle i)) (abs_nonneg _), fun i => i.elim0⟩,
        hval⟩) h0

theorem HPolytope.conZonotope_contains {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conZonotope up lo).construct := by -- --- PROOF ---
  refine HPolytope.subset_conZonotopeOf P _ (fun y hy =>
    Interval.subset_nominal_zonotope _ (HPolytope.interval_contains up lo hy)) fun i => ?_
  show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
  rw [toReal_zero]
  exact ⟨le_refl 0, le_refl 0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
