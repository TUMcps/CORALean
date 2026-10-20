module

public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominal
public import CORALean.ContSet.ConZonotope.Float.Operations.MtimesNominalErr
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeRowSplit
public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeProdError

@[expose] public section

/-!
# A point of `mtimesNominal` is within `mtimesNominalErr` of the exact image of a nominal point

A coefficient vector of the rounded product names the same coefficients in `cZ`, and the point
they name there is mapped by the matrix: the rounded center and the rounded generators are each
within a directed rounding of the exact ones, the generators' over the unit box
(`HPolytope.prodError`).

## Inputs
* `M` – matrix
* `cZ` – float constrained zonotope
* `p` – point of the rounded product

## Hypotheses
* `hp` – the point lies in the nominal set of the rounded product

## Conclusion
* it is near the exact image of a nominal point
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.mtimesNominal_err (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) {p : Vec ℝ m}
    (hp : p ∈ nominalSet (cZ.mtimesNominal M)) :
    ∃ z ∈ nominalSet cZ, ∀ i, |p i - (toRealMat M *ᵥ z) i|
      ≤ toReal (cZ.mtimesNominalErr M i) := by -- --- PROOF ---
  obtain ⟨β, hβ, hP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hp
  -- the point the same coefficients name in `cZ`
  have hz : (fun i => toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * β j) ∈ nominalSet cZ :=
    ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, hP, fun _ => rfl⟩
  refine ⟨_, hz, fun i => ?_⟩
  have hsplit := HPolytope.rowSplit M (fun i j => cZ.G j i) cZ.c β _ (fun _ => rfl) i
  have herr := abs_le.mp (HPolytope.prodError M (fun i j => cZ.G j i) β hβ i)
  have hc1 := dotDown_le (M i) cZ.c
  have hc2 := le_dotUp (M i) cZ.c
  have hc3 := sub_le_subUp (dotUp (M i) cZ.c) (dotDown (M i) cZ.c)
  have hadd := add_le_addUp (subUp (dotUp (M i) cZ.c) (dotDown (M i) cZ.c))
    (radius (matMulDiff M fun i j => cZ.G j i) i)
  have hpi : p i = toReal (dotDown (M i) cZ.c)
      + (toRealMat (matMulDown M fun i j => cZ.G j i) *ᵥ β) i := by
    rw [hval i]
    rfl
  show |p i - (toRealMat M *ᵥ _) i| ≤ toReal (addUp _ _)
  rw [hsplit, hpi, abs_le]
  constructor <;> linarith [herr.1, herr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
