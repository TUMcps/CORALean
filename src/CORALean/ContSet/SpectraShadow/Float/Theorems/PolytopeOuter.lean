module

public import CORALean.ContSet.SpectraShadow.Float.Operations.PolytopeOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.DualBoundLe
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemIneqsIff

@[expose] public section

/-!
# The float outer polytope of a shadow encloses it

Every kept row is a row of a certified dual bound (`dualBound_le`): `Σ aᵣ xᵣ ≤ dualBound` for
every point of the shadow. Outer: finitely many rows, each rounded up.

## Inputs
* `S` – spectrahedral shadow
* `dirs` – vectors indexed by `Fin N`
* `Y` – matrices indexed by `Fin N`

## Hypotheses
* none

## Conclusion
* the float outer polytope of a shadow encloses it
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.polytopeOuter_outer (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (dirs : Fin N → Vec 𝕋 n)
    (Y : (i : Fin N) → Mat 𝕋 S.k S.k) : -- --- CONCL ---
    S.construct ⊆ (S.polytopeOuter dirs Y).construct := by -- --- PROOF ---
  intro x hx
  refine HPolytope.mem_ineqs_iff.2 fun r => ?_
  have hr := (List.mem_filter.1 (List.get_mem
    ((List.finRange N).filter fun i => S.dualCertified (dirs i) (Y i)) r)).2
  have := SpectraShadow.dualBound_le (by simpa using hr) x hx
  simpa [Matrix.mulVec, dotProduct, toRealMat] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
