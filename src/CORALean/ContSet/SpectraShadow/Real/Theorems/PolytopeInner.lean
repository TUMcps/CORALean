module

public import CORALean.ContSet.SpectraShadow.Real.Operations.PolytopeInner
public import CORALean.ContSet.SpectraShadow.Real.Theorems.TranslateMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# The inner polytope of a shadow is inside it

The vertices are the points `v` of `SpS - c` that the support function returns, plus `c`: points
of the shadow. A shadow is convex, so their hull is inside it. Inner: the hull of finitely many
boundary points is not the shadow. The theorem asks only that each `v` be a point of `SpS - c`,
as the solver's maximisers are.

## Inputs
* `S` – spectrahedral shadow
* `c` – center of length `n`
* `v` – vectors indexed by `Fin N`

## Hypotheses
* `hv` – every `v i` lies in the shadow shifted by `-c`

## Conclusion
* the inner polytope of a shadow is inside it
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.polytopeInner_inner (S : SpectraShadow (Vec ℝ n)) (c : Vec ℝ n)
    (v : Fin N → Vec ℝ n) (hv : ∀ i, v i ∈ (S.translate (-c)).construct) :
    (SpectraShadow.polytopeInner (N := N) c v).construct ⊆ S.construct := by
  rintro x ⟨β, hβ0, hβ1, rfl⟩
  refine Convex.sum_mem (SpectraShadow.convex_construct S) (fun j _ => hβ0 j) hβ1 (fun j _ => ?_)
  have := (S.mem_translate_iff (-c) (v j)).1 (hv j)
  simpa [SpectraShadow.polytopeInner] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
