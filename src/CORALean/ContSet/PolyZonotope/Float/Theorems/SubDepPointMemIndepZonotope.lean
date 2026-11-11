module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber
public import CORALean.ContSet.PolyZonotope.Float.Operations.IndepZonotope
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A fiber point less the dependent part is independent

The fiber of `pZ` at `a` is the dependent point plus the independent part: what is left after
subtracting the nominal point is a point of `indepZonotope`.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values
* `x` – point

## Hypotheses
* `hx` – the point is in the fiber at `a`

## Conclusion
* the point less the nominal point is in `indepZonotope`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A fiber point less the dependent part is a point of the independent zonotope. -/
theorem PolyZonotope.sub_depPoint_mem_indepZonotope (pZ : PolyZonotope (Vec 𝕋 n))
    {a : Fin pZ.p → ℝ} {x : Vec ℝ n} (hx : x ∈ pZ.fiber a) : -- --- CONCL ---
    x - pZ.nominal.point a ∈ pZ.indepZonotope.toSet := by -- --- PROOF ---
  obtain ⟨β, hβ, e, he, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  refine ⟨fun i => ∑ j, toReal (pZ.GI j i) * β j,
    Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ, fun i => ?_⟩, e, he, ?_⟩
  · show _ = toReal (zero : 𝕋) + _
    rw [toReal_zero, zero_add]
    rfl
  · funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
