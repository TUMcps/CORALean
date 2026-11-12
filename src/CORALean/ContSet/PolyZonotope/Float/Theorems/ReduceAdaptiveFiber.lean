module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceAdaptive
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactGensFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByPoint

@[expose] public section

/-!
# `reduceAdaptive` keeps every fiber

Boxing the generators the adaptive rule selects moves their share at each factor value into the
independent block (`reduceBy_point`), and adding the equal exponent columns keeps the fiber with
the gap in the error box (`compactGens_fiber`); so a point of the set at some factor values is
still a point at those values, which is what an `exactPlus` with a set over the same factors needs.

## Inputs
* `pZ` – polynomial zonotope
* `diagpercent` – admissible distance
* `p` – square root precision
* `a` – factor values
* `x` – point

## Hypotheses
* `ha` – the factor values lie in the unit box
* `hx` – the point is in the fiber of `pZ`

## Conclusion
* the point is in the fiber of the reduced set at the same values
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n d r dI rI : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Boxing generators keeps the fiber at every factor value. -/
private theorem PolyZonotope.aux_reduceBy_fiber (pZ : PolyZonotope (Vec 𝕋 n))
    (partD : Split (Fin pZ.h) into (Fin d) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin rI)) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) {x : Vec ℝ n} (hx : x ∈ pZ.fiber a) : -- --- CONCL ---
    x ∈ (pZ.reduceBy partD partI).fiber a := by -- --- PROOF ---
  obtain ⟨β, hβ, e, he, hxe⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  obtain ⟨β', hβ', hpt⟩ := PolyZonotope.reduceBy_point pZ partD partI ha hβ
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨β', hβ', e, he, ?_⟩
  rw [hxe]
  funext i
  repeat rw [PolyZonotope.nominal_point_eq]
  simp only [Pi.add_apply]
  exact congrArg (· + e i) (hpt i)

/-- `materialise` changes nothing the fiber can see, so `compactGens` keeps it through it. -/
private theorem PolyZonotope.aux_materialise_compactGens_fiber (Q : PolyZonotope (Vec 𝕋 n))
    {a : Fin Q.p → ℝ} (ha : ∀ k, |a k| ≤ 1) {x : Vec ℝ n} (hx : x ∈ Q.fiber a) :
    x ∈ Q.materialise.compactGens.fiber a :=
  PolyZonotope.compactGens_fiber Q.materialise (a := a) ha
    ((PolyZonotope.fiber_materialise Q a).symm ▸ hx)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reduction keeps every fiber at the factor values it was taken at. -/
theorem PolyZonotope.reduceAdaptive_fiber (pZ : PolyZonotope (Vec 𝕋 n)) (diagpercent : 𝕋)
    (p : ℕ) {a : Fin pZ.p → ℝ} (ha : ∀ k, |a k| ≤ 1) {x : Vec ℝ n} (hx : x ∈ pZ.fiber a) :
    x ∈ (pZ.reduceAdaptive diagpercent p).fiber a := by
  unfold PolyZonotope.reduceAdaptive
  simp only []
  exact PolyZonotope.aux_materialise_compactGens_fiber (pZ.reduceBy _ _) ha
    (PolyZonotope.aux_reduceBy_fiber pZ _ _ ha hx)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
