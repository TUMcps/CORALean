module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Origin
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `PolyZonotope.origin` is exactly the origin

`zero` reads as `0`, so the nominal part is the exact layer's point polynomial
zonotope at the origin, and the error box is the origin box.

## Inputs
* `n` – dimension

## Hypotheses
* none

## Conclusion
* the set is exactly the origin
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.origin_exact (n : ℕ) : -- --- CONCL ---
    (PolyZonotope.origin n : PolyZonotope (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  have h : InflatedContSet.nominal (PolyZonotope.origin n : PolyZonotope (Vec 𝕋 n))
      = Real.PolyZonotope.ofPoint (0 : Vec ℝ n) := by
    unfold PolyZonotope.origin Real.PolyZonotope.ofPoint
    show (⟨0, 0, 0, toRealVec (fun _ : Fin n => (zero : 𝕋)), _, _, _⟩ : Real.PolyZonotope (Vec ℝ n))
      = ⟨0, 0, 0, 0, _, _, _⟩
    have hc : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
    congr 1
    · funext l; exact l.elim0
    · funext l; exact l.elim0
  have hN : InflatedContSet.nominalSet (PolyZonotope.origin n : PolyZonotope (Vec 𝕋 n)) = {0} := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Set.ext fun x =>
      (Real.PolyZonotope.mem_ofPoint_iff (0 : Vec ℝ n) x).trans Set.mem_singleton_iff.symm
  have hE : (PolyZonotope.origin n : PolyZonotope (Vec 𝕋 n)).I_error.construct = {0} :=
    Interval.origin_exact n
  show InflatedContSet.nominalSet (PolyZonotope.origin n : PolyZonotope (Vec 𝕋 n))
      + (PolyZonotope.origin n : PolyZonotope (Vec 𝕋 n)).I_error.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
