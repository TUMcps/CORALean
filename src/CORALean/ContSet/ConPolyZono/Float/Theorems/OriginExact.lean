module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Origin
public import CORALean.ContSet.ConPolyZono.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `ConPolyZono.origin` is exactly the origin

`zero` reads as `0`, so the nominal part is the exact layer's point constrained
polynomial zonotope at the origin, and the error box is the origin box.
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

theorem ConPolyZono.origin_exact (n : ℕ) :
    (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  -- the stored zeros read as ℝ's, so the nominal part is the exact layer's point
  have hc : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  have hb : (Interval.origin 0 : Interval (Vec 𝕋 0)).nominal = ⟨0, 0⟩ := by
    unfold Interval.origin Interval.nominal
    congr 1 <;> funext i <;> exact i.elim0
  have h : InflatedContSet.nominal (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n))
      = Real.ConPolyZono.ofPoint (0 : Vec ℝ n) := by
    unfold Real.ConPolyZono.ofPoint
    show (⟨0, 0, 0, 0, 0, toRealVec (fun _ : Fin n => (zero : 𝕋)), _, _, _, _,
        (Interval.origin 0 : Interval (Vec 𝕋 0)).nominal, _⟩ : Real.ConPolyZono (Vec ℝ n))
      = ⟨0, 0, 0, 0, 0, 0, _, _, _, _, ⟨0, 0⟩, _⟩
    congr 1
    all_goals exact funext fun l => l.elim0
  -- the nominal part denotes `{0}`, and so does the box
  have hN : InflatedContSet.nominalSet (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)) = {0} := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Set.ext fun x =>
      (Real.ConPolyZono.mem_ofPoint_iff (0 : Vec ℝ n) x).trans Set.mem_singleton_iff.symm
  have hE : (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)).err.construct = {0} :=
    Interval.origin_exact n
  -- the sum of the two singletons
  show InflatedContSet.nominalSet (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n))
      + (ConPolyZono.origin n : ConPolyZono 𝕋 (Vec 𝕋 n)).err.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
