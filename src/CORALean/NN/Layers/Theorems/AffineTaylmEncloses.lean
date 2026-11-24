module

public import CORALean.NN.Layers.Operations.AffineTaylm
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusMergedOuter
public import CORALean.ContSet.Taylm.Float.Theorems.PlusScalarOuter
public import CORALean.ContSet.Taylm.Float.Theorems.ScaleOuter
public import CORALean.ContSet.Taylm.Real.Theorems.MemToSetIff

@[expose] public section

/-!
# What the affine layer on Taylor models encloses

A point of the input set is a point `t` of the box and the values `f j t` of functions the input
models enclose; output `i` encloses `∑ j f j · W i j + b i` (`scale_outer`, `plusMerged_outer`,
`plusScalar_outer` along the fold), whose value at `t` is the affine map at the point.

## Inputs
* `W` – weights
* `b` – bias

## Hypotheses
* none

## Conclusion
* the layer encloses `x ↦ W x + b`
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold adds each scaled model's function to what the start encloses. -/
private theorem aux_fold {x : Fin (n + 1) → Taylm 𝕋 d} {f : Fin (n + 1) → Vec ℝ d → ℝ}
    (hf : ∀ j, (x j).Encloses (f j)) (w : Fin (n + 1) → 𝕋) :
    ∀ (L : List (Fin n)) (acc : Taylm 𝕋 d) (g : Vec ℝ d → ℝ), acc.Encloses g →
      (L.foldl (fun acc j => acc.plusMerged ((x j.succ).scale (w j.succ))) acc).Encloses
        fun t => g t + (L.map fun j => f j.succ t * toReal (w j.succ)).sum
  | [], acc, g, h => by simpa using h
  | j :: L, acc, g, h => by
    have := aux_fold hf w L _ _
      (Taylm.plusMerged_outer h (Taylm.scale_outer (hf j.succ) (w j.succ)))
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    convert this using 2 with t
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.affineTaylm_encloses (W : Mat 𝕋 m (n + 1)) (b : Vec 𝕋 m) : -- --- CONCL ---
    (Layer.affineTaylm (d := d) W b).Encloses
      fun x => toRealMat W *ᵥ x + toRealVec b := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  obtain ⟨f, hf, t, ht, hxf⟩ := (Real.Taylm.mem_toSet_iff _ x).1 hx
  refine (Real.Taylm.mem_toSet_iff _ _).2 ⟨fun i t' =>
      (f 0 t' * toReal (W i 0) + ((List.finRange n).map fun j =>
        f j.succ t' * toReal (W i j.succ)).sum) + toReal (b i), fun i => ?_, t, ht, fun i => ?_⟩
  · exact Taylm.plusScalar_outer
      (aux_fold hf (W i) _ _ _ (Taylm.scale_outer (hf 0) (W i 0))) (b i)
  · -- at `t` the sum is the affine map at the point
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, toRealMat, toRealVec, Fin.sum_univ_succ,
      Fin.sum_univ_def]
    rw [hxf 0]
    congr 1
    congr 1
    · ring
    · congr 1; exact List.map_congr_left fun j _ => by rw [hxf j.succ, mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
