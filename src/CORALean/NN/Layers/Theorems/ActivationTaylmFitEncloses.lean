module

public import CORALean.NN.Layers.Operations.ActivationTaylmFit
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Definitions.EvalPoly
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMonoMem
public import CORALean.ContSet.Taylm.Float.Theorems.ConstSparseOuter
public import CORALean.ContSet.Taylm.Float.Theorems.FromRangeOuter
public import CORALean.ContSet.Taylm.Float.Theorems.PlusMergedOuter
public import CORALean.ContSet.Taylm.Float.Theorems.PowBinaryOuter
public import CORALean.ContSet.Taylm.Float.Theorems.ScaleOuter
public import CORALean.ContSet.Taylm.Real.Theorems.MemToSetIff

@[expose] public section

/-!
# What the activation layer on Taylor models encloses, in CORA.cpp's order

`σ` coordinatewise, where every neuron's fit is sound for it and its coefficients above `top` are
zero. A point of the set is a point `t` of the box and values `f i t` of functions the input models
enclose; `f i t` lies in the bounds the fit is taken on (`boundsMono_mem`), so the deviation
`σ (x i) - p (x i)` is within the error and `fromRange` holds it as a constant. The output model
encloses `c₀ + deviation + ∑ c_k f^k` over the powers taken, which at `t` is `σ (x i)` because the
powers left out have zero coefficients.

## Inputs
* `P` – the fit of every neuron
* `top` – the degree of every neuron's fit on a box

## Hypotheses
* `hP` – every neuron's fit is sound for the activation
* `hz` – a coefficient above the degree `top` is zero

## Conclusion
* the layer encloses the activation coordinatewise
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n deg d : ℕ} {σ : ℝ → ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The fold adds each power taken, times its coefficient, to what the start encloses. -/
private theorem aux_fold {x : Taylm 𝕋 d} {f : Vec ℝ d → ℝ} (hf : x.Encloses f)
    (c : Fin (deg + 1) → 𝕋) (p : Fin deg → Prop) [DecidablePred p] :
    ∀ (L : List (Fin deg)) (r : Taylm 𝕋 d) (g : Vec ℝ d → ℝ), r.Encloses g →
      (L.foldl (fun r k => if p k then
          r.plusMerged ((x.powBinary ((k : ℕ) + 1)).scale (c k.succ)) else r) r).Encloses
        fun t => g t + (L.map fun k =>
          if p k then f t ^ ((k : ℕ) + 1) * toReal (c k.succ) else 0).sum
  | [], r, g, h => by simpa using h
  | k :: L, r, g, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    split_ifs with hk
    · have := aux_fold hf c p L _ _
        (Taylm.plusMerged_outer h
          (Taylm.scale_outer (Taylm.powBinary_outer hf ((k : ℕ) + 1)) (c k.succ)))
      convert this using 2 with t
      ring
    · have := aux_fold hf c p L r g h
      convert this using 2 with t
      ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationTaylmFit_encloses {P : LayerRelaxation 𝕋 n deg}
    {top : Fin n → 𝕋 → 𝕋 → ℕ} (hP : ∀ i, (P i).Encloses σ)
    (hz : ∀ i l u (k : Fin deg), top i l u ≤ k →
      toReal ((P i).coeffs l u k.succ) = 0) : -- --- CONCL ---
    (Layer.activationTaylmFit (d := d) P top).Encloses (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  obtain ⟨f, hf, t, ht, hxf⟩ := (Real.Taylm.mem_toSet_iff _ x).1 hx
  -- each neuron's box, fit and deviation at the point
  set l : Fin n → 𝕋 := fun i => (s.taylm i).boundsMono.inf with hl
  set u : Fin n → 𝕋 := fun i => (s.taylm i).boundsMono.sup with hu
  set c : Fin n → Fin (deg + 1) → 𝕋 := fun i => (P i).coeffs (l i) (u i) with hc
  set dv : Fin n → ℝ := fun i =>
    σ (x i) - Real.evalPoly (fun k => toReal (c i k)) (x i) with hdv
  refine (Real.Taylm.mem_toSet_iff _ _).2
    ⟨fun i t' => (toReal (c i 0) + dv i) + ((List.finRange deg).map fun (k : Fin deg) =>
        if (k : ℕ) < top i (l i) (u i) then f i t' ^ ((k : ℕ) + 1) * toReal (c i k.succ)
        else 0).sum, fun i => ?_, t, ht, fun i => ?_⟩
  · -- the constant and the deviation, then the powers
    have hb := Taylm.boundsMono_mem (hf i) ht
    rw [← hxf i] at hb
    have hrel := abs_le.mp ((hP i).sound hb.1 hb.2)
    have h₀ := Taylm.plusMerged_outer (Taylm.constSparse_outer d (c i 0) (s.taylm i).maxOrder).1
      (Taylm.fromRange_outer d (neg ((P i).error (l i) (u i)))
        ((P i).error (l i) (u i)) (s.taylm i).maxOrder (v := dv i)
        (by rw [toReal_neg]; linarith [hrel.1]) hrel.2)
    exact aux_fold (hf i) (c i) (fun k : Fin deg => (k : ℕ) < top i (l i) (u i)) _ _ _ h₀
  · -- at `t` the fit plus its deviation is `σ (x i)`: the powers left out have zero coefficients
    have hsum : ((List.finRange deg).map fun (k : Fin deg) =>
        if (k : ℕ) < top i (l i) (u i) then f i t ^ ((k : ℕ) + 1) * toReal (c i k.succ)
        else 0).sum = ∑ k : Fin deg, toReal (c i k.succ) * x i ^ ((k : ℕ) + 1) := by
      rw [Fin.sum_univ_def]
      congr 1
      refine List.map_congr_left fun k _ => ?_
      split_ifs with hk
      · rw [hxf i]; ring
      · rw [hz i (l i) (u i) k (not_lt.1 hk)]; ring
    simp only
    rw [hsum, hdv]
    simp only [Real.evalPoly, Fin.sum_univ_succ, pow_zero, mul_one, Fin.val_succ, Fin.val_zero]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
