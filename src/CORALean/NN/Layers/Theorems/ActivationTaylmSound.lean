module

public import CORALean.ContSet.Taylm.Float.Theorems.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter
public import CORALean.ContSet.Taylm.Float.Theorems.PowOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SmulOuter
public import CORALean.ContSet.Taylm.Float.Theorems.SumOuter
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.NN.Layers.Operations.ActivationTaylm
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.TaylmIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# What the activation layer on Taylor models encloses

`σ` coordinatewise, where every neuron's relaxation is sound for it. A point of the set is a
point `t` of the box and the values `f i t` of functions the models enclose; the fit
evaluated at `f i` and the constant deviation `σ (x i) - p (x i)`, which the error bounds,
are functions the output models enclose, and at `t` they add up to `σ (x i)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n deg d : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activationTaylm_sound {P : LayerRelaxation 𝕋 n deg}
    (hP : ∀ i, (P i).Sound σ) :
    (Layer.activationTaylm (d := d) P).Sound (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  -- the point is a point of the box and the values of functions the input models enclose
  have hbox := Taylm.interval_contains s.taylm hx
  obtain ⟨f, hf, t, ht, hxf⟩ := (Real.Taylm.mem_construct_iff _ x).1 hx
  -- the fit's coefficients on each neuron's range, and the deviation of `σ` from the fit at `x`
  set c : Fin n → Fin (deg + 1) → ℝ := fun i k =>
    toReal ((P i).coeffs ((Taylm.interval s.taylm).inf i) ((Taylm.interval s.taylm).sup i) k)
    with hc
  set dv : Fin n → ℝ := fun i => σ (x i) - Real.evalPoly (c i) (x i) with hdv
  refine (Real.Taylm.mem_construct_iff _ _).2
    ⟨fun i s' => (c i 0 + dv i) + ∑ k : Fin deg, c i k.succ * f i s' ^ ((k : ℕ) + 1), ?_, t, ht,
      fun i => ?_⟩
  · -- each output model encloses the fit at `f i` plus the constant deviation
    intro i
    have hrel := abs_le.mp ((hP i).sound (hbox i).1 (hbox i).2)
    have hrem : (⟨[], neg ((P i).error ((Taylm.interval s.taylm).inf i)
        ((Taylm.interval s.taylm).sup i)),
        (P i).error ((Taylm.interval s.taylm).inf i) ((Taylm.interval s.taylm).sup i),
        (s.taylm i).maxOrder⟩ : Taylm 𝕋 d).Encloses fun _ => dv i := by
      intro t' _
      simp only [Taylm.nominal, Real.Taylm.poly, Real.Taylm.polyOf_nil, List.map_nil, sub_zero,
        toReal_neg]
      exact ⟨hrel.1, hrel.2⟩
    -- constant, remainder box, then the sum of the scaled powers
    exact Taylm.plus_outer (Taylm.plus_outer (Taylm.const_outer _ _) hrem)
      (Taylm.sum_outer fun k => Taylm.smul_outer ⟨le_refl _, le_refl _⟩
        (Taylm.pow_outer (hf i) _))
  · -- at `t` the fit plus its deviation is `σ (x i)`
    simp only
    rw [← hxf i, hdv]
    simp only [Real.evalPoly, Fin.sum_univ_succ, pow_zero, mul_one, Fin.val_succ, Fin.val_zero]
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
