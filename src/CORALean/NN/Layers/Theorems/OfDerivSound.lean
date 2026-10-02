import CORALean.NN.Layers.Operations.RelaxationOfDeriv
import CORALean.NN.Layers.Theorems.AbsSubLeSpread
import CORALean.NN.Layers.Theorems.Real.SubMulBoundsOfDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The relaxation a derivative bracket buys is sound

`sub_mul_bounds_of_deriv` is the whole mathematical content, about the exact `σ` and the
exact reals the stored values denote; what is added is that the two ends, evaluated with
rounding, are each pushed outward, and `abs_sub_le_spread` measures from the stored midpoint.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What the bracket buys, and the only place `σ` and its derivative appear. -/
theorem Relaxation.ofDeriv_sound {E : Enclosure 𝕋} {lo hi lam : 𝕋 → 𝕋 → 𝕋} (σ' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt σ (σ' x) x) (hE : E.Sound σ)
    (hlo : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u → toReal (lo l u) ≤ σ' x)
    (hhi : ∀ (l u : 𝕋) (x : ℝ), toReal l ≤ x → x ≤ toReal u → σ' x ≤ toReal (hi l u))
    (hlam : ∀ l u : 𝕋, toReal l ≤ toReal u →
      toReal (lo l u) ≤ toReal (lam l u) ∧ toReal (lam l u) ≤ toReal (hi l u)) :
    (Relaxation.ofDeriv E lo hi lam).Sound σ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  show |σ t - (toReal (lam l u) * t + toReal (Relaxation.curvMid E lo hi lam l u))|
    ≤ toReal (maximum (subUp (Relaxation.curvHi E hi lam l u) (Relaxation.curvMid E lo hi lam l u))
      (subUp (Relaxation.curvMid E lo hi lam l u) (Relaxation.curvLo E lo lam l u)))
  have hle : toReal l ≤ toReal u := le_trans hl hu
  obtain ⟨hlow, hhigh⟩ := Real.sub_mul_bounds_of_deriv
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ _ => hd x)
    (hlo l u) (hhi l u) (hlam l u hle).1 (hlam l u hle).2 hl hu
  have hwidth := sub_le_subUp u l
  have hA : toReal (Relaxation.curvLo E lo lam l u) ≤ σ t - toReal (lam l u) * t := by
    have hfac := subDown_le_sub (lo l u) (lam l u)
    have hfac0 : toReal (subDown (lo l u) (lam l u)) ≤ 0 := by
      have := (hlam l u hle).1
      linarith
    -- a non-positive factor against the widest box: the smallest the product can be
    have hstep : toReal (subDown (lo l u) (lam l u)) * toReal (subUp u l)
        ≤ (toReal (lo l u) - toReal (lam l u)) * (toReal u - toReal l) :=
      le_trans (mul_le_mul_of_nonpos_left hwidth hfac0)
        (mul_le_mul_of_nonneg_right hfac (by linarith))
    have hprod := mulDown_le_mul (subDown (lo l u) (lam l u)) (subUp u l)
    have hint := subDown_le_sub (E.lo l) (mulUp (lam l u) l)
    have hmul := mul_le_mulUp (lam l u) l
    have hend := hE.lo_le l
    have hsum := addDown_le_add (subDown (E.lo l) (mulUp (lam l u) l))
      (mulDown (subDown (lo l u) (lam l u)) (subUp u l))
    rw [Relaxation.curvLo]
    linarith
  have hB : σ t - toReal (lam l u) * t ≤ toReal (Relaxation.curvHi E hi lam l u) := by
    have hfac := sub_le_subUp (hi l u) (lam l u)
    have hfac0 : 0 ≤ toReal (subUp (hi l u) (lam l u)) := by
      have := (hlam l u hle).2
      linarith
    -- both factors non-negative here, so the widest box makes the product largest
    have hstep : (toReal (hi l u) - toReal (lam l u)) * (toReal u - toReal l)
        ≤ toReal (subUp (hi l u) (lam l u)) * toReal (subUp u l) :=
      le_trans (mul_le_mul_of_nonneg_right hfac (by linarith))
        (mul_le_mul_of_nonneg_left hwidth hfac0)
    have hprod := mul_le_mulUp (subUp (hi l u) (lam l u)) (subUp u l)
    have hint := sub_le_subUp (E.hi l) (mulDown (lam l u) l)
    have hmul := mulDown_le_mul (lam l u) l
    have hend := hE.le_hi l
    have hsum := add_le_addUp (subUp (E.hi l) (mulDown (lam l u) l))
      (mulUp (subUp (hi l u) (lam l u)) (subUp u l))
    rw [Relaxation.curvHi]
    linarith
  have hspread := abs_sub_le_spread (c := Relaxation.curvMid E lo hi lam l u) hA hB
  rw [show σ t - (toReal (lam l u) * t + toReal (Relaxation.curvMid E lo hi lam l u))
    = σ t - toReal (lam l u) * t - toReal (Relaxation.curvMid E lo hi lam l u) from by ring]
  exact hspread

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
