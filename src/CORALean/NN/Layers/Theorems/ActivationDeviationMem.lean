module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.RelaxationBox

@[expose] public section

/-!
# The deviation of an activation from its chosen affine map is in the relaxation's box

At a point of the input box, `σ x` minus the affine map the relaxation chose, coordinatewise, lies
in `Relaxation.box`: `sound` bounds the deviation by `offset ± error`, and `subDown`/`addUp` widen
the two ends outward. It is what `Layer.activation` adds to the image of the set, and so what its
enclosure and its tracking of the generators are both made of.

## Inputs
* `R` – relaxation of the activation
* `P` – condition on the input box
* `J` – input box
* `x` – point of the input box

## Hypotheses
* `hR` – relaxation is sound where the condition holds
* `hx` – point lies in the box
* `hP` – every coordinate's box satisfies the condition

## Conclusion
* the deviation of the activation of the point from the affine map lies in the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet ContSetLike Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.deviation_mem_box {R : Relaxation 𝕋} {P : 𝕋 → 𝕋 → Prop}
    (hR : R.EnclosesWhere σ P) {J : Interval (Vec 𝕋 n)} {x : Vec ℝ n} (hx : x ∈ toSet J)
    (hP : ∀ i, P (J.inf i) (J.sup i)) : -- --- CONCL ---
    (fun i => σ (x i) - (Scalar.toRealMat (R.step_slopeMat J) *ᵥ x) i) ∈
      Interval.toSet (R.box J) := by -- --- PROOF ---
  set A : Mat ℝ n n := Scalar.toRealMat (R.step_slopeMat J) with hA
  have hslope : ∀ i, (A *ᵥ x) i = toReal (R.slope (J.inf i) (J.sup i)) * x i := by
    intro i
    have hdiag : A = Matrix.diagonal (toRealVec fun i => R.slope (J.inf i) (J.sup i)) := by
      funext p q
      exact toReal_diagonalBlock _ p q
    rw [hdiag]
    exact Matrix.mulVec_diagonal _ _ i
  intro i
  have hlo : toReal (J.inf i) ≤ x i := (hx i).1
  have hhi : x i ≤ toReal (J.sup i) := (hx i).2
  have hrel := abs_le.mp (hR.sound (hP i) hlo hhi)
  have hval : σ (x i) - (A *ᵥ x) i
      = σ (x i) - toReal (R.slope (J.inf i) (J.sup i)) * x i := by rw [hslope i]
  -- `sound` is an absolute value, and `subDown`/`addUp` widen its two ends outward
  have hlow := subDown_le_sub (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))
  have hhigh := add_le_addUp (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))
  refine ⟨?_, ?_⟩
  · show toReal (subDown (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))) ≤
      σ (x i) - (A *ᵥ x) i
    rw [hval]
    linarith [hrel.1]
  · show σ (x i) - (A *ᵥ x) i ≤
      toReal (addUp (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i)))
    rw [hval]
    linarith [hrel.2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
