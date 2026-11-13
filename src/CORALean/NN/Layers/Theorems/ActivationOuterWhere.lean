module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Theorems.ActivationDeviationMem
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# What an activation layer encloses where its relaxation is sound

`σ` coordinatewise, wherever the relaxation is sound for `σ` on the box. The proof splits `σ x`
into the
chosen affine map, which `mtimes` carries, and the deviation from it, which `sound` bounds by
`offset ± error` coordinatewise and `subDown`/`addUp` widen outward into the box.

## Inputs
* `R` – relaxation of the activation
* `P` – condition on the input box
* `s` – input set
* `x` – point of the input set

## Hypotheses
* `hR` – relaxation is sound where the condition holds
* `hx` – point lies in the input set
* `hP` – every coordinate's box satisfies the condition

## Conclusion
* the activation of the point lies in the layer's output set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet ContSetLike Plus Mtimes Float Float.IntervalOuter Float.OfInterval
open Float.FloatOps
  Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `σ` coordinatewise lands in the layer's output at every point of a set whose box the
relaxation is sound on: the proof of `Layer.activation_encloses`, which asks of the box nothing. -/
theorem Layer.activation_outer_where {R : Relaxation 𝕋} {P : 𝕋 → 𝕋 → Prop}
    (hR : R.EnclosesWhere σ P) (s : S n) (x : Vec ℝ n) (hx : x ∈ toSet s)
    (hP : ∀ i, P ((interval s).inf i) ((interval s).sup i)) : -- --- CONCL ---
    (fun i => σ (x i)) ∈
      toSet ((Layer.activation (S := S) (n := n) R).enclose s) := by -- --- PROOF ---
  have hbox := interval_outer s hx
  set J := interval s with hJ
  set A : Mat ℝ n n := Scalar.toRealMat (R.step_slopeMat J) with hA
  -- the deviation from the chosen affine map, which is what the box holds
  set d : Vec ℝ n := fun i => σ (x i) - (A *ᵥ x) i with hd
  have hsplit : (fun i => σ (x i)) = A *ᵥ x + d := by
    funext i
    show σ (x i) = (A *ᵥ x) i + d i
    rw [hd]
    ring
  have hmem : d ∈ Interval.toSet (R.box J) := Relaxation.deviation_mem_box hR hbox hP
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer _ s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hmem))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
