import CORALean.NN.Layers.Operations.Activation

/-!
# What an activation layer encloses

`σ` coordinatewise, wherever the relaxation is sound for `σ`. The proof splits `σ x` into the
chosen affine map, which `mtimes` carries, and the deviation from it, which `sound` bounds by
`offset ± error` coordinatewise and `subDown`/`addUp` widen outward into the box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Float Float.IntervalOuter Float.OfInterval Float.FloatOps
  Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `σ` coordinatewise is what the layer encloses, which is where `σ` first appears:
`Layer.activation` itself never sees it. -/
theorem Layer.activation_sound {R : Relaxation 𝕋} (hR : R.Sound σ) :
    (Layer.activation (S := S) (n := n) R).Sound (fun x i => σ (x i)) := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox := interval_outer s hx
  set J := interval s with hJ
  set A : Mat ℝ n n := Scalar.toRealMat (R.slopeMat J) with hA
  have hslope : ∀ i, (A *ᵥ x) i = toReal (R.slope (J.inf i) (J.sup i)) * x i := by
    intro i
    have hdiag : A = Matrix.diagonal (toRealVec fun i => R.slope (J.inf i) (J.sup i)) := by
      funext p q
      exact toReal_diagonalBlock _ p q
    rw [hdiag]
    exact Matrix.mulVec_diagonal _ _ i
  -- the deviation from the chosen affine map, which is what the box holds
  set d : Vec ℝ n := fun i => σ (x i) - (A *ᵥ x) i with hd
  have hsplit : (fun i => σ (x i)) = A *ᵥ x + d := by
    funext i
    show σ (x i) = (A *ᵥ x) i + d i
    rw [hd]
    ring
  -- and the deviation is inside the box, `sound` bounding it and the rounding widening it
  have hmem : d ∈ Interval.construct (R.box J) := by
    intro i
    have hlo : toReal (J.inf i) ≤ x i := (hbox i).1
    have hhi : x i ≤ toReal (J.sup i) := (hbox i).2
    have hrel := abs_le.mp (hR.sound hlo hhi)
    have hval : d i = σ (x i) - toReal (R.slope (J.inf i) (J.sup i)) * x i := by
      show σ (x i) - (A *ᵥ x) i = _
      rw [hslope i]
    -- `sound` is an absolute value, and `subDown`/`addUp` widen its two ends outward
    have hlow : toReal (subDown (R.offset (J.inf i) (J.sup i))
        (R.error (J.inf i) (J.sup i))) ≤ d i := by
      have h := subDown_le_sub (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))
      rw [hval]
      linarith [hrel.1]
    have hhigh : d i ≤ toReal (addUp (R.offset (J.inf i) (J.sup i))
        (R.error (J.inf i) (J.sup i))) := by
      have h := add_le_addUp (R.offset (J.inf i) (J.sup i)) (R.error (J.inf i) (J.sup i))
      rw [hval]
      linarith [hrel.2]
    exact ⟨hlow, hhigh⟩
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer _ s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hmem))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
