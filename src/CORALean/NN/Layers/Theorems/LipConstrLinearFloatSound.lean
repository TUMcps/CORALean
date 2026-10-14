module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.NN.Layers.Operations.LipConstrLinearFloat
public import CORALean.NN.Layers.Theorems.LipConstrScaleFloatMem

@[expose] public section

/-!
# What the float Lipschitz-constrained linear layer encloses

The real layer `x ↦ N (W x + b)` at the weights, bias and `λ` the floats denote. The scaling
`N` lies in its box, so `N W` lies in the interval matrix `mtimes` runs at and `N b` in the
bias box. Needs `0 < λ`, which makes the box a bracket of `N`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Float Float.OfInterval Float.SoundFloatArithmetic
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes ℐ[𝕋] S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.lipConstrLinearFloat_sound (W : Mat 𝕋 m n) (b : Vec 𝕋 m) (lam : 𝕋)
    (hl : 0 < toReal lam) :
    (Layer.lipConstrLinearFloat (S := S) W b lam).Sound
      fun x i => Layer.lipConstrScale (toRealMat W) (toReal lam) i
        * (toRealMat W *ᵥ x + toRealVec b) i := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hN := Layer.lipConstrScaleFloat_mem W lam hl
  set N := Layer.lipConstrScale (toRealMat W) (toReal lam) with hNdef
  -- `N W` lies in the interval matrix `mtimes` runs at
  have hmat : Matrix.diagonal N * toRealMat W ∈
      (⟨fun i j => Interval.mulLo ((Layer.lipConstrScaleFloat W lam).inf i)
          ((Layer.lipConstrScaleFloat W lam).sup i) (W i j) (W i j),
        fun i j => Interval.mulHi ((Layer.lipConstrScaleFloat W lam).inf i)
          ((Layer.lipConstrScaleFloat W lam).sup i) (W i j) (W i j)⟩ :
        Interval (Mat 𝕋 m n)).construct := by
    refine Interval.mem_mat_iff.2 fun i j => ?_
    have := Interval.mul_between_corners (hN i).1 (hN i).2
      (le_refl (toReal (W i j))) (le_refl (toReal (W i j)))
    have e : (Matrix.diagonal N * toRealMat W) i j = N i * toReal (W i j) := by
      simp [Matrix.diagonal_mul, toRealMat]
    rw [e]
    exact this
  -- and `N b` in the bias box
  have hbias : (fun i => N i * toRealVec b i) ∈
      (⟨fun i => Interval.mulLo ((Layer.lipConstrScaleFloat W lam).inf i)
          ((Layer.lipConstrScaleFloat W lam).sup i) (b i) (b i),
        fun i => Interval.mulHi ((Layer.lipConstrScaleFloat W lam).inf i)
          ((Layer.lipConstrScaleFloat W lam).sup i) (b i) (b i)⟩ :
        Interval (Vec 𝕋 m)).construct := fun i =>
    Interval.mul_between_corners (hN i).1 (hN i).2 (le_refl (toReal (b i))) (le_refl (toReal (b i)))
  -- the layer's map is `(N W) x + N b`
  have key : (fun i => N i * (toRealMat W *ᵥ x + toRealVec b) i)
      = (Matrix.diagonal N * toRealMat W) *ᵥ x + fun i => N i * toRealVec b i := by
    funext i
    simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Pi.add_apply, mul_add]
  -- so both parts are enclosed by `mtimes_outer` and `plus_outer`
  show (fun i => N i * (toRealMat W *ᵥ x + toRealVec b) i) ∈ construct
    (plus (mtimes (𝕄 := ℐ[𝕋]) _ s) (ofInterval _))
  rw [key]
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer (𝕄 := ℐ[𝕋]) _ s
      (Set.mem_biUnion hmat (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hbias))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
