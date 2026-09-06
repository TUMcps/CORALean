import CORALean.NN.Layers.Linear

/-!
# `Layer.linearWithError` degenerates to `Layer.linear`

At `E = Interval.point 0` the committed centre is `0` and the added box is a
point, so the two layers compute and propagate identically: a plain linear
layer is the error-free case of the adapted one, not a different construction.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.linearWithError_zero (W : Mat ℝ m n) (b : Vec ℝ m)
    (hE : (Interval.point (0 : Vec ℝ m)).IsNonempty) :
    Layer.linearWithError
      (S := S) W b (Interval.point 0) hE = Layer.linear (S := S) W b := by -- --- PROOF ---
  -- the committed centre at a point interval is the point itself
  have hcenter : (Interval.point (0 : Vec ℝ m)).center = 0 := by
    show (2:ℝ)⁻¹ • ((0 : Vec ℝ m) + 0) = 0
    rw [add_zero, smul_zero]
  have heval : (Layer.linearWithError (S := S) W b (Interval.point 0) hE).eval
      = (Layer.linear (S := S) W b).eval := by
    funext x
    show W *ᵥ x + b + (Interval.point (0 : Vec ℝ m)).center = W *ᵥ x + b
    rw [hcenter, add_zero]
  have hpropagate : (Layer.linearWithError (S := S) W b (Interval.point 0) hE).propagate
      = (Layer.linear (S := S) W b).propagate := by
    funext s
    show plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) (Interval.point 0)))
        = plus (mtimes W s) (ofInterval (Interval.point b))
    have hbox : Interval.plus (Interval.point b) (Interval.point (0 : Vec ℝ m))
        = Interval.point b := by
      show (⟨b + 0, b + 0⟩ : Interval (Vec ℝ m)) = ⟨b, b⟩
      rw [add_zero]
    rw [hbox]
  -- `eval` and `propagate` agree, and the soundness field is a proposition
  have key : ∀ (L₁ L₂ : Layer S n m), L₁.eval = L₂.eval → L₁.propagate = L₂.propagate →
      L₁ = L₂ := by
    rintro ⟨e₁, p₁, o₁⟩ ⟨e₂, p₂, o₂⟩ rfl rfl
    rfl
  exact key _ _ heval hpropagate

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
