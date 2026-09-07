import CORALean.NN.Layers.Linear

/-!
# `Layer.linearWithError` degenerates to `Layer.linear`

At `E = Interval.point 0` the committed centre is `0` and the added box is a
point, so the two layers compute and enclose identically: a plain linear
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

theorem Layer.linearWithError_zero (W : Mat ℝ m n) (b : Vec ℝ m) :
    Layer.linearWithError (S := S) W b (Interval.point 0)
      = Layer.linear (S := S) W b := by -- --- PROOF ---
  have henclose : (Layer.linearWithError (S := S) W b (Interval.point 0)).enclose
      = (Layer.linear (S := S) W b).enclose := by
    funext s
    show plus (mtimes W s) (ofInterval (Interval.plus (Interval.point b) (Interval.point 0)))
        = plus (mtimes W s) (ofInterval (Interval.point b))
    -- a point box added to a point box is the point box of the sum
    have hbox : Interval.plus (Interval.point b) (Interval.point (0 : Vec ℝ m))
        = Interval.point b := by
      show (⟨b + 0, b + 0⟩ : Interval (Vec ℝ m)) = ⟨b, b⟩
      rw [add_zero]
    rw [hbox]
  -- a layer is its `enclose` and nothing else
  exact congrArg Layer.mk henclose

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
