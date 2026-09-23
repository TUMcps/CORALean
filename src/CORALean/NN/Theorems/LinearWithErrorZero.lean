import CORALean.NN.Layers.Linear

/-!
# `Layer.linearWithError` degenerates to `Layer.linear`

At `E = Interval.point 0` the committed centre is `0` and the added box is a
point, so the two layers compute and enclose identically: a plain linear
layer is the error-free case of the adapted one, not a different construction.
That is [1, Eq. 2]'s initialization, `I'_k = [0, 0]`: a network adapted to carry the
error of merging denotes, before any merge, the network it was adapted from.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.OfInterval S] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.linearWithError_zero (W : Mat ℝ m n) (b : Vec ℝ m) :
    Real.Layer.linearWithError (S := S) W b (Real.Interval.point 0)
      = Real.Layer.linear (S := S) W b := by -- --- PROOF ---
  have henclose : (Real.Layer.linearWithError (S := S) W b (Real.Interval.point 0)).enclose
      = (Real.Layer.linear (S := S) W b).enclose := by
    funext s
    show plus (mtimes W s)
        (ofInterval (Real.Interval.plus (Real.Interval.point b) (Real.Interval.point 0)))
        = plus (mtimes W s) (ofInterval (Real.Interval.point b))
    -- a point box added to a point box is the point box of the sum
    have hbox : Real.Interval.plus (Real.Interval.point b) (Real.Interval.point (0 : Vec ℝ m))
        = Real.Interval.point b := by
      show (⟨b + 0, b + 0⟩ : Real.Interval (Vec ℝ m)) = ⟨b, b⟩
      rw [add_zero]
    rw [hbox]
  -- a layer is its `enclose` and nothing else
  exact congrArg Layer.mk henclose

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
