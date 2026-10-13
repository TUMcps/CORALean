import CORALean.NN.Layers.Operations.Exp
import CORALean.NN.Layers.Theorems.ActivationOuterWhere
import CORALean.NN.Layers.Theorems.ExpRelaxationSound

/-!
# What the exponential layer encloses

`Real.exp` coordinatewise, for every point of a set whose box has its right ends under `2ᵏ/2`.
The hypothesis is the cost of a machine upper bound on `exp`, which no format has everywhere.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.exp_outer (k : ℕ) (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s)
    (hs : ∀ i, toReal ((Float.IntervalOuter.interval s).sup i) ≤ 2 ^ k / 2) :
    (fun i => Real.exp (x i)) ∈ construct ((Layer.exp (𝕋 := 𝕋) (S := S) (n := n) k).enclose s) :=
  Layer.activation_outer_where (expRelaxation_sound k) s x hx hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
