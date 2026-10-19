module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Theorems.ActivationOuterWhere

@[expose] public section

/-!
# What an activation layer encloses

`σ` coordinatewise, wherever the relaxation is sound for `σ`: `Layer.activation_outer_where` at
the trivial box condition.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


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
theorem Layer.activation_encloses {R : Relaxation 𝕋} (hR : R.Sound σ) :
    (Layer.activation (S := S) (n := n) R).Encloses (fun x i => σ (x i)) :=
  ⟨fun s x hx => Layer.activation_outer_where ⟨fun _ hl hu => hR.sound hl hu⟩ s x hx
    (P := fun _ _ => True) fun _ => trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
