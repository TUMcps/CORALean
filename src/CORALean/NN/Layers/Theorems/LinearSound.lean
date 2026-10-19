module

public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.Linear

@[expose] public section

/-!
# What the linear layer encloses

The exact affine map the stored weights denote, `x ↦ W x + b` read into ℝ: `mtimes` carries
the weights over every point of the set and `plus` adds the bias's zero-width box. At `𝕋 := ℝ`
the reading is the identity and this is `W x + b` itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Float Float.OfInterval Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.linear_sound (W : Mat 𝕋 m n) (b : Vec 𝕋 m) :
    (Layer.linear (S := S) W b).Sound fun x => toRealMat W *ᵥ x + toRealVec b :=
  ⟨fun s _x hx => plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ (Interval.mem_point b)))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
