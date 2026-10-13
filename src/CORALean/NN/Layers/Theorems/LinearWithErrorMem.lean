module

public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.NN.Layers.Operations.LinearWithError

@[expose] public section

/-!
# The linear layer with an error box, at every value of the error

What the layer encloses at *every* value of the error, not only its centre: `W x + c` for any
real `c` within what `E` denotes of `b` — CORA's `W h + b ⊕ E` read pointwise, and what the
reduction algorithms freeze a bias at.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Float Float.OfInterval Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.OfInterval S 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `W x + c` for any `c` within what `E` denotes of `b`. -/
theorem Layer.linearWithError_mem (W : Mat 𝕋 m n) {b : Vec 𝕋 m} {c : Vec ℝ m}
    {E : Interval (Vec 𝕋 m)} (hc : c - toRealVec b ∈ E.construct) (s : S n) {x : Vec ℝ n}
    (hx : x ∈ construct s) :
    toRealMat W *ᵥ x + c ∈
      construct ((Layer.linearWithError (S := S) W b E).enclose s) := by -- --- PROOF ---
  have hbox : toRealVec b + (c - toRealVec b) ∈ construct (Interval.plus (Interval.point b) E) :=
    Interval.plus_outer _ _ (Set.add_mem_add (Interval.mem_point b) hc)
  rw [add_sub_cancel] at hbox
  exact plus_outer _ _ (Set.add_mem_add
    (mtimes_outer W s (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (ofInterval_outer _ hbox))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
