module

public import CORALean.Global.Float.Instances.Real.Theorems.Basic
public import CORALean.NN.Definitions.Reduction
public import CORALean.NN.Theorems.NeuronMergingOuter

@[expose] public section

/-!
# `ReducesAt` is sound

Induction on the derivation. `nil`: `eval` is the identity, so `image` is `construct s` itself.
`keep`: `hg.enclose_outer` moves the point past the layer, then the hypothesis at that set. `merge`:
`neuronMerging_sandwich_outer` moves it past the sandwich, then the hypothesis at that set;
`image_eq_eval_image` reopens each of those sets to a point. `widen`: `linearWithError_mem`, the
bias being one value of the box. `freeze`: the survivors pass the trimmed layers as in `merge`, and
the bucket's own value `w` is the one the hypothesis is read at, layer `k+1`'s sum splitting along
the partition exactly as it does there.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the original network's image lies in the reduced network's enclosure
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever layers of `nn` were reduced to reach `nn'`, the original network's image lies
in the enclosure `nn'.enclose s` builds. -/
theorem NeuralNetwork.reducesAt_outer : -- --- CONCL ---
    ∀ {n m : ℕ} {s : S n} {nn nn' : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m},
      NeuralNetwork.ReducesAt s nn nn' f → f '' construct s ⊆ construct (nn'.enclose s)
  | _, _, s, _, _, _, .nil _ hid => by
      rintro _ ⟨x, hx, rfl⟩
      rw [hid x]
      exact hx
  | _, _, s, _, _, _, .keep (inst := _) _ curr hg hcomp h => by
      rintro _ ⟨x, hx, rfl⟩
      rw [hcomp x]
      exact reducesAt_outer h ⟨_, hg.enclose_outer s x hx, rfl⟩
  | _, _, s, _, _, _, .merge _ part W0 b0 R hR W1 b1 Y hY hcomp h => by
      rintro _ ⟨x, hx, rfl⟩
      have hsand := neuronMerging_sandwich_outer part W0 b0 R hR W1 b1 Y s hY ⟨x, hx, rfl⟩
      rw [hcomp x]
      exact reducesAt_outer h ⟨_, hsand, rfl⟩
  | _, _, s, _, _, _, .widen _ W c b E hc hcomp h => by
      rintro _ ⟨x, hx, rfl⟩
      rw [hcomp x]
      -- the layer runs the box's nonempty hull, which holds the box
      have hE := Float.Interval.construct_subset_nonemptyHull _ hc
      exact reducesAt_outer h ⟨_, Layer.linearWithError_mem W hE s hx, rfl⟩
  | _, _, s, _, _, _, .freeze (σ := σ) _ part W0 c0 b0 E0 hc0 R hR W1 c1 Y hY hcomp h => by
      rintro _ ⟨x, hx, rfl⟩
      set v : Vec ℝ _ := fun i => σ ((W0 *ᵥ x + c0) i) with hv
      -- the survivors pass the trimmed layer `k-1`, their error a restriction of `E0`
      have hrow : (W0.submatrix part.left id) *ᵥ x + c0 ∘ part.left
          = (W0 *ᵥ x + c0) ∘ part.left :=
        funext fun i => by simp [Matrix.mulVec, Matrix.submatrix_apply, dotProduct]
      have hc : c0 ∘ part.left - b0 ∘ part.left
          ∈ construct (⟨E0.inf ∘ part.left, E0.sup ∘ part.left⟩ : Float.Interval (Vec ℝ _)) :=
        fun i => hc0 (part.left i)
      have hA1 := Layer.linearWithError_mem (S := S) (W0.submatrix part.left id)
        (Float.Interval.construct_subset_nonemptyHull _ hc) s hx
      rw [Float.toRealMat_real, hrow] at hA1
      have hA2 := (Layer.activation_encloses (S := S) hR).enclose_outer _ _ hA1
      -- the bucket is frozen at its own value, which its bounds admit
      have hw : v ∘ part.right
          ∈ construct (⟨Y.inf ∘ part.right, Y.sup ∘ part.right⟩ : Float.Interval (Vec ℝ _)) :=
        fun i => hY x hx (part.right i)
      -- layer `k+1`'s dot product splits along the survivors and the bucket
      have hval : W1 *ᵥ v + c1 = (W1.submatrix id part.left) *ᵥ (v ∘ part.left)
          + (c1 + (W1.submatrix id part.right) *ᵥ (v ∘ part.right)) := by
        rw [part.mulVec_split₂ W1 v]
        abel
      rw [hcomp x, hval]
      exact reducesAt_outer (h _ hw) ⟨v ∘ part.left, hA2, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
