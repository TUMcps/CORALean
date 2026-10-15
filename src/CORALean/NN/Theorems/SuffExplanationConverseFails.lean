module

public import CORALean.ContSet.Interval.Float.Theorems.NonemptyHullIsNonempty
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Instances
public import CORALean.NN.Layers.Theorems.LinearSound
public import CORALean.NN.Layers.Theorems.LinearWithErrorSound
public import CORALean.NN.Theorems.EncloseOuter
public import CORALean.NN.Definitions.SuffExplanation
public import CORALean.NN.Definitions.SuffExplanationAbstract

@[expose] public section

/-!
# The transfer theorem's converse fails under its own hypothesis

`suffExplanation_of_abstract`'s converse fails even granting its containment
hypothesis, as [1, Sec. 4] itself says of its running example: "although every
abstract explanation is valid for the original network, the reverse is not
necessarily true". A sound abstraction can be too loose to see a separation the
original network has, which is exactly why refinement exists. The witness keeps
`nnAbs` a genuine `Layer.linearWithError` [2] abstraction of `nn` — same weights
and bias, an error box centered at `0` so the two agree exactly — and makes the
box wide enough that the enclosed output ties, though the exact one never does.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Layer.linearWithError`.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Real.OfInterval Matrix
open scoped CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The constant `(0, 1)` network: class `1` always strictly wins. -/
noncomputable def aux_suffExplanationConverseFails_nn :
    NeuralNetwork ℐ𝒱 1 2 :=
  NeuralNetwork.ofLayer (LinearLayer.mk (0 : Mat ℝ 2 1) (fun k => if k = 1 then (1 : ℝ) else 0))

/-- The symmetric `±1` error box: centered at `0`, wide enough to tie. -/
def aux_suffExplanationConverseFails_box : Float.Interval (Vec ℝ 2) := ⟨fun _ => -1, fun _ => 1⟩

-- the committed error is the center of the box the layer runs, the box itself, so `0`
theorem aux_suffExplanationConverseFails_box_center :
    aux_suffExplanationConverseFails_box.nonemptyHull.nominal.center = 0 := by
  funext i
  show (2 : ℝ)⁻¹ * ((-1 : ℝ) + max (-1) 1) = 0
  norm_num

/-- What both networks compute, which neither of them stores. -/
def aux_suffExplanationConverseFails_f : Vec ℝ 1 → Vec ℝ 2 :=
  fun x => (0 : Mat ℝ 2 1) *ᵥ x + fun k => if k = 1 then (1 : ℝ) else 0

theorem aux_suffExplanationConverseFails_nn_sound :
    aux_suffExplanationConverseFails_nn.Sound aux_suffExplanationConverseFails_f :=
  NeuralNetwork.ofLayer_sound (Layer.linear_sound _ _)

/-- `nn`'s abstraction: the same weights and bias, over-approximated by the
`±1` box. -/
noncomputable def aux_suffExplanationConverseFails_nnAbs :
    NeuralNetwork ℐ𝒱 1 2 :=
  NeuralNetwork.ofLayer (LinearWithErrorLayer.mk (0 : Mat ℝ 2 1)
    (fun k => if k = 1 then (1 : ℝ) else 0) aux_suffExplanationConverseFails_box)

-- the box's error is committed at its own center, `0`, so the exact networks agree
theorem aux_suffExplanationConverseFails_nnAbs_sound :
    aux_suffExplanationConverseFails_nnAbs.Sound
      aux_suffExplanationConverseFails_f := by -- --- PROOF ---
  refine (NeuralNetwork.ofLayer_sound (S := ℐ𝒱)
    (curr := LinearWithErrorLayer.mk (0 : Mat ℝ 2 1) (fun k => if k = 1 then (1 : ℝ) else 0)
      aux_suffExplanationConverseFails_box) (Layer.linearWithError_sound (0 : Mat ℝ 2 1)
    (fun k => if k = 1 then (1 : ℝ) else 0) aux_suffExplanationConverseFails_box.nonemptyHull
    aux_suffExplanationConverseFails_box.nonemptyHull_isNonempty)).congr fun x' => ?_
  funext i
  show ((0 : Mat ℝ 2 1) *ᵥ x') i + (if i = 1 then (1 : ℝ) else 0)
      = ((0 : Mat ℝ 2 1) *ᵥ x') i + (if i = 1 then (1 : ℝ) else 0)
        + aux_suffExplanationConverseFails_box.nonemptyHull.nominal.center i
  rw [aux_suffExplanationConverseFails_box_center]
  simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- The converse of `suffExplanation_of_abstract` fails under its own
hypothesis: a sound abstraction (`hcontain`) of a sufficient `nn` need not be
abstractly sufficient for `nnAbs`. -/
theorem suffExplanation_of_abstract_converse_fails :
    ∃ (nn nnAbs : NeuralNetwork ℐ𝒱 1 2) (f : Vec ℝ 1 → Vec ℝ 2)
      (x : Vec ℝ 1) (ε : ℝ) (E : Finset (Fin 1)) (l : Fin 2),
      nn.Sound f
      ∧ f '' construct (ofInterval (S := ℐ𝒱) (explainBox x ε E))
        ⊆ construct (nnAbs.enclose
          (ofInterval (S := ℐ𝒱) (explainBox x ε E)))
      ∧ IsSuffExplanation f x ε E l
        ∧ ¬ nnAbs.IsSuffExplanationAbstract x ε E l := by -- --- PROOF ---
  refine ⟨aux_suffExplanationConverseFails_nn, aux_suffExplanationConverseFails_nnAbs,
    aux_suffExplanationConverseFails_f, (fun _ => 0), 0, ∅, 1,
    aux_suffExplanationConverseFails_nn_sound, ?_, ?_, ?_⟩
  · -- both networks compute the same map, so `nn`'s exact image is inside the enclosure
    rintro _ ⟨x', hx', rfl⟩
    exact aux_suffExplanationConverseFails_nnAbs_sound.enclose_outer _ x' hx'
  · -- `nn` never ties: the only rival is strictly behind
    intro x' _ j hj
    have heval : aux_suffExplanationConverseFails_f x'
        = fun k => if k = 1 then (1 : ℝ) else 0 := by
      funext i
      show ((0 : Mat ℝ 2 1) *ᵥ x') i + (if i = 1 then (1 : ℝ) else 0)
          = if i = 1 then (1 : ℝ) else 0
      simp
    rw [heval]
    simp [if_neg hj]
  · -- the box's slack lets class `0` catch class `1`, though the exact network never would
    intro hcontra
    set X := ofInterval (S := ℐ𝒱)
      (explainBox (fun _ => (0 : ℝ)) 0 (∅ : Finset (Fin 1))) with hX
    have hzero : ∀ i, (Real.Interval.mtimes (0 : Mat ℝ 2 1) X).inf i = 0
        ∧ (Real.Interval.mtimes (0 : Mat ℝ 2 1) X).sup i = 0 :=
      fun i => ⟨by simp [Real.Interval.mtimes], by simp [Real.Interval.mtimes]⟩
    have hi01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i => match i with
      | 0 => Or.inl rfl
      | 1 => Or.inr rfl
    have hmem : (fun k => if k = 0 then (1 : ℝ) else 0) ∈
        construct (aux_suffExplanationConverseFails_nnAbs.enclose X) := by
      intro i
      -- the zero weights drop out, leaving the `±1` box around `nn`'s bias
      have hz := hzero i
      constructor
      · show (Real.Interval.mtimes (0 : Mat ℝ 2 1) X).inf i +
            ((if i = 1 then (1 : ℝ) else 0) + aux_suffExplanationConverseFails_box.inf i)
            ≤ (if i = 0 then (1 : ℝ) else 0)
        rw [hz.1]
        rcases hi01 i with hi | hi <;> subst hi <;>
          norm_num [aux_suffExplanationConverseFails_box]
      -- the upper end runs at the box's nonempty hull, the box itself here
      · show (if i = 0 then (1 : ℝ) else 0) ≤
            (Real.Interval.mtimes (0 : Mat ℝ 2 1) X).sup i +
              ((if i = 1 then (1 : ℝ) else 0)
                + max (aux_suffExplanationConverseFails_box.inf i)
                  (aux_suffExplanationConverseFails_box.sup i))
        rw [hz.2]
        rcases hi01 i with hi | hi <;> subst hi <;>
          norm_num [aux_suffExplanationConverseFails_box]
    have h01 : (0 : Fin 2) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    exact (Set.disjoint_left.mp hcontra hmem) ⟨0, h01, by simp⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
