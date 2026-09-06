import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.NN.Layers.Linear
import CORALean.NN.Theorems.PropagateOuter
import CORALean.NN.Theorems.SuffExplanationAbstract
import CORALean.NN.Theorems.SuffExplanation

/-!
# The transfer theorem's converse fails under its own hypothesis

`suffExplanation_of_abstract`'s converse fails even granting its containment
hypothesis [1, §4]: a sound abstraction can still be too loose to see a
separation the original network has. The witness keeps `nnAbs` a genuine
`Layer.linearWithError` [2] abstraction of `nn` — same weights and bias, an
error box centred at `0` so the two agree exactly — and makes the box wide
enough that the enclosed output ties, though the exact one never does. This
loss of precision is exactly why refinement exists.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
* [2] `CORALean.Real.Layer.linearWithError`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet OfInterval Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The constant `(0, 1)` network: class `1` always strictly wins. -/
def aux_suffExplanationConverseFails_nn : NeuralNetwork (fun n => Interval (Vec ℝ n)) 1 2 :=
  NeuralNetwork.ofLayer (Layer.linear (0 : Mat ℝ 2 1) (fun k => if k = 1 then (1 : ℝ) else 0))

/-- The symmetric `±1` error box: centred at `0`, wide enough to tie. -/
def aux_suffExplanationConverseFails_box : Interval (Vec ℝ 2) := ⟨fun _ => -1, fun _ => 1⟩

theorem aux_suffExplanationConverseFails_box_isNonempty :
    aux_suffExplanationConverseFails_box.IsNonempty := fun _ => by
  show (-1 : ℝ) ≤ 1
  norm_num

-- the committed error is the box's own centre, which is `0` since the box is symmetric
theorem aux_suffExplanationConverseFails_box_center :
    aux_suffExplanationConverseFails_box.center = 0 := by
  funext i
  show (2 : ℝ)⁻¹ * ((-1 : ℝ) + 1) = 0
  norm_num

/-- `nn`'s abstraction: the same weights and bias, over-approximated by the
`±1` box. -/
noncomputable def aux_suffExplanationConverseFails_nnAbs :
    NeuralNetwork (fun n => Interval (Vec ℝ n)) 1 2 :=
  NeuralNetwork.ofLayer (Layer.linearWithError (0 : Mat ℝ 2 1)
    (fun k => if k = 1 then (1 : ℝ) else 0) aux_suffExplanationConverseFails_box
    aux_suffExplanationConverseFails_box_isNonempty)

-- the box's error is committed at its own centre, `0`, so the exact networks agree
theorem aux_suffExplanationConverseFails_eval_eq (x' : Vec ℝ 1) :
    aux_suffExplanationConverseFails_nnAbs.eval x'
      = aux_suffExplanationConverseFails_nn.eval x' := by -- --- PROOF ---
  funext i
  show ((0 : Mat ℝ 2 1) *ᵥ x') i + (if i = 1 then (1 : ℝ) else 0)
      + aux_suffExplanationConverseFails_box.center i
      = ((0 : Mat ℝ 2 1) *ᵥ x') i + (if i = 1 then (1 : ℝ) else 0)
  rw [aux_suffExplanationConverseFails_box_center]
  simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- The converse of `suffExplanation_of_abstract` fails under its own
hypothesis: a sound abstraction (`hcontain`) of a sufficient `nn` need not be
abstractly sufficient for `nnAbs`. -/
theorem suffExplanation_of_abstract_converse_fails :
    ∃ (nn nnAbs : NeuralNetwork (fun n => Interval (Vec ℝ n)) 1 2) (x : Vec ℝ 1) (ε : ℝ)
      (E : Finset (Fin 1)) (l : Fin 2),
      nn.outputSet (ofInterval (S := fun n => Interval (Vec ℝ n)) (explainBox x ε E))
        ⊆ construct (nnAbs.propagate
          (ofInterval (S := fun n => Interval (Vec ℝ n)) (explainBox x ε E)))
      ∧ nn.IsSuffExplanation x ε E l
        ∧ ¬ nnAbs.IsSuffExplanationAbstract x ε E l := by -- --- PROOF ---
  refine ⟨aux_suffExplanationConverseFails_nn, aux_suffExplanationConverseFails_nnAbs,
    (fun _ => 0), 0, ∅, 1, ?_, ?_, ?_⟩
  · -- `nn` and `nnAbs` evaluate identically, so `nn`'s exact image lies in `nnAbs`'s enclosure
    rintro _ ⟨x', hx', rfl⟩
    rw [← aux_suffExplanationConverseFails_eval_eq]
    exact aux_suffExplanationConverseFails_nnAbs.propagate_outer _ x' hx'
  · -- `nn` never ties: the only rival is strictly behind
    intro x' _ j hj
    have heval : aux_suffExplanationConverseFails_nn.eval x'
        = fun k => if k = 1 then (1 : ℝ) else 0 := by
      funext i
      show ((0 : Mat ℝ 2 1) *ᵥ x') i + (if i = 1 then (1 : ℝ) else 0)
          = if i = 1 then (1 : ℝ) else 0
      simp
    rw [heval]
    simp [if_neg hj]
  · -- the box's slack lets class `0` catch class `1`, though the exact network never would
    intro hcontra
    set X := ofInterval (S := fun n => Interval (Vec ℝ n))
      (explainBox (fun _ => (0 : ℝ)) 0 (∅ : Finset (Fin 1))) with hX
    have hzero : ∀ i, (Interval.mtimes (0 : Mat ℝ 2 1) X).inf i = 0
        ∧ (Interval.mtimes (0 : Mat ℝ 2 1) X).sup i = 0 :=
      fun i => ⟨by simp [Interval.mtimes], by simp [Interval.mtimes]⟩
    have hi01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := fun i => match i with
      | 0 => Or.inl rfl
      | 1 => Or.inr rfl
    have hmem : (fun k => if k = 0 then (1 : ℝ) else 0) ∈
        construct (aux_suffExplanationConverseFails_nnAbs.propagate X) := by
      intro i
      -- the zero weights drop out, leaving the `±1` box around `nn`'s bias
      have hz := hzero i
      constructor
      · show (Interval.mtimes (0 : Mat ℝ 2 1) X).inf i +
            ((if i = 1 then (1 : ℝ) else 0) + aux_suffExplanationConverseFails_box.inf i)
            ≤ (if i = 0 then (1 : ℝ) else 0)
        rw [hz.1]
        rcases hi01 i with hi | hi <;> subst hi <;>
          norm_num [aux_suffExplanationConverseFails_box]
      · show (if i = 0 then (1 : ℝ) else 0) ≤
            (Interval.mtimes (0 : Mat ℝ 2 1) X).sup i +
              ((if i = 1 then (1 : ℝ) else 0) + aux_suffExplanationConverseFails_box.sup i)
        rw [hz.2]
        rcases hi01 i with hi | hi <;> subst hi <;>
          norm_num [aux_suffExplanationConverseFails_box]
    have h01 : (0 : Fin 2) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    exact (Set.disjoint_left.mp hcontra hmem) ⟨0, h01, by simp⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
