module

public import CORALean.NN.Operations.RefinableNetworkEval
public import CORALean.NN.Operations.RefinementLipschitz

@[expose] public section

/-!
# A chain of Lipschitz layers is Lipschitz

The induction `RefinementConvergent`'s tail hypothesis is discharged by: the
head's constant times the tail's, which is `LipschitzWith.comp` read along the
chain. The empty network is the identity, so its constant is `1` rather than
`0` — a network of no layers still moves its input.

The constant is existential and not computed. A product of layer bounds is the
worst case and every use here only needs *some* bound, so naming it would
commit the statement to a number no caller reads.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.exists_lipschitzWith_eval :
    ∀ {n m : ℕ} (rn : RefinableNetwork S n m), rn.LipschitzLayers →
      ∃ K : NNReal, LipschitzWith K rn.eval
  | _, _, .nil, _ => ⟨1, LipschitzWith.id⟩
  | _, _, .cons L rest, h => by
    obtain ⟨⟨K, hK⟩, hrest⟩ := h
    -- the tail's constant multiplies the head's, composition being the only step
    obtain ⟨K', hK'⟩ := rest.exists_lipschitzWith_eval hrest
    exact ⟨K' * K, hK'.comp hK⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
