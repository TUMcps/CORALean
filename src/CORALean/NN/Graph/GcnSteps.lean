import CORALean.NN.Graph.ConvUncertain

/-!
# A chain of message-passing steps at one uncertain graph

`gcnSteps` iterates `gcnShared` at *one* `P`, so every step pairs over the
factor set the previous one preserved and the edge weighing a message at the
first step is the same factor at the last. Composing `gcnUncertain` instead
would pad a fresh copy of the edge factors onto each result and let one edge
take unrelated values at two steps — the dependency this representation is
here to keep.

`evalSteps` is what the chain computes, written at a *matrix* rather than at a
set and a factor vector: the graph's own iteration is then literally the same
function, which is what the soundness statement needs.

The feature width `F` is fixed across steps, deliberately, so the chain is an
ordinary recursion rather than a dependent one. A network changing width needs
the dependent chain `NeuralNetwork` already is; nothing here would change but
the bookkeeping — the dependency is about the factors, not the widths.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

/-- `L` message-passing steps at a fixed matrix `Pm`, weights applied in order:
the value the chain below computes at one factor vector. -/
def GNN.evalSteps {N F : ℕ} (Pm : Mat ℝ N N) :
    ∀ (L : ℕ), (Fin L → Mat ℝ F F) → Mat ℝ N F → Mat ℝ N F
  | 0, _, h => h
  | L + 1, W, h => GNN.evalSteps Pm L (fun i => W i.succ) (Pm * h * W 0)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` message-passing steps at one uncertain graph, weights applied in order,
the factor set preserved throughout. -/
def GNN.gcnSteps {N F : ℕ} (P : PolyZonotope (Mat ℝ N N)) :
    ∀ (L : ℕ), (Fin L → Mat ℝ F F) → (H : PolyZonotope (Mat ℝ N F)) → P.p = H.p →
      PolyZonotope (Mat ℝ N F)
  | 0, _, H, _ => H
  | L + 1, W, H, hp =>
      GNN.gcnSteps P L (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl

/-- Every set in the chain carries `P`'s factors: the base case through `hp`, and
every step through `gcnShared_p`. -/
theorem GNN.gcnSteps_p {N F : ℕ} (P : PolyZonotope (Mat ℝ N N)) (L : ℕ) :
    ∀ (W : Fin L → Mat ℝ F F) (H : PolyZonotope (Mat ℝ N F)) (hp : P.p = H.p),
      (GNN.gcnSteps P L W H hp).p = P.p := by
  induction L with
  | zero => exact fun _ _ hp => hp.symm
  | succ L ih => exact fun W H hp => ih (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
