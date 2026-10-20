module

public import CORALean.NN.Graph.Operations.GcnShared

@[expose] public section

/-!
# A chain of message-passing steps at one uncertain graph

`gcnSteps` iterates `gcnShared` at *one* `P`, so every step pairs over the factor set the previous
one preserved and the edge weighing a message at the first step is the same factor at the last.
Composing `gcnUncertain` instead would pad a fresh copy of the edge factors onto each result and let
one edge take unrelated values at two steps — the dependency this representation keeps.

The feature width `F` is fixed across steps, so the chain is an ordinary recursion rather than a
dependent one.

## Inputs
* `N` – number of nodes
* `F` – feature width
* `P` – polynomial zonotope of the graph

## Output
* polynomial zonotope after the chain of steps
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` message-passing steps at one uncertain graph, weights applied in order,
the factor set preserved throughout. -/
def GNN.gcnSteps {N F : ℕ} (P : PolyZonotope (Mat ℝ N N)) :
    ∀ (L : ℕ), (Fin L → Mat ℝ F F) → (H : PolyZonotope (Mat ℝ N F)) → P.p = H.p →
      PolyZonotope (Mat ℝ N F)
  | 0, _, H, _ => H
  | L + 1, W, H, hp =>
      GNN.gcnSteps P L (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
