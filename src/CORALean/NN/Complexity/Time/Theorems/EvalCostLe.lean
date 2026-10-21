module

public import CORALean.NN.Complexity.Time.Operations.EvalCost
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetDepth
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetMaxWidth
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Evaluating a network costs `O(n_max² κ)`

The asserted `SetBasedNet.evalCost` is at most `(cEval + 4) N² κ` for `N ≥ 1` at least every
width of the network, the input's included: a linear layer `W h + b` costs `2 m n + 2 m ≤ 4 N²`,
an activation `n · cEval ≤ N² cEval`. This is the check of a candidate in [1, Prop. 4]'s proof,
`O(κ q²)` there with `n_max ≤ q`.

## Inputs
* `cEval` – cost of one activation at one neuron
* `N` – bound on every width
* `n` – input width
* `k` – output width
* `net` – set-based network

## Hypotheses
* `hN` – `1 ≤ N`
* `hw` – every width is at most `N`

## Conclusion
* the evaluation costs at most `(cEval + 4) N² κ`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The input width is one of the widths `maxWidth` ranges over. -/
theorem aux_le_maxWidth : ∀ {n k : ℕ} (net : SetBasedNet n k), n ≤ net.maxWidth
  | _, _, .output => le_rfl
  | _, _, .linear _ _ _ => le_max_left _ _
  | _, _, .nonlinear _ _ _ _ => le_max_left _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- Evaluating the network at a point costs at most `(cEval + 4) N² κ`. -/
theorem SetBasedNet.evalCost_le (cEval : Cost) {N : ℕ} (hN : 1 ≤ N) {n k : ℕ}
    (net : SetBasedNet n k) (hw : net.maxWidth ≤ N) : -- --- CONCL ---
    (net.evalCost cEval).ops ≤ (cEval.ops + 4) * (N * N) * net.depth := by -- --- PROOF ---
  induction net with
  | output => simp [SetBasedNet.evalCost]
  | @linear n m k W b tail ih =>
    -- `2 m n + 2 m ≤ 4 N²` for the layer, the tail by induction
    have hw' : max n tail.maxWidth ≤ N := hw
    have htail := ih (le_of_max_le_right hw')
    have hm : m ≤ N := (aux_le_maxWidth tail).trans (le_of_max_le_right hw')
    have hn : n ≤ N := le_of_max_le_left hw'
    show (Cost.matVec m n + ⟨m⟩ + tail.evalCost cEval).ops ≤
      (cEval.ops + 4) * (N * N) * (tail.depth + 1)
    simp only [Cost.ops_add, Cost.matVec]
    have hmn : m * n ≤ N * N := Nat.mul_le_mul hm hn
    have hmN : m ≤ N * N := hm.trans (Nat.le_mul_of_pos_left N hN)
    nlinarith
  | @nonlinear n k me eLo eUp tail ih =>
    -- `n · cEval ≤ N² cEval` for the layer
    have hw' : max n tail.maxWidth ≤ N := hw
    have htail := ih (le_of_max_le_right hw')
    have hn : n ≤ N * N := (le_of_max_le_left hw').trans (Nat.le_mul_of_pos_left N hN)
    show (n • cEval + tail.evalCost cEval).ops ≤ (cEval.ops + 4) * (N * N) * (tail.depth + 1)
    simp only [Cost.ops_add, Cost.ops_smul]
    have := Nat.mul_le_mul_right cEval.ops hn
    nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
