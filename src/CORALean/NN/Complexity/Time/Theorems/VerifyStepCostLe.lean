module

public import CORALean.NN.Complexity.Time.Operations.VerifyStepCost
public import CORALean.NN.Complexity.Time.Theorems.EvalCostLe
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ForwardCostLe
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An iteration of the set-based verification costs `O(κ q³ + ξ p q²)`

[1, Prop. 4] for the asserted `SetBasedNet.verifyStepCost`: at most
`(cNeuron + cEval + 21) κ Q³ + (60 + 2R + iterFM (17R + 19)) ξ p Q²` when `Q` bounds the output
generators and every width, the input's included, `p ≤ Q`, and every piece has at most `R` split
rows. The enclosure is `O(n_max² q κ)` (`SetBasedNet.forwardCost_le`), `O(κ q³)` with
`n_max ≤ q`; the `p` candidates each evaluate `Φ`, `O(p κ n_max²) ⊆ O(κ q³)` with `p ≤ q`; the test,
the candidates' factors and Prop. 2 are `O(p n_κ q)`, each piece `O((p + r) q²)` per pass of
Prop. 3.

## Inputs
* `cNeuron` – cost of the slope and errors of one neuron
* `cEval` – cost of one activation at one point
* `N` – bound on every width
* `Q` – bound on the output generators
* `n` – input width
* `k` – output width
* `net` – set-based network
* `h` – generators of the input set
* `p` – rows of the unsafe set
* `ξ` – pieces of the split
* `r` – rows of one piece's split constraints
* `R` – bound on `r`
* `iterFM` – passes of Prop. 3 per piece

## Hypotheses
* `hN` – `1 ≤ N`
* `hh` – `1 ≤ h`
* `hw` – every width is at most `N`
* `hq` – the output generators are at most `Q`
* `hNQ` – `N ≤ Q`
* `hp` – `1 ≤ p`
* `hpQ` – `p ≤ Q`
* `hξ` – `1 ≤ ξ`
* `hr` – `r ≤ R`

## Conclusion
* the iteration costs `O(κ Q³ + ξ p Q²)` with constants in `cNeuron`, `cEval`, `R`, `iterFM`

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
private theorem aux_in_le_maxWidth : ∀ {n k : ℕ} (net : SetBasedNet n k), n ≤ net.maxWidth
  | _, _, .output => le_rfl
  | _, _, .linear _ _ _ => le_max_left _ _
  | _, _, .nonlinear _ _ _ _ => le_max_left _ _

/-- The output width is one of the widths `maxWidth` ranges over. -/
private theorem aux_out_le_maxWidth : ∀ {n k : ℕ} (net : SetBasedNet n k), k ≤ net.maxWidth
  | _, _, .output => le_rfl
  | _, _, .linear _ _ tail => (aux_out_le_maxWidth tail).trans (le_max_right _ _)
  | _, _, .nonlinear _ _ _ tail => (aux_out_le_maxWidth tail).trans (le_max_right _ _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4]: an iteration costs `O(κ Q³ + ξ p Q²)` for widths and `p` at most `Q`. -/
theorem SetBasedNet.verifyStepCost_le (cNeuron cEval : Cost) {N Q n k : ℕ}
    (net : SetBasedNet n k) {h p ξ r R iterFM : ℕ} (hN : 1 ≤ N) (hh : 1 ≤ h)
    (hw : net.maxWidth ≤ N) (hq : h + net.neurons ≤ Q) (hNQ : N ≤ Q) (hp : 1 ≤ p)
    (hpQ : p ≤ Q) (hξ : 1 ≤ ξ) (hr : r ≤ R) : -- --- CONCL ---
    (net.verifyStepCost cNeuron cEval h p ξ r iterFM).ops ≤
      (cNeuron.ops + cEval.ops + 21) * (net.depth * (Q * Q * Q)) +
        (60 + 2 * R + iterFM * (17 * R + 19)) * (ξ * p * (Q * Q)) := by -- --- PROOF ---
  simp only [SetBasedNet.verifyStepCost, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  -- the sizes, all at most `Q`
  have hQ : 1 ≤ Q := hN.trans hNQ
  have hk : k ≤ Q := (aux_out_le_maxWidth net).trans (hw.trans hNQ)
  have hn : n ≤ Q := (aux_in_le_maxWidth net).trans (hw.trans hNQ)
  have hq' : h + net.neurons + 1 ≤ 2 * Q := by omega
  have hhQ : h ≤ Q := by omega
  -- the enclosure and the evaluations: `O(κ Q³)`
  have hF := SetBasedNet.forwardCost_le cNeuron hN net h hh hw hq
  have hF' : (cNeuron.ops + 17) * (N * N * Q) * net.depth ≤
      (cNeuron.ops + 17) * (net.depth * (Q * Q * Q)) := by
    rw [mul_assoc, mul_comm (N * N * Q)]
    gcongr
  have hE := SetBasedNet.evalCost_le cEval hN net hw
  have hE' : p * ((cEval.ops + 4) * (N * N) * net.depth) ≤
      (cEval.ops + 4) * (net.depth * (Q * Q * Q)) := by
    have : p * (N * N) ≤ Q * Q * Q := by
      calc p * (N * N) ≤ Q * (Q * Q) := by gcongr
        _ = Q * Q * Q := by ring
    calc p * ((cEval.ops + 4) * (N * N) * net.depth) =
        (cEval.ops + 4) * (net.depth * (p * (N * N))) := by ring
      _ ≤ (cEval.ops + 4) * (net.depth * (Q * Q * Q)) := by gcongr
  have hpE : p * (net.evalCost cEval).ops ≤ p * ((cEval.ops + 4) * (N * N) * net.depth) :=
    Nat.mul_le_mul_left p hE
  -- the test, the candidates, the checks' membership and Prop. 2: `O(p Q²)`
  have hpk : p * k ≤ p * Q := Nat.mul_le_mul_left p hk
  have hpq : p * (h + net.neurons) ≤ p * Q := Nat.mul_le_mul_left p hq
  have hpQQ : p * Q ≤ p * (Q * Q) := Nat.mul_le_mul_left p (Nat.le_mul_of_pos_left Q hQ)
  have hp1 : p ≤ p * Q := Nat.le_mul_of_pos_right p hQ
  have hrow : (h + net.neurons + 1) * (2 * (p * k) + p) ≤ 6 * (p * (Q * Q)) := by
    calc (h + net.neurons + 1) * (2 * (p * k) + p) ≤ (2 * Q) * (3 * (p * Q)) := by
          gcongr
          omega
      _ = 6 * (p * (Q * Q)) := by ring
  have hQQ : Q ≤ Q * Q := Nat.le_mul_of_pos_left Q hQ
  -- the candidates: `p (h (2k + 2) + 2nh + 2n) ≤ 10 p Q²`
  have hcand : p * (h * (2 * k + 2) + (2 * (n * h) + n) + n) ≤ 10 * (p * (Q * Q)) := by
    have h1 : h * (2 * k + 2) + (2 * (n * h) + n) + n ≤ 10 * (Q * Q) := by
      have hhk : h * k ≤ Q * Q := Nat.mul_le_mul hhQ hk
      have hnh : n * h ≤ Q * Q := Nat.mul_le_mul hn hhQ
      have e : h * (2 * k + 2) = 2 * (h * k) + 2 * h := by ring
      rw [e]
      omega
    calc p * (h * (2 * k + 2) + (2 * (n * h) + n) + n) ≤ p * (10 * (Q * Q)) := by gcongr
      _ = 10 * (p * (Q * Q)) := by ring
  -- the membership tests of the candidates: `p (2pk + 2p) ≤ 4 p Q²`
  have hmem : p * (2 * (p * k) + p + p) ≤ 4 * (p * (Q * Q)) := by
    have h1 : 2 * (p * k) + p + p ≤ 4 * (Q * Q) := by
      have := Nat.mul_le_mul hpQ hk
      omega
    calc p * (2 * (p * k) + p + p) ≤ p * (4 * (Q * Q)) := by gcongr
      _ = 4 * (p * (Q * Q)) := by ring
  -- a piece: `O((p + r) Q²)` per pass, `p + r ≤ p (R + 1)`
  have hpr : p + r ≤ p * (R + 1) := by
    have : r ≤ p * R := hr.trans (Nat.le_mul_of_pos_left R hp)
    rw [Nat.mul_succ]
    omega
  have hpQ2 : p * Q ≤ p * (Q * Q) := Nat.mul_le_mul_left p hQQ
  have hpiece : (p + r) * (h + 1) + iterFM * ((p + r) * h * (4 * h + 13) + 2 * h) + h +
      (2 * (n * h) + n) + (n + 3 * h) + h * (n + 2) ≤
      (14 + 2 * R + iterFM * (17 * R + 19)) * (p * (Q * Q)) := by
    have h1 : (p + r) * (h + 1) ≤ 2 * (R + 1) * (p * (Q * Q)) := by
      calc (p + r) * (h + 1) ≤ p * (R + 1) * (2 * Q) := by gcongr; omega
        _ = 2 * (R + 1) * (p * Q) := by ring
        _ ≤ 2 * (R + 1) * (p * (Q * Q)) := by gcongr
    -- one pass of Prop. 3 at `p + r` rows
    have h2 : (p + r) * h * (4 * h + 13) + 2 * h ≤ (17 * R + 19) * (p * (Q * Q)) := by
      have h4 : 4 * h + 13 ≤ 17 * Q := by omega
      have h5 : (p + r) * h * (4 * h + 13) ≤ 17 * (R + 1) * (p * (Q * Q)) := by
        calc (p + r) * h * (4 * h + 13) ≤ p * (R + 1) * Q * (17 * Q) := by gcongr
          _ = 17 * (R + 1) * (p * (Q * Q)) := by ring
      have h6 : 2 * h ≤ 2 * (p * (Q * Q)) := by
        have : h ≤ p * (Q * Q) :=
          hhQ.trans (hQQ.trans (Nat.le_mul_of_pos_left (Q * Q) hp))
        omega
      calc (p + r) * h * (4 * h + 13) + 2 * h ≤
          17 * (R + 1) * (p * (Q * Q)) + 2 * (p * (Q * Q)) := by omega
        _ = (17 * R + 19) * (p * (Q * Q)) := by ring
    -- the emptiness test and the rescaled zonotope
    have h3 : h + (2 * (n * h) + n) + (n + 3 * h) + h * (n + 2) ≤ 12 * (p * (Q * Q)) := by
      have hnh : n * h ≤ Q * Q := Nat.mul_le_mul hn hhQ
      have hhn : h * n ≤ Q * Q := Nat.mul_le_mul hhQ hn
      have hQp : Q * Q ≤ p * (Q * Q) := Nat.le_mul_of_pos_left (Q * Q) hp
      have e : h * (n + 2) = h * n + 2 * h := by ring
      rw [e]
      omega
    have h6 := Nat.mul_le_mul_left iterFM h2
    have e : (14 + 2 * R + iterFM * (17 * R + 19)) * (p * (Q * Q)) =
        2 * (R + 1) * (p * (Q * Q)) + iterFM * ((17 * R + 19) * (p * (Q * Q))) +
          12 * (p * (Q * Q)) := by ring
    rw [e]
    omega
  have hpiece' := Nat.mul_le_mul_left ξ hpiece
  -- the queue, and every `O(p Q²)` term at most `ξ p Q²`
  have hξp : p * (Q * Q) ≤ ξ * p * (Q * Q) := by
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ hξ
  have hqueue : ξ + 1 ≤ 2 * (ξ * p * (Q * Q)) := by
    have : ξ ≤ ξ * p * (Q * Q) := by
      rw [mul_assoc]
      exact Nat.le_mul_of_pos_right ξ (Nat.mul_pos hp (Nat.mul_pos hQ hQ))
    omega
  -- `ξ` pieces, and the sum of all bounds
  have hξpiece : ξ * ((14 + 2 * R + iterFM * (17 * R + 19)) * (p * (Q * Q))) =
      (14 + 2 * R + iterFM * (17 * R + 19)) * (ξ * p * (Q * Q)) := by ring
  rw [hξpiece] at hpiece'
  have hsum : (cNeuron.ops + cEval.ops + 21) * (net.depth * (Q * Q * Q)) =
      (cNeuron.ops + 17) * (net.depth * (Q * Q * Q)) +
        (cEval.ops + 4) * (net.depth * (Q * Q * Q)) := by ring
  have hsum2 : (60 + 2 * R + iterFM * (17 * R + 19)) * (ξ * p * (Q * Q)) =
      (14 + 2 * R + iterFM * (17 * R + 19)) * (ξ * p * (Q * Q)) + 46 * (ξ * p * (Q * Q)) := by
    ring
  -- the checks split into `Φ`'s evaluations and the membership tests
  have hchk : p * ((net.evalCost cEval).ops + (2 * (p * k) + p) + p) =
      p * (net.evalCost cEval).ops + p * (2 * (p * k) + p + p) := by ring
  rw [hsum, hsum2, hchk]
  have hc : (h + net.neurons + 1) * (2 * (p * k) + p) + (2 * (p * (h + net.neurons)) + 2 * p)
      ≤ 10 * (p * (Q * Q)) := by omega
  have hd : (h + net.neurons + 1) * (2 * (p * k) + p) + (3 * (p * (h + net.neurons)) + 2 * p)
      ≤ 11 * (p * (Q * Q)) := by omega
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
