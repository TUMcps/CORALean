module

public import CORALean.NN.Complexity.Time.Operations.EvalCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ForwardCost
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetNeurons

@[expose] public section

/-!
# `SetBasedNet.verifyStepCost`

Asserted, not proved, as [1, Prop. 4]'s proof counts it and as `SetBasedNet.verify` processes one
input set with `h` generators: the enclosure (`SetBasedNet.forwardCost`), the test (8) on the
`q ≤ h + Σₖ nₖ` output generators, a candidate (9) and a check per row of `A` (`p` of them), the
constraints of Prop. 2, and per piece of the split (`ξ` of them, at most `r` rows each) the rows,
`iterFM` passes of Prop. 3 (each row and factor isolated by two masked dot products), the
emptiness test and the rescaled zonotope. The queue operations cost a constant each, as [1]
reads Knuth's queue; `SetBasedNet.verify` holds the queue as a list.

## Inputs
* `cNeuron` – cost of the slope and errors of one neuron
* `cEval` – cost of one activation at one point
* `n` – input width
* `k` – output width
* `net` – set-based network
* `h` – generators of the input set
* `p` – rows of the unsafe set
* `ξ` – pieces of the split
* `r` – rows of one piece's split constraints
* `iterFM` – passes of Prop. 3 per piece

## Output
* cost of one iteration of [1, Alg. 1]

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What one iteration of [1, Alg. 1] costs on an input set with `h` generators. -/
def SetBasedNet.verifyStepCost (cNeuron cEval : Cost) {n k : ℕ} (net : SetBasedNet n k)
    (h p ξ r iterFM : ℕ) : Cost :=
  -- the output enclosure has at most `q` generators
  let q := h + net.neurons
  -- 6. `Y_i ← enclose(Φ, X_i)`
  let enclose := net.forwardCost cNeuron h
  -- 7. (8): `A c_y`, `A G_y`, `|A(i,·) G_y| 1` and one comparison per row
  let check := (q + 1) • Cost.matVec p k + ⟨2 * (p * q) + 2 * p⟩
  -- 10. per row, the factors `-sign(A(i,·) G_y(·,j))` of the input's `h` and `c_x + G_x β̃`
  let candidates := p • (h • (⟨2 * k + 2⟩ : Cost) + Cost.matVec n h + ⟨n⟩)
  -- 11-12. `Φ(x̃_i)` and `Φ(x̃_i) ∈ U`, per row
  let checks := p • (net.evalCost cEval + Cost.matVec p k + ⟨p⟩)
  -- 15. `C := A G_y(·,[q₀])` and `d := b - A c_y + |A G_y(·,[q_κ]∖[q₀])| 1`
  let constraints := (q + 1) • Cost.matVec p k + ⟨3 * (p * q) + 2 * p⟩
  -- 16. a pass of Prop. 3 at `p + r` rows: `C⁺`, `C⁻`, every `C̲(i,j)`, the `max` and `min`
  let pass : Cost := ⟨(p + r) * h * (4 * h + 13) + 2 * h⟩
  -- 16. a piece: its rows, the passes, the emptiness test and `⟨c_x + G_x β_c, G_x Diag(β_r)⟩_Z`
  let piece : Cost := ⟨(p + r) * (h + 1)⟩ + iterFM • pass + ⟨h⟩ + Cost.matVec n h +
    ⟨n + 3 * h⟩ + ⟨h * (n + 2)⟩
  -- 5, 17. `dequeue` and the `ξ` calls of `enqueue`
  let queue : Cost := ⟨ξ + 1⟩
  enclose + check + candidates + checks + constraints + ξ • piece + queue

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
