module

public import CORALean.NN.Definitions.VerifyResult
public import CORALean.NN.Operations.UnsafeInputConstraints
public import CORALean.ContSet.ConZonotope.Real.Operations.FourierMotzkinIter
public import CORALean.ContSet.Zonotope.Real.Operations.ZonotackFactors

@[expose] public section

/-!
# `SetBasedNet.verify`

[1, Alg. 1], CORA's `neuralNetwork/verify` with `'zonotack'` falsification and refinement: a queue
of input sets; each is enclosed (Prop. 1), verified by (8), falsified by the vertex (9) nearest
the unsafe set, else refined by Prop. 2 and split. The sets are zonotopes: a split piece
`X_i|_{[C; C_j] ≤ [d; d_j]}` is stored as its factor bounds of Prop. 3 rescaling `X_i`, as
[1, App. D] and CORA's `aux_refineInputSet` do, and an empty piece is dropped. The falsification
takes `-sign`, CORA's (`Zonotope.zonotackFactors`), not the printed `sign`. `fuel` bounds the sets
processed, CORA's `max_verif_iter`, at `UNKNOWN`; the split is a parameter (Sec. B).

## Inputs
* `N` – set-based network
* `Φ` – the network's function, to check a candidate
* `A` – unsafe-set matrix
* `b` – unsafe-set offset
* `split` – the split constraints `C_j β ≤ d_j` of each input set
* `iterFM` – passes of Prop. 3 per piece

## Output
* `VERIFIED`, `FALSIFIED(x̃)` or `UNKNOWN` for a queue of input sets and a budget

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

open Matrix

variable {n k p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One piece of [1, Alg. 1, l. 16]: `X|_{[C; C_j] ≤ [d; d_j]}` bounded by `iterFM` passes of
[1, Prop. 3] and stored as the rescaled `X`, `none` when the bounds are empty. -/
noncomputable def aux_piece (X : Zonotope (Vec ℝ n)) (Cd : Mat ℝ p X.h × Vec ℝ p)
    (s : Σ r : ℕ, Mat ℝ r X.h × Vec ℝ r) (iterFM : ℕ) : Option (Zonotope (Vec ℝ n)) :=
  -- 1. the refinement and the split constraints together, `[C; C_j] β ≤ [d; d_j]`
  let Call : Mat ℝ (p + s.1) X.h := Fin.append Cd.1 s.2.1
  let dall : Vec ℝ (p + s.1) := Fin.append Cd.2 s.2.2
  -- 2. the factor bounds `[β̲, β̄]` of the constrained hypercube (Prop. 3)
  let Bβ := ConZonotope.fourierMotzkinIter Call dall iterFM
  -- 3. an empty box holds no unsafe input: the piece is verified
  if ∃ j, Bβ.sup j < Bβ.inf j then none else
  -- 4. the box as a zonotope, `⟨c_x + G_x β_c, G_x Diag(β_r)⟩_Z`
  some ⟨X.h, X.c + ∑ j, ((Bβ.inf j + Bβ.sup j) / 2) • X.G j,
    fun j => ((Bβ.sup j - Bβ.inf j) / 2) • X.G j⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] on a queue of input sets, processing at most `fuel` of them. -/
noncomputable def SetBasedNet.verify (N : SetBasedNet n k) (Φ : Vec ℝ n → Vec ℝ k)
    (A : Mat ℝ p k) (b : Vec ℝ p)
    (split : (X : Zonotope (Vec ℝ n)) → List (Σ r : ℕ, Mat ℝ r X.h × Vec ℝ r)) (iterFM : ℕ) :
    ℕ → List (Zonotope (Vec ℝ n)) → SetBasedNet.VerifyResult n
  -- 22. the queue is empty: every input set is verified
  | _, [] => .verified
  | 0, _ :: _ => .unknown
  -- 5. `X_i ← Q.dequeue()`
  | fuel + 1, Xi :: Q =>
    -- 6. `Y_i ← enclose(Φ, X_i)` (Prop. 1)
    let Yi := N.forward Xi
    -- 7-8. `Y_i ∩ U = ∅` by (8): the input set is verified
    if ∃ i, b i < (A *ᵥ Yi.c) i - ∑ j, |(A *ᵥ Yi.G j) i| then
      N.verify Φ A b split iterFM fuel Q
    else
      -- 10. `x̃_i ← c_x + G_x β̃_i([q₀])`, `β̃_i` the vertex (9) for each row `i`
      let xs : List (Vec ℝ n) := List.ofFn fun i : Fin p =>
        Xi.c + ∑ j, Yi.zonotackFactors (A i) (Fin.castLE (N.le_forward_h Xi) j) • Xi.G j
      -- 11-13. `Φ(x̃_i) ∈ U`: `FALSIFIED(x̃_i)`
      match xs.find? fun x => decide (∀ i, (A *ᵥ Φ x) i ≤ b i) with
      | some x => .falsified x
      | none =>
        -- 15. the constraints `C`, `d` of Prop. 2
        let Cd := N.unsafeInputConstraints Xi A b
        -- 16. `X_i|_{C₁≤d₁}, …, X_i|_{C_ξ≤d_ξ}`, each as its box
        let pieces := (split Xi).filterMap fun s => aux_piece Xi Cd s iterFM
        -- 17. `Q.enqueue(…)`
        N.verify Φ A b split iterFM fuel (Q ++ pieces)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
