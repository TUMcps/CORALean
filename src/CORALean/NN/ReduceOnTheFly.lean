import CORALean.ContSet.Interval.Real.Operations.Mtimes
import CORALean.ContSet.Interval.Real.Operations.Plus
import CORALean.NN.BucketTolerance
import CORALean.NN.ReducibleNetwork

/-!
# [1, Alg. 2]: reducing a network on the fly

[1, Alg. 2] walks the nonlinear layers `k = 2, 4, …, κ`. Before each but the last it looks
ahead: the set `H_{k-2}` reaching layer `k-1` is boxed, pushed through `L̂_{k-1}` and `L_k` in
interval arithmetic to bounds `I_k`, [1, Alg. 1] picks the buckets at `I_k`, and [1, Prop. 4]
merges them out of layers `k-1`, `k`, `k+1`. Only then does the set itself pass the two reduced
layers. What comes back is the reduced network `Φ̂_ρ` and the output set `Y = H_κ`.

`reduceOnTheFlyFrom` is the loop from one `k` on, `L̂_{k-1}` in hand, recursing on the layers
after `k + 1`; the case split on them is line 3's `k < κ`. `mergeRows` and `mergeCols` are line
7's [1, Prop. 4] at layers `k-1` and `k+1`, layer `k` being the same activation on fewer inputs.

One departure, forced by [1, Alg. 3], which runs this on a network already reduced: [1, Prop. 4]
*sets* `Î'_{k+1} := W_{k+1}(·,B) I_k(B)`, which is right only while `I'_{k+1} = [0, 0]`, and
`mergeCols` *adds* it, as [1, Eq. 4] adds the errors of several buckets. On an original network
the two agree.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet IntervalOuter

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]

/-- [1, Prop. 4] at layer `k-1`: `Ŵ_{k-1} = W_{k-1}(B̄,·)`, `b̂_{k-1} = b_{k-1}(B̄)`,
`Î'_{k-1} = I'_{k-1}(B̄)`, the survivors `B̄` on the left of `part`. -/
def ReducedLinear.mergeRows {n n₁ d r : ℕ} (L : ReducedLinear n n₁)
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r)) : ReducedLinear n d where
  W := L.W.submatrix part.left id
  b := L.b ∘ part.left
  I' := ⟨L.I'.inf ∘ part.left, L.I'.sup ∘ part.left⟩

/-- [1, Prop. 4] at layer `k+1`: `Ŵ_{k+1} = W_{k+1}(·,B̄)`, `b̂_{k+1} = b_{k+1}`, and the bucket
`B` on the right of `part` paying `W_{k+1}(·,B) I_k(B)` into the error. -/
noncomputable def ReducedLinear.mergeCols {n₁ n₂ d r : ℕ} (L : ReducedLinear n₁ n₂)
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r)) (I_k : Interval (Vec ℝ n₁)) :
    ReducedLinear d n₂ where
  W := L.W.submatrix id part.left
  b := L.b
  I' := Interval.plus L.I'
    (Interval.mtimes (L.W.submatrix id part.right) ⟨I_k.inf ∘ part.right, I_k.sup ∘ part.right⟩)

/-- [1, Alg. 2] from one `k` on: `H_km2` is `H_{k-2}`, `Lhat_km1` is `L̂_{k-1}` and `L_k` the
activation; `Φ̂_ρ` from layer `k-1` on comes back with `Y = H_κ`, `none` where Alg. 1 gave out. -/
noncomputable def reduceOnTheFlyFrom (le : ℝ → ℝ → Bool) (tol : ℝ) (fuel : ℕ) (ρ : ℝ) :
    ∀ {n n₁ m : ℕ}, S n → ReducedLinear n n₁ → {σ : ℝ → ℝ} → Relaxation σ → MergeBuckets ℝ →
      ReducibleNetwork n₁ m → Option (ReducibleNetwork n m × S m)
  | _, _, _, H_km2, Lhat_km1, _, L_k, B, .nil =>                    -- Alg. 2, line 3: k = κ
    let H_km1 := Lhat_km1.toLayer.enclose H_km2                     -- Alg. 2, line 10
    let H_k := (Layer.activation L_k).enclose H_km1                 -- Alg. 2, line 11
    some (.cons Lhat_km1 L_k B .nil, H_k)                           -- Alg. 2, line 13: Y ← H_κ
  | _, _, _, H_km2, Lhat_km1, _, L_k, B, .cons L_kp1 L_kp2 B' rest =>  -- Alg. 2, line 3: k < κ
    let I_km2 := interval H_km2                                     -- Alg. 2, line 4
    let I_k := (Layer.activation (S := ℐ𝒱) L_k).enclose
      ((Lhat_km1.toLayer (S := ℐ𝒱)).enclose I_km2)                  -- Alg. 2, line 5
    match bucketTolerance le tol fuel B I_k ρ with                  -- Alg. 2, line 6
    | none => none
    | some B_kδ =>
      let part := Partition.ofPred fun i => B_kδ i = true           -- Alg. 2, line 7: B̄ ⊕ B
      let Lhat_km1 := Lhat_km1.mergeRows part                       -- Alg. 2, line 7: L̂_{k-1}
      let Lhat_kp1 := L_kp1.mergeCols part I_k                      -- Alg. 2, line 7: L̂_{k+1}
      let H_km1 := Lhat_km1.toLayer.enclose H_km2                   -- Alg. 2, line 10
      let H_k := (Layer.activation L_k).enclose H_km1               -- Alg. 2, line 11: L̂_k
      match reduceOnTheFlyFrom le tol fuel ρ H_k Lhat_kp1 L_kp2 B' rest with  -- line 2: k + 2
      | none => none
      | some (Φhat, Y) => some (.cons Lhat_km1 L_k B Φhat, Y)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the network `Φ` reduced at rate `ρ` along the input set `X`, and the output
set `Y` it computes on the way; `none` where [1, Alg. 1] ran out of `fuel` at some layer. -/
noncomputable def reduceOnTheFly (le : ℝ → ℝ → Bool) (tol : ℝ) (fuel : ℕ) {n m : ℕ} (X : S n)
    (ρ : ℝ) : ReducibleNetwork n m → Option (ReducibleNetwork n m × S m)
  | .nil => some (.nil, X)                                          -- κ = 0: no layer to reduce
  | .cons L_1 L_2 B rest =>
    let H_0 := X                                                    -- Alg. 2, line 1
    let Lhat_1 := L_1                                               -- Alg. 2, line 1
    reduceOnTheFlyFrom le tol fuel ρ H_0 Lhat_1 L_2 B rest          -- Alg. 2, lines 2-13

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
