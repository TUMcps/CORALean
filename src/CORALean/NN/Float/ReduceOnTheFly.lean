import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.Interval.Float.Operations.Mtimes
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.NN.Float.BucketTolerance
import CORALean.NN.Float.ReducibleNetwork

/-!
# [1, Alg. 2] over a floating-point scalar

`Real.reduceOnTheFly` line for line, and a `def`: the look-ahead runs the float layers at the
float interval family, [1, Alg. 1] is `Float.bucketTolerance`, and the split of a layer's
neurons is `Partition.ofPred`, which sorts rather than choosing. `mergeCols` rounds once, in
`Interval.mtimes` and `Interval.plus`, both outward; the rest of line 7 only selects floats.

`reduceOnTheFly_outer` is its soundness, at every instance of the network it is given.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet IntervalOuter

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]

/-- [1, Prop. 4] at layer `k-1`: `Ŵ_{k-1} = W_{k-1}(B̄,·)`, `b̂_{k-1} = b_{k-1}(B̄)`,
`Î'_{k-1} = I'_{k-1}(B̄)`, the survivors `B̄` on the left of `part`. -/
def ReducedLinear.mergeRows {n n₁ d r : ℕ} (L : ReducedLinear 𝕋 n n₁)
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r)) : ReducedLinear 𝕋 n d where
  W := L.W.submatrix part.left id
  b := L.b ∘ part.left
  I' := ⟨L.I'.inf ∘ part.left, L.I'.sup ∘ part.left⟩

/-- [1, Prop. 4] at layer `k+1`: `Ŵ_{k+1} = W_{k+1}(·,B̄)`, `b̂_{k+1} = b_{k+1}`, and the bucket
`B` on the right of `part` paying `W_{k+1}(·,B) I_k(B)` into the error. -/
def ReducedLinear.mergeCols {n₁ n₂ d r : ℕ} (L : ReducedLinear 𝕋 n₁ n₂)
    (part : Split (Fin n₁) into (Fin d) ⊕ (Fin r)) (I_k : Interval 𝕋 n₁) :
    ReducedLinear 𝕋 d n₂ where
  W := L.W.submatrix id part.left
  b := L.b
  I' := Interval.plus L.I'
    (Interval.mtimes (L.W.submatrix id part.right) ⟨I_k.inf ∘ part.right, I_k.sup ∘ part.right⟩)

/-- [1, Alg. 2] from one `k` on: `H_km2` is `H_{k-2}`, `Lhat_km1` is `L̂_{k-1}` and `L_k` the
activation; `Φ̂_ρ` from layer `k-1` on comes back with `Y = H_κ`, `none` where Alg. 1 gave out. -/
def reduceOnTheFlyFrom (tol : 𝕋) (fuel : ℕ) (ρ : 𝕋) :
    ∀ {n n₁ m : ℕ}, S n → ReducedLinear 𝕋 n n₁ → Relaxation 𝕋 → MergeBuckets 𝕋 →
      ReducibleNetwork 𝕋 n₁ m → Option (ReducibleNetwork 𝕋 n m × S m)
  | _, _, _, H_km2, Lhat_km1, L_k, B, .nil =>                       -- Alg. 2, line 3: k = κ
    let H_km1 := Lhat_km1.toLayer.enclose H_km2                     -- Alg. 2, line 10
    let H_k := (Layer.activation L_k).enclose H_km1                 -- Alg. 2, line 11
    some (.cons Lhat_km1 L_k B .nil, H_k)                           -- Alg. 2, line 13: Y ← H_κ
  | _, _, _, H_km2, Lhat_km1, L_k, B, .cons L_kp1 L_kp2 B' rest =>  -- Alg. 2, line 3: k < κ
    let I_km2 := interval H_km2                                     -- Alg. 2, line 4
    let I_k := (Layer.activation (S := Interval 𝕋) L_k).enclose
      ((Lhat_km1.toLayer (S := Interval 𝕋)).enclose I_km2)          -- Alg. 2, line 5
    match bucketTolerance tol fuel B I_k ρ with                     -- Alg. 2, line 6
    | none => none
    | some B_kδ =>
      let part := Partition.ofPred fun i => B_kδ i = true           -- Alg. 2, line 7: B̄ ⊕ B
      let Lhat_km1 := Lhat_km1.mergeRows part                       -- Alg. 2, line 7: L̂_{k-1}
      let Lhat_kp1 := L_kp1.mergeCols part I_k                      -- Alg. 2, line 7: L̂_{k+1}
      let H_km1 := Lhat_km1.toLayer.enclose H_km2                   -- Alg. 2, line 10
      let H_k := (Layer.activation L_k).enclose H_km1               -- Alg. 2, line 11: L̂_k
      match reduceOnTheFlyFrom tol fuel ρ H_k Lhat_kp1 L_kp2 B' rest with  -- line 2: k + 2
      | none => none
      | some (Φhat, Y) => some (.cons Lhat_km1 L_k B Φhat, Y)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the network `Φ` reduced at rate `ρ` along the input set `X`, and the output
set `Y` it computes on the way; `none` where [1, Alg. 1] ran out of `fuel` at some layer. -/
def reduceOnTheFly (tol : 𝕋) (fuel : ℕ) {n m : ℕ} (X : S n) (ρ : 𝕋) :
    ReducibleNetwork 𝕋 n m → Option (ReducibleNetwork 𝕋 n m × S m)
  | .nil => some (.nil, X)                                          -- κ = 0: no layer to reduce
  | .cons L_1 L_2 B rest =>
    let H_0 := X                                                    -- Alg. 2, line 1
    let Lhat_1 := L_1                                               -- Alg. 2, line 1
    reduceOnTheFlyFrom tol fuel ρ H_0 Lhat_1 L_2 B rest             -- Alg. 2, lines 2-13

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
