module

public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.NN.Operations.BucketTolerance
public import CORALean.NN.Operations.MergeCols
public import CORALean.NN.Operations.ReducedLinearToLayer
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# [1, Alg. 2] from one nonlinear layer on

The loop of [1, Alg. 2] from layer `k` on, with `H_{k-2}` and the pending linear layer
`L̂_{k-1}` in hand, recursing on the layers after `k + 1`; the case split on them is line 3's
`k < κ`. Before each nonlinear layer but the last it looks ahead: `H_{k-2}` is boxed and pushed
through `L̂_{k-1}` and `L_k` at the interval family to bounds `I_k`, [1, Alg. 1] picks the
buckets there, and `mergeRows`/`mergeCols` apply [1, Prop. 4]. Only then does the set pass the
two reduced layers. The split of a layer's neurons is `Partition.ofPred`, which sorts rather
than choosing.

## Inputs
* `le` – comparison of two scalars
* `tol` – tolerance on the remaining fraction
* `fuel` – bound on the loop iterations
* `ρ` – reduction rate

## Output
* reduced network from the layer on with the output set, or none if the fuel runs out

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float ContSet IntervalOuter
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] from one `k` on: `H_km2` is `H_{k-2}`, `Lhat_km1` is `L̂_{k-1}` and `L_k` the
activation; `Φ̂_ρ` from layer `k-1` on comes back with `Y = H_κ`, `none` where Alg. 1 gave out. -/
def reduceOnTheFlyFrom (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) (ρ : 𝕋) :
    ∀ {n n₁ m : ℕ}, S n → ReducedLinear 𝕋 n n₁ → (R : Relaxation 𝕋) →
      (∃ σ : ℝ → ℝ, R.IsSound σ) → MergeBuckets 𝕋 → ReducibleNetwork 𝕋 n₁ m →
      Option (ReducibleNetwork 𝕋 n m × S m)
  -- 3. `if k < κ` fails, `k = κ`: no look-ahead, lines 4-8 are skipped
  | _, _, _, H_km2, Lhat_km1, L_k, hσ_k, B, .nil =>
    -- 10. `H_{k-1} ← enclose(L̂_{k-1}, H_{k-2})` (Prop. 3)
    let H_km1 := Lhat_km1.toLayer.enclose H_km2
    -- 11. `H_k ← enclose(L̂_k, H_{k-1})`
    let H_k := (Layer.activation L_k).enclose H_km1
    -- 13. `return Y ← H_κ`
    some (.cons Lhat_km1 L_k hσ_k B .nil, H_k)
  -- 3. `if k < κ` holds: the look-ahead of lines 4-7
  | _, _, _, H_km2, Lhat_km1, L_k, hσ_k, B, .cons L_kp1 L_kp2 hσ_kp2 B' rest =>
    -- 4. `I_{k-2} ← interval(H_{k-2})` (Prop. 1)
    let I_km2 := interval H_km2
    -- 5. `I_k ← L_k(L̂_{k-1}(I_{k-2}))`
    let I_k :=
      (Layer.activation (S := ℐ𝒱[𝕋]) L_k).enclose
        ((Lhat_km1.toLayer (S := ℐ𝒱[𝕋])).enclose I_km2)
    -- 6. determine the merge buckets `B_{k,δ}` (Sec. 3.3, Alg. 1)
    match bucketTolerance le tol fuel B I_k ρ with
    | none => none
    | some B_kδ =>
      -- 7. `L̂_{k-1}, L̂_k, L̂_{k+1} ← merge`: the neurons the buckets merge
      let part := Partition.ofPred fun i => B_kδ i = true
      -- 7. … `L̂_{k-1}`, its rows merged (Prop. 4)
      let Lhat_km1 := Lhat_km1.mergeRows part
      -- 7. … `L̂_{k+1}`, its columns merged
      let Lhat_kp1 := L_kp1.mergeCols part I_k
      -- 10. `H_{k-1} ← enclose(L̂_{k-1}, H_{k-2})` (Prop. 3)
      let H_km1 := Lhat_km1.toLayer.enclose H_km2
      -- 11. `H_k ← enclose(L̂_k, H_{k-1})`
      let H_k := (Layer.activation L_k).enclose H_km1
      -- 2. `for k = 2, 4, …, κ`: the next pass is `k + 2`
      match reduceOnTheFlyFrom le tol fuel ρ H_k Lhat_kp1 L_kp2 hσ_kp2 B' rest with
      | none => none
      | some (Φhat, Y) => some (.cons Lhat_km1 L_k hσ_k B Φhat, Y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
