module

public import CORALean.NN.Operations.ReduceOnTheFly
public import CORALean.NN.Operations.ReducedLinearIdentity

@[expose] public section

/-!
# [1, Alg. 3]: compressing the input before verifying

[1, Cor. 1]'s compression network `Φ_pre` — the identity kernel, a ReLU, the identity kernel — is
prepended to `Φ_org` and reduced first, on the input box `I_X` alone. The set representation is only
built for what survives, `H_{-2}`, and [1, Alg. 2] then runs from there on. Three readings, each
forced by [1, Def. 1]'s alternation: `Φ_org` has at least one layer pair; `L_0`, the identity, is
composed into `L_1` before anything is reduced, so nothing rounds; and `Φ'_org` opens with
`L̂_{-1}`, a nonlinear layer, so line 4 puts the identity before it, which line 5 reduces again. The
ReLU is the caller's relaxation; `compressionPreprocessing_outer` asks it be sound.

## Inputs
* `le` – comparison of two scalars
* `tol` – tolerance on the remaining fraction
* `fuel` – bound on the loop iterations
* `R_relu` – relaxation of ReLU
* `n` – input width
* `n₁` – first hidden width
* `m` – output width
* `I_X` – input box
* `L_1` – first reduced linear layer
* `L_2` – second layer's relaxation
* `B_2` – merge buckets of the second layer
* `rest` – remaining reducible network
* `ρ` – reduction rate

## Hypotheses
* `hσ_relu` – ReLU relaxation is sound for some function
* `hσ_2` – second relaxation is sound for some function

## Output
* output set of the compressed and reduced network, or none if Alg. 1 gave out

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float ContSet OfInterval
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the output set of `Φ_org = (L_1, L_2, …)` on the image box `I_X`, compressed
by `Φ_pre` first and reduced on the fly at rate `ρ`; `none` where [1, Alg. 1] gave out. -/
def compressionPreprocessing (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) (R_relu : Relaxation 𝕋)
    (hσ_relu : ∃ σ : ℝ → ℝ, R_relu.IsSound σ)
    {n n₁ m : ℕ} (I_X : Interval (Vec 𝕋 n)) (L_1 : ReducedLinear 𝕋 n n₁) (L_2 : Relaxation 𝕋)
    (hσ_2 : ∃ σ : ℝ → ℝ, L_2.IsSound σ)
    (B_2 : MergeBuckets 𝕋) (rest : ReducibleNetwork 𝕋 n₁ m) (ρ : 𝕋) : Option (S m) :=
  -- 1. `L_{-2}`, the identity, of `L_{-2}, L_{-1}, L_0 ← construct Φ_pre` (Cor. 1)
  let L_m2 := ReducedLinear.identity (𝕋 := 𝕋) n
  -- 1. `L_{-1}`, the ReLU; `L_0`, the identity, is composed into `L_1`
  let L_m1 := R_relu
  -- 2. `L̂_{-2}, L̂_{-1}, L̂_0 ← reduce using I_X, ρ` (Thm. 1): Alg. 2's line 5, `I_{-1}`
  let I_m1 :=
    (Layer.activation (S := ℐ𝒱[𝕋]) L_m1).enclose
      ((L_m2.toLayer (S := ℐ𝒱[𝕋])).enclose I_X)
  -- 2. … Alg. 2's line 6: the merge buckets `B_{-1,δ}` at the tolerance of `Alg. 1`
  match bucketTolerance le tol fuel .dynamic I_m1 ρ with
  | none => none
  | some B_m1δ =>
    -- 2. … Alg. 2's line 7: the neurons the buckets merge
    let part := Partition.ofPred fun i => B_m1δ i = true
    -- 2. … `L̂_{-2}` merges the rows of `L_{-2}`
    let Lhat_m2 := L_m2.mergeRows part
    -- 2. … `L̂_0` merges the columns of `L_1`, composed into it
    let Lhat_1 := L_1.mergeCols part I_m1
    -- 3. `H_{-2} ← zonotope(L̂_{-2}(I_X))` (Prop. 2)
    let H_m2 := ofInterval
      ((Lhat_m2.toLayer (S := ℐ𝒱[𝕋])).enclose I_X)
    -- 4. `Φ'_org(·) ← Φ_org(L̂_0(L̂_{-1}(·)))`: the layers prepended
    let Φ'_org := ReducibleNetwork.cons (ReducedLinear.identity _) L_m1 hσ_relu .dynamic
      (.cons Lhat_1 L_2 hσ_2 B_2 rest)
    -- 5. `Y ← execute Alg. 2 using H_{-2}, Φ'_org, ρ`, 6. `return Y`
    match reduceOnTheFly le tol fuel H_m2 ρ Φ'_org with
    | some (_, Y) => some Y
    | none => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
