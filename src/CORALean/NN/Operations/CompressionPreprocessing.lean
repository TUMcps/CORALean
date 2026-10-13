import CORALean.NN.Operations.ReduceOnTheFly
import CORALean.NN.Operations.ReducedLinearIdentity

/-!
# [1, Alg. 3]: compressing the input before verifying

[1, Cor. 1]'s compression network `Φ_pre` — the identity kernel, a ReLU, the identity kernel —
is prepended to `Φ_org` and reduced first, on the input box `I_X` alone. The set representation
is only built for what survives, `H_{-2}`, and [1, Alg. 2] then runs from there on.

Three readings, each forced by [1, Def. 1]'s alternation. `Φ_org` has at least one layer pair.
`L_0`, the identity, is composed into `L_1` before anything is reduced — [1, Prop. 4]'s column
selection is what reaches `L_1`, never a product, so nothing rounds. And `Φ'_org` opens with
`L̂_{-1}`, a nonlinear layer, so line 4 puts the identity before it, which line 5 reduces again.
The ReLU is the caller's relaxation; `compressionPreprocessing_outer` asks it be sound.

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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the output set of `Φ_org = (L_1, L_2, …)` on the image box `I_X`, compressed
by `Φ_pre` first and reduced on the fly at rate `ρ`; `none` where [1, Alg. 1] gave out. -/
def compressionPreprocessing (le : 𝕋 → 𝕋 → Bool) (tol : 𝕋) (fuel : ℕ) (R_relu : Relaxation 𝕋)
    (hσ_relu : ∃ σ : ℝ → ℝ, R_relu.Sound σ)
    {n n₁ m : ℕ} (I_X : Interval (Vec 𝕋 n)) (L_1 : ReducedLinear 𝕋 n n₁) (L_2 : Relaxation 𝕋)
    (hσ_2 : ∃ σ : ℝ → ℝ, L_2.Sound σ)
    (B_2 : MergeBuckets 𝕋) (rest : ReducibleNetwork 𝕋 n₁ m) (ρ : 𝕋) : Option (S m) :=
  let L_m2 := ReducedLinear.identity (𝕋 := 𝕋) n                     -- Alg. 3, line 1: L_{-2}
  let L_m1 := R_relu                                                -- Alg. 3, line 1: L_{-1}
  let I_m1 :=                                                       -- Alg. 3, line 2 (Alg. 2, l. 5)
    (Layer.activation (S := fun n => Interval (Vec 𝕋 n)) L_m1).enclose
      ((L_m2.toLayer (S := fun n => Interval (Vec 𝕋 n))).enclose I_X)
  match bucketTolerance le tol fuel .dynamic I_m1 ρ with            -- Alg. 3, line 2 (Alg. 2, l. 6)
  | none => none
  | some B_m1δ =>
    let part := Partition.ofPred fun i => B_m1δ i = true            -- Alg. 3, line 2 (Alg. 2, l. 7)
    let Lhat_m2 := L_m2.mergeRows part                              -- Alg. 3, line 2: L̂_{-2}
    let Lhat_1 := L_1.mergeCols part I_m1                           -- Alg. 3, line 2: L̂_0, in L_1
    let H_m2 := ofInterval                                          -- Alg. 3, line 3
      ((Lhat_m2.toLayer (S := fun n => Interval (Vec 𝕋 n))).enclose I_X)
    let Φ'_org := ReducibleNetwork.cons (ReducedLinear.identity _) L_m1 hσ_relu .dynamic
      (.cons Lhat_1 L_2 hσ_2 B_2 rest)                              -- Alg. 3, line 4
    match reduceOnTheFly le tol fuel H_m2 ρ Φ'_org with             -- Alg. 3, line 5
    | some (_, Y) => some Y                                         -- Alg. 3, line 6
    | none => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
