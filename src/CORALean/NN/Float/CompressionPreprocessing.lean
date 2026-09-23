import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.NN.Float.ReduceOnTheFly

/-!
# [1, Alg. 3] over a floating-point scalar

`Real.compressionPreprocessing` line for line, and a `def`. The identity kernel is the matrix
`diagonalBlock` places ones on, stored exactly, and composing it into `L_1` costs nothing here
either: [1, Prop. 4]'s column selection is what reaches `L_1`, never a product. The ReLU is
whichever float relaxation the caller passes; `compressionPreprocessing_outer` asks that it be
sound for `Real.relu`.

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

open ContSet OfInterval FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]

/-- The identity as a layer of [1, Eq. 2]: [1, Cor. 1]'s kernel `K(k,l,1,1) = [k = l]`, which
leaves every pixel where it is, with no error. -/
def ReducedLinear.identity (n : ℕ) : ReducedLinear 𝕋 n n :=
  ⟨diagonalBlock fun _ => one, fun _ => zero, Interval.point fun _ => zero⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the output set of `Φ_org = (L_1, L_2, …)` on the image box `I_X`, compressed
by `Φ_pre` first and reduced on the fly at rate `ρ`; `none` where [1, Alg. 1] gave out. -/
def compressionPreprocessing (tol : 𝕋) (fuel : ℕ) (R_relu : Relaxation 𝕋) {n n₁ m : ℕ}
    (I_X : Interval 𝕋 n) (L_1 : ReducedLinear 𝕋 n n₁) (L_2 : Relaxation 𝕋) (B_2 : MergeBuckets 𝕋)
    (rest : ReducibleNetwork 𝕋 n₁ m) (ρ : 𝕋) : Option (S m) :=
  let L_m2 := ReducedLinear.identity (𝕋 := 𝕋) n                     -- Alg. 3, line 1: L_{-2}
  let L_m1 := R_relu                                                -- Alg. 3, line 1: L_{-1}
  let I_m1 := (Layer.activation (S := Interval 𝕋) L_m1).enclose
    ((L_m2.toLayer (S := Interval 𝕋)).enclose I_X)                  -- Alg. 3, line 2 (Alg. 2, l. 5)
  match bucketTolerance tol fuel .dynamic I_m1 ρ with               -- Alg. 3, line 2 (Alg. 2, l. 6)
  | none => none
  | some B_m1δ =>
    let part := Partition.ofPred fun i => B_m1δ i = true            -- Alg. 3, line 2 (Alg. 2, l. 7)
    let Lhat_m2 := L_m2.mergeRows part                              -- Alg. 3, line 2: L̂_{-2}
    let Lhat_1 := L_1.mergeCols part I_m1                           -- Alg. 3, line 2: L̂_0, in L_1
    let H_m2 := ofInterval
      ((Lhat_m2.toLayer (S := Interval 𝕋)).enclose I_X)             -- Alg. 3, line 3
    let Φ'_org := ReducibleNetwork.cons (ReducedLinear.identity _) L_m1 .dynamic
      (.cons Lhat_1 L_2 B_2 rest)                                   -- Alg. 3, line 4
    match reduceOnTheFly tol fuel H_m2 ρ Φ'_org with                -- Alg. 3, line 5
    | some (_, Y) => some Y                                         -- Alg. 3, line 6
    | none => none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
