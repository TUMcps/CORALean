import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.NN.Layers.ReLU
import CORALean.NN.ReduceOnTheFly

/-!
# [1, Alg. 3]: compressing the input before verifying

[1, Cor. 1]'s compression network `Φ_pre` — the identity kernel, a ReLU, the identity kernel —
is prepended to `Φ_org` and reduced first, on the input box `I_X` alone. The set representation
is only built for what survives, `H_{-2}`, and [1, Alg. 2] then runs from there through the
compressed image into `Φ_org`, reducing on the fly.

Three readings, each forced by [1, Def. 1]'s alternation, which [1, Alg. 2] relies on. `Φ_org`
has at least one layer pair, `L_1` and `L_2`. `L_0`, being the identity, is composed into
`L_1` before anything is reduced — `W_1 · I = W_1` exactly, in either layer, where a general
product `W_1 Ŵ_0` would round — so line 2's `L̂_0` arrives inside `L̂_1`. And `Φ'_org` opens
with `L̂_{-1}`, a nonlinear layer, so line 4 puts the identity, `I' = [0, 0]`, before it; the
loop then reduces `L̂_{-1}` again at line 5, as it reduces every `k < κ` of `Φ'_org`.
Line 2 is [1, Alg. 2] on `Φ_pre` at the one nonlinear layer below its last, lines 4-7, the
set there being `I_X` itself; the sets its lines 10-11 would go on to compute are not used.

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

open ContSet OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]

/-- The identity as a layer of [1, Eq. 2]: [1, Cor. 1]'s kernel `K(k,l,1,1) = [k = l]`, which
leaves every pixel where it is, with no error. -/
noncomputable def ReducedLinear.identity (n : ℕ) : ReducedLinear n n := ⟨1, 0, Interval.point 0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the output set of `Φ_org = (L_1, L_2, …)` on the image box `I_X`, compressed
by `Φ_pre` first and reduced on the fly at rate `ρ`; `none` where [1, Alg. 1] gave out. -/
noncomputable def compressionPreprocessing (le : ℝ → ℝ → Bool) (tol : ℝ) (fuel : ℕ)
    (R_relu : Relaxation relu) {n n₁ m : ℕ} (I_X : Interval (Vec ℝ n)) (L_1 : ReducedLinear n n₁)
    {σ₂ : ℝ → ℝ} (L_2 : Relaxation σ₂) (B_2 : MergeBuckets ℝ) (rest : ReducibleNetwork n₁ m)
    (ρ : ℝ) : Option (S m) :=
  let L_m2 := ReducedLinear.identity n                              -- Alg. 3, line 1: L_{-2}
  let L_m1 := R_relu                                                -- Alg. 3, line 1: L_{-1}
  let I_m1 := (Layer.activation (S := ℐ𝒱) L_m1).enclose
    ((L_m2.toLayer (S := ℐ𝒱)).enclose I_X)                          -- Alg. 3, line 2 (Alg. 2, l. 5)
  match bucketTolerance le tol fuel .dynamic I_m1 ρ with            -- Alg. 3, line 2 (Alg. 2, l. 6)
  | none => none
  | some B_m1δ =>
    let part := Partition.ofPred fun i => B_m1δ i = true            -- Alg. 3, line 2 (Alg. 2, l. 7)
    let Lhat_m2 := L_m2.mergeRows part                              -- Alg. 3, line 2: L̂_{-2}
    let Lhat_1 := L_1.mergeCols part I_m1                           -- Alg. 3, line 2: L̂_0, in L_1
    let H_m2 := ofInterval ((Lhat_m2.toLayer (S := ℐ𝒱)).enclose I_X)  -- Alg. 3, line 3
    let Φ'_org := ReducibleNetwork.cons (ReducedLinear.identity _) L_m1 .dynamic
      (.cons Lhat_1 L_2 B_2 rest)                                   -- Alg. 3, line 4
    match reduceOnTheFly le tol fuel H_m2 ρ Φ'_org with             -- Alg. 3, line 5
    | some (_, Y) => some Y                                         -- Alg. 3, line 6
    | none => none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
