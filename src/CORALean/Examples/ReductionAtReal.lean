import CORALean.Global.Float.Instances.Real.Theorems.Basic
import CORALean.NN.Definitions.Reduction
import CORALean.NN.Theorems.BucketToleranceApprox
import CORALean.NN.Theorems.CompressionPreprocessingOuter
import CORALean.NN.Theorems.HoldsOfReduceOnTheFly
import CORALean.NN.Theorems.NeuronMergingOuter
import CORALean.NN.Theorems.Real.InstanceOfInstanceNetwork

/-!
# Network reduction read at `𝕋 := ℝ`

The reduction [1] is written once over the scalar, and its theorems with it. At ℝ every rounding
is exact, so each reads as the statement the exact layer used to prove on its own, and these are
those statements, derived: the tolerance test as `|n̂_k/n_k - ρ| ≤ tol`, Prop. 4 at real
weights, and Thm. 1 and Alg. 3's soundness at a network of layers `IsInstanceNetwork` names.

What they need beyond instantiation is only that counting in the scalar is exact at ℝ, which
is what `ratio` reads at `𝕋 := ℝ` once the repeated additions are summed.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix ContSet Float Float.FloatOps

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S] {n m : ℕ}

/-- [1, Alg. 1] at ℝ: what `bucketTolerance_approx` says is the fraction of neurons left within
`tol` of `ρ`, exactly, at any order `le` sound on a `true`. -/
example {le : ℝ → ℝ → Bool} (hle : ∀ a b, le a b = true → a ≤ b) {tol : ℝ} {fuel : ℕ}
    {B : MergeBuckets ℝ} {I_k : Float.Interval (Vec ℝ n)} {ρ : ℝ} {B_kδ : Fin n → Bool}
    (h : bucketTolerance le tol fuel B I_k ρ = some B_kδ) :
    |((n - bucketed B_kδ : ℕ) : ℝ) / n - ρ| ≤ tol := by
  -- counting is exact at ℝ, so the scalar's quotient is the quotient
  have hcount : ∀ k : ℕ, nsmulDown k (1 : ℝ) = k ∧ nsmulUp k (1 : ℝ) = k := fun k => by
    induction k with
    | zero => exact ⟨by show (0 : ℝ) = _; simp, by show (0 : ℝ) = _; simp⟩
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · show (1 : ℝ) + nsmulDown k 1 = _; rw [ih.1]; push_cast; ring
      · show (1 : ℝ) + nsmulUp k 1 = _; rw [ih.2]; push_cast; ring
  have happrox := bucketTolerance_approx hle _ h
  have hratio : ratio (𝕋 := ℝ) (n - bucketed B_kδ) n = ((n - bucketed B_kδ : ℕ) : ℝ) / n := by
    show nsmulDown _ (1 : ℝ) / nsmulUp _ 1 = _
    rw [(hcount _).1, (hcount _).2]
  rw [toReal_real, toReal_real, hratio] at happrox
  exact happrox

/-- [1, Prop. 4] at real weights: the generic statement, its `toRealMat` reading `W` itself. -/
example {d r n0 n2 : ℕ} (part : Split (Fin n) into (Fin d) ⊕ (Fin r)) (W0 : Mat ℝ n n0)
    (b0 : Vec ℝ n) {σ : ℝ → ℝ} (R : Relaxation ℝ) (hR : R.IsSound σ) (W1 : Mat ℝ n2 n)
    (b1 : Vec ℝ n2) (Y : Float.Interval (Vec ℝ n)) (X : S n0)
    (hY : ∀ x ∈ construct X, (fun i => σ ((W0 *ᵥ x + b0) i)) ∈ construct Y) :
    (fun x => W1 *ᵥ (fun i => σ ((W0 *ᵥ x + b0) i)) + b1) '' construct X
      ⊆ construct ((mergedSandwich part W0 b0 hR W1 b1 Y : NeuralNetwork S n0 n2).enclose X) :=
  neuronMerging_sandwich_outer part W0 b0 R hR W1 b1 Y X hY

/-- [1, Thm. 1] at a network of layers: an instance network is an instance. -/
example {le : ℝ → ℝ → Bool} {tol : ℝ} {fuel : ℕ} {ρ : ℝ} {X : S n}
    {Φ Φhat : ReducibleNetwork ℝ n m} {Y : S m} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hΦ : Φ.IsInstanceNetwork nn f)
    (hrun : reduceOnTheFly le tol fuel X ρ Φ = some (Φhat, Y))
    (spec : Specification (Set (Vec ℝ m))) (hspec : spec.Holds (construct Y)) :
    spec.Holds (f '' construct X) :=
  holds_of_reduceOnTheFly (instance_of_instanceNetwork hΦ) spec _ _ hrun hspec

/-- [1, Alg. 3] at a network of layers, the ReLU any relaxation sound for it. -/
example {le : ℝ → ℝ → Bool} {tol : ℝ} {fuel : ℕ} {R_relu : Relaxation ℝ}
    (hR : R_relu.IsSound Real.relu) {n₁ : ℕ} {I_X : Float.Interval (Vec ℝ n)}
    (hX : ∀ x ∈ I_X.construct, ∀ i, 0 ≤ x i) {L_1 : ReducedLinear ℝ n n₁}
    {L_2 : Relaxation ℝ} {hL_2 : ∃ σ : ℝ → ℝ, L_2.IsSound σ} {B_2 : MergeBuckets ℝ}
    {rest : ReducibleNetwork ℝ n₁ m} {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hΦ : (ReducibleNetwork.cons L_1 L_2 hL_2 B_2 rest).IsInstanceNetwork nn f) {ρ : ℝ} {Y : S m}
    (hrun : compressionPreprocessing le tol fuel R_relu ⟨_, hR⟩ I_X L_1 L_2 hL_2 B_2 rest ρ
      = some Y) :
    f '' I_X.construct ⊆ construct Y :=
  compressionPreprocessing_outer hR hX (instance_of_instanceNetwork hΦ) _ hrun

end CORALean.Real
