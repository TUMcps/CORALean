import CORALean.ContSet.Interval.Float.Theorems.SubsetNonemptyHull
import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.Relaxation
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Operations.Activation
import CORALean.NN.Layers.Operations.Relu
import CORALean.NN.Layers.Theorems.ActivationSound
import CORALean.NN.Layers.Theorems.LinearWithErrorMem
import CORALean.NN.Operations.CompressionPreprocessing
import CORALean.NN.Theorems.ReduceOnTheFlyOuter

/-!
# [1, Alg. 3] is sound on a nonnegative image

[1, Cor. 1]'s compression network computes the identity on `ℝ₊ⁿ`: the stored identity
kernel denotes the identity and its stored zeros zero, so line 2's look-ahead box holds the
merged pixels of a nonnegative `x`, line 3's `H_{-2}` its surviving ones, and `Φ'_org` frozen
at the merged ones is an instance computing `Φ_org` at `x`, which `reduceOnTheFly_outer`
carries into `Y`. The ReLU relaxation is the caller's, sound for `Real.relu`; the
nonnegativity is [1, Cor. 1]'s `X ⊂ ℝ₊`, without which the ReLU is not the identity.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.IntervalOuter Float.OfInterval Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3]: on a nonnegative image box `I_X`, the output set holds every
instance of `Φ_org` at every point of `I_X`. -/
theorem compressionPreprocessing_outer {le : 𝕋 → 𝕋 → Bool} {tol : 𝕋} {fuel : ℕ}
    {R_relu : Relaxation 𝕋} (hR : R_relu.Sound Real.relu)
    {hσ_relu : ∃ σ : ℝ → ℝ, R_relu.Sound σ} {n n₁ m : ℕ} {I_X : Interval 𝕋 n}
    (hX : ∀ x ∈ I_X.construct, ∀ i, 0 ≤ x i) {L_1 : ReducedLinear 𝕋 n n₁} {L_2 : Relaxation 𝕋}
    {hσ_2 : ∃ σ : ℝ → ℝ, L_2.Sound σ}
    {B_2 : MergeBuckets 𝕋} {rest : ReducibleNetwork 𝕋 n₁ m} {f : Vec ℝ n → Vec ℝ m}
    (hΦ : (ReducibleNetwork.cons L_1 L_2 hσ_2 B_2 rest).Instance f) {ρ : 𝕋} {Y : S m}
    (hrun : compressionPreprocessing le tol fuel R_relu hσ_relu I_X L_1 L_2 hσ_2 B_2 rest ρ
      = some Y) :
    f '' I_X.construct ⊆ construct Y := by -- --- PROOF ---
  cases hΦ with
  | @cons _ _ _ _ c1 _ _ σ₂ _ _ h1 _ hR2 hc1 hrest1 hf1 =>
  simp only [compressionPreprocessing] at hrun
  split at hrun
  · exact absurd hrun (by simp)
  · rename_i B_m1δ _
    split at hrun
    · rename_i Φhat Y' hrun2
      cases hrun
      set part := Partition.ofPred fun i => B_m1δ i = true
      set I_m1 := (Layer.activation (S := Interval 𝕋) R_relu).enclose
        (((ReducedLinear.identity (𝕋 := 𝕋) n).toLayer (S := Interval 𝕋)).enclose I_X)
      rintro _ ⟨x, hx, rfl⟩
      -- the stored identity denotes the identity, and the stored zeros zero
      have hId : ∀ k, toRealMat (diagonalBlock fun _ : Fin k => (FloatOps.one : 𝕋)) = 1 := by
        intro k
        funext i j
        rw [toRealMat, toReal_diagonalBlock]
        simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]
      have hz : ∀ k, toRealVec (fun _ : Fin k => (FloatOps.zero : 𝕋)) = 0 := fun k => by
        funext i
        simp [toRealVec, toReal_zero]
      have h00 : ∀ k, (0 : Vec ℝ k) - toRealVec (fun _ : Fin k => (FloatOps.zero : 𝕋))
          ∈ (Interval.point fun _ : Fin k => (FloatOps.zero : 𝕋)).construct := fun k => by
        rw [hz k, sub_zero, ← hz k]
        exact Interval.mem_point _
      -- the identity kernel selects coordinates, and ReLU is the identity on an image
      have hsel : ∀ {k : ℕ} (g : Fin k → Fin n),
          (1 : Mat ℝ n n).submatrix g id *ᵥ x = x ∘ g := fun g => by
        funext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
      have hrelu : (fun i => Real.relu (((1 : Mat ℝ n n) *ᵥ x + 0) i)) = x := by
        funext i
        simp [Real.relu, hX x hx i]
      -- line 2's look-ahead box holds `x`, so its bucket `B` holds `x`'s merged pixels
      have hxI : x ∈ I_m1.construct := by
        have h := (Layer.activation_sound (S := Interval 𝕋) hR).enclose_outer _ _
          (Layer.linearWithError_mem (S := Interval 𝕋) (diagonalBlock fun _ => FloatOps.one)
            (Interval.construct_subset_nonemptyHull _ (h00 n)) I_X hx)
        rwa [hId, hrelu] at h
      set w := x ∘ part.right
      have hw : w ∈ (⟨I_m1.inf ∘ part.right, I_m1.sup ∘ part.right⟩ : Interval 𝕋 _).construct :=
        fun i => hxI (part.right i)
      -- and line 3's `H_{-2}` holds its surviving pixels
      have hxl : x ∘ part.left ∈ construct (ofInterval (S := S)
          ((((ReducedLinear.identity (𝕋 := 𝕋) n).mergeRows part).toLayer
            (S := Interval 𝕋)).enclose I_X)) := by
        apply ofInterval_outer
        have hc : (0 : Vec ℝ n) ∘ part.left
            - toRealVec ((ReducedLinear.identity (𝕋 := 𝕋) n).mergeRows part).b
            ∈ ((ReducedLinear.identity (𝕋 := 𝕋) n).mergeRows part).I'.construct :=
          fun i => h00 n (part.left i)
        have h := Layer.linearWithError_mem (S := Interval 𝕋)
          ((ReducedLinear.identity (𝕋 := 𝕋) n).mergeRows part).W
          (Interval.construct_subset_nonemptyHull _ hc) I_X hx
        have hW : toRealMat ((ReducedLinear.identity (𝕋 := 𝕋) n).mergeRows part).W
            = (1 : Mat ℝ n n).submatrix part.left id := by
          show (toRealMat (diagonalBlock fun _ : Fin n => (FloatOps.one : 𝕋))).submatrix _ _ = _
          rw [hId]
        rwa [hW, hsel, show (0 : Vec ℝ n) ∘ part.left = 0 from rfl, add_zero] at h
      -- `Φ'_org` frozen at `w`: an instance whose bias at `L̂_1` is `c_1 + W_1(·,B) w`
      set W1 := toRealMat L_1.W
      have hc' : c1 + W1.submatrix id part.right *ᵥ w - toRealVec (L_1.mergeCols part I_m1).b
          ∈ (L_1.mergeCols part I_m1).I'.construct := by
        have hsplit : c1 + W1.submatrix id part.right *ᵥ w - toRealVec L_1.b
            = (c1 - toRealVec L_1.b) + W1.submatrix id part.right *ᵥ w := by abel
        show c1 + W1.submatrix id part.right *ᵥ w - toRealVec L_1.b ∈ _
        rw [hsplit]
        exact Interval.plus_outer _ _ (Set.add_mem_add hc1
          (Interval.mtimes_outer (L_1.W.submatrix id part.right) _ ⟨w, hw, rfl⟩))
      have hΦ' := ReducibleNetwork.Instance.cons (c := 0) (R := R_relu) (hτ := hσ_relu)
        (B := .dynamic) (L := ReducedLinear.identity _) hR (h00 _)
        (ReducibleNetwork.Instance.cons (c := c1 + W1.submatrix id part.right *ᵥ w) (R := L_2)
          (hτ := hσ_2) (B := B_2) hR2 hc' hrest1 (fun _ => rfl)) (fun _ => rfl)
      obtain ⟨hout, rfl⟩ := reduceOnTheFly_outer hΦ' hrun2
      have hmem := hout ⟨x ∘ part.left, hxl, rfl⟩
      -- which at `x`'s own survivors is `Φ_org` at `x`, the ReLU and the kernel being identities
      have hrelu' : (fun i => Real.relu (((1 : Mat ℝ _ _) *ᵥ (x ∘ part.left) + 0) i))
          = x ∘ part.left := by
        funext i
        simp [Real.relu, hX x hx (part.left i)]
      have hval : W1.submatrix id part.left *ᵥ (x ∘ part.left)
          + (c1 + W1.submatrix id part.right *ᵥ w) = W1 *ᵥ x + c1 := by
        rw [part.mulVec_split₂ W1 x]
        abel
      have key : (fun i => σ₂ ((W1 *ᵥ x + c1) i))
          = fun i => σ₂ ((toRealMat (L_1.mergeCols part I_m1).W *ᵥ (fun i => Real.relu
              ((toRealMat (ReducedLinear.identity (𝕋 := 𝕋) _).W *ᵥ (x ∘ part.left) + 0) i))
            + (c1 + W1.submatrix id part.right *ᵥ w)) i) := by
        rw [show toRealMat (ReducedLinear.identity (𝕋 := 𝕋) _).W = 1 from hId _, hrelu']
        show _ = fun i => σ₂ ((W1.submatrix id part.left *ᵥ (x ∘ part.left) + _) i)
        rw [hval]
      rw [hf1, key]
      exact hmem
    · exact absurd hrun (by simp)
end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
