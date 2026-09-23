import CORALean.NN.CompressionPreprocessing
import CORALean.NN.Theorems.ReduceOnTheFlyReducesAt
import CORALean.NN.Theorems.ReducesAtOuter

/-!
# [1, Alg. 3] is sound on a nonnegative image

[1, Cor. 1]'s compression network computes the identity on `ℝ₊ⁿ`, so the output set of
[1, Alg. 3] holds `Φ_org`'s exact image of every nonnegative `x ∈ I_X`. The pixels line 2
keeps are in `H_{-2}`, the identity kernel selecting them; the pixels it merges are in its
look-ahead box `I_{-1}`, ReLU leaving them unchanged; and `Φ'_org` with its first linear
layer's bias frozen at those merged pixels is an instance of `Φ'_org` that computes `Φ_org`
at `x` from `x`'s surviving pixels — so `reduceOnTheFly_reducesAt` at line 5 does the rest.
The nonnegativity is [1, Cor. 1]'s `X ⊂ ℝ₊`, without which the ReLU is not the identity.

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

open Matrix ContSet IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3]: on a nonnegative image box `I_X`, the output set holds `Φ_org`'s exact image,
at every instance of `Φ_org`. -/
theorem compressionPreprocessing_outer {le : ℝ → ℝ → Bool} {tol : ℝ} {fuel : ℕ}
    {R_relu : Relaxation relu} {n n₁ m : ℕ} {I_X : Interval (Vec ℝ n)}
    (hX : ∀ x ∈ construct I_X, ∀ i, 0 ≤ x i) {L_1 : ReducedLinear n n₁} {σ₂ : ℝ → ℝ}
    {L_2 : Relaxation σ₂} {B_2 : MergeBuckets ℝ} {rest : ReducibleNetwork n₁ m}
    {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hΦ : (ReducibleNetwork.cons L_1 L_2 B_2 rest).Instance nn f) {ρ : ℝ} {Y : S m}
    (hrun : compressionPreprocessing le tol fuel R_relu I_X L_1 L_2 B_2 rest ρ = some Y) :
    f '' construct I_X ⊆ construct Y := by -- --- PROOF ---
  cases hΦ with
  | @cons _ _ _ _ c1 _ _ _ _ nn1 h1 _ hc1 hrest1 hf1 =>
  simp only [compressionPreprocessing] at hrun
  split at hrun
  · exact absurd hrun (by simp)
  · rename_i B_m1δ _
    split at hrun
    · rename_i Φhat Y' hrun2
      cases hrun
      set part := Partition.ofPred fun i => B_m1δ i = true
      set I_m1 := (Layer.activation (S := ℐ𝒱) R_relu).enclose
        (((ReducedLinear.identity n).toLayer (S := ℐ𝒱)).enclose I_X)
      rintro _ ⟨x, hx, rfl⟩
      -- the identity kernel selects coordinates, and ReLU is the identity on an image
      have hsel : ∀ {k : ℕ} (g : Fin k → Fin n),
          (1 : Mat ℝ n n).submatrix g id *ᵥ x = x ∘ g := fun g => by
        funext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
      have hrelu : (fun i => relu (((1 : Mat ℝ n n) *ᵥ x + 0) i)) = x := by
        funext i
        simp [relu, hX x hx i]
      have h00 : ∀ {k : ℕ}, (0 : Vec ℝ k) - 0 ∈ construct (Interval.point (0 : Vec ℝ k)) :=
        fun {k} => (sub_self (0 : Vec ℝ k)).symm ▸ Interval.mem_point 0
      -- line 2's look-ahead box holds `x`, so its bucket `B` holds `x`'s merged pixels
      have hxI : x ∈ construct I_m1 := by
        have h := (Layer.activation_sound (S := ℐ𝒱) R_relu).enclose_outer _ _
          (Layer.linearWithError_mem (S := ℐ𝒱) (1 : Mat ℝ n n) h00 I_X hx)
        rwa [hrelu] at h
      set w := x ∘ part.right
      have hw : w ∈ construct
          (⟨I_m1.inf ∘ part.right, I_m1.sup ∘ part.right⟩ : Interval (Vec ℝ _)) :=
        fun i => hxI (part.right i)
      -- and line 3's `H_{-2}` holds its surviving pixels
      have hxl : x ∘ part.left ∈ construct (ofInterval (S := S)
          ((((ReducedLinear.identity n).mergeRows part).toLayer (S := ℐ𝒱)).enclose I_X)) := by
        apply ofInterval_outer
        have hc : (0 : Vec ℝ n) ∘ part.left - (0 : Vec ℝ n) ∘ part.left
            ∈ construct ((ReducedLinear.identity n).mergeRows part).I' :=
          fun i => h00 (part.left i)
        have h := Layer.linearWithError_mem (S := ℐ𝒱) ((1 : Mat ℝ n n).submatrix part.left id)
          hc I_X hx
        rwa [hsel, show (0 : Vec ℝ n) ∘ part.left = 0 from rfl, add_zero] at h
      -- `Φ'_org` frozen at `w`: an instance whose bias at `L̂_1` is `c_1 + W_1(·,B) w`
      have hc' : c1 + L_1.W.submatrix id part.right *ᵥ w - (L_1.mergeCols part I_m1).b
          ∈ construct (L_1.mergeCols part I_m1).I' := by
        have hsplit : c1 + L_1.W.submatrix id part.right *ᵥ w - L_1.b
            = (c1 - L_1.b) + L_1.W.submatrix id part.right *ᵥ w := by abel
        show c1 + L_1.W.submatrix id part.right *ᵥ w - L_1.b ∈ _
        rw [hsplit]
        exact Interval.plus_outer _ _ (Set.add_mem_add hc1
          (Interval.mtimes_outer _ _ ⟨w, hw, rfl⟩))
      have hΦ' := ReducibleNetwork.Instance.cons (S := S) (c := 0) (R := R_relu)
        (B := .dynamic) (L := ReducedLinear.identity _) h00
        (ReducibleNetwork.Instance.cons (c := c1 + L_1.W.submatrix id part.right *ᵥ w) (R := L_2)
          (B := B_2) hc' hrest1 (fun _ => rfl)) (fun _ => rfl)
      obtain ⟨hred, rfl⟩ := reduceOnTheFly_reducesAt hΦ' hrun2
      have hout := NeuralNetwork.reducesAt_outer hred ⟨x ∘ part.left, hxl, rfl⟩
      -- which at `x`'s own survivors is `Φ_org` at `x`, the ReLU and the kernel being identities
      have hrelu' : (fun i => relu (((1 : Mat ℝ _ _) *ᵥ (x ∘ part.left) + 0) i))
          = x ∘ part.left := by
        funext i
        simp [relu, hX x hx (part.left i)]
      have hval : L_1.W.submatrix id part.left *ᵥ (x ∘ part.left)
          + (c1 + L_1.W.submatrix id part.right *ᵥ w) = L_1.W *ᵥ x + c1 := by
        rw [part.mulVec_split₂ L_1.W x]
        abel
      rw [hf1]
      simp only [ReducedLinear.mergeCols, ReducedLinear.identity] at hout
      rw [hrelu', hval] at hout
      exact hout
    · exact absurd hrun (by simp)
end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
