import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.NN.Float.ReduceOnTheFly
import CORALean.NN.Operations.Enclose

/-!
# [1, Alg. 2] over a floating-point scalar is sound

Every instance of the network maps the input set into the output set `Y` the float algorithm
computed, and `Y` is the reduced network's own enclosure. The argument is the exact layer's
`ReducesAt` derivation read pointwise: at `k < κ` the look-ahead box `I_k`, computed at the
float interval family, holds the merged neurons' values; the survivors pass the trimmed layers;
and the rest of the loop is invoked at the bias the merged values freeze layer `k+1` at, which
the box `mergeCols` gives it holds — `Interval.mtimes` and `Interval.plus` round outward.

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

open Matrix ContSet IntervalOuter SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {tol : 𝕋} {fuel : ℕ} {ρ : 𝕋}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 10, 11 and 13 are the reduced layers' `enclose`, so `Y = H_κ` is `Φ̂_ρ`'s. -/
theorem aux_reduceOnTheFlyFrom_enclose :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork 𝕋 n₁ m) (H : S n) (L : ReducedLinear 𝕋 n n₁)
      (R : Relaxation 𝕋) (B : MergeBuckets 𝕋) {Φhat : ReducibleNetwork 𝕋 n m} {Y : S m},
      reduceOnTheFlyFrom tol fuel ρ H L R B rest = some (Φhat, Y) →
        Y = Φhat.toNetwork.enclose H
  | _, _, _, .nil, H, L, R, B, Φhat, Y, hrun => by
      simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      rfl
  | _, _, _, .cons L1 R1 B1 rest1, H, L, R, B, Φhat, Y, hrun => by
      simp only [reduceOnTheFlyFrom] at hrun
      split at hrun
      · exact absurd hrun (by simp)
      · split at hrun
        · exact absurd hrun (by simp)
        · rename_i hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          have hY := aux_reduceOnTheFlyFrom_enclose rest1 _ _ R1 B1 hrec
          exact hY

/-- The loop from one `k` on, for every bias `c` the pending layer `L̂_{k-1}`'s box admits. -/
theorem aux_reduceOnTheFlyFrom_outer :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork 𝕋 n₁ m) (H : S n) (L : ReducedLinear 𝕋 n n₁)
      (R : Relaxation 𝕋) (B : MergeBuckets 𝕋) {σ : ℝ → ℝ} (_hR : R.Sound σ) {c : Vec ℝ n₁}
      (_hc : c - toRealVec L.b ∈ L.I'.construct) {h : Vec ℝ n₁ → Vec ℝ m}
      (_hrest : rest.Instance h) {Φhat : ReducibleNetwork 𝕋 n m} {Y : S m},
      reduceOnTheFlyFrom tol fuel ρ H L R B rest = some (Φhat, Y) →
      ∀ x ∈ construct H, h (fun i => σ ((toRealMat L.W *ᵥ x + c) i)) ∈ construct Y
  | _, _, _, .nil, H, L, R, B, σ, hR, c, hc, _, hrest, Φhat, Y, hrun => by
      cases hrest with
      | nil hid =>
        simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        -- k = κ: the pending layer's box holds `c`, and the last activation encloses `σ`
        intro x hx
        rw [hid]
        exact (Layer.activation_sound hR).enclose_outer _ _
          (Layer.linearWithError_mem L.W hc H hx)
  | _, _, _, .cons L1 R1 B1 rest1, H, L, R, B, σ, hR, c, hc, _, hrest, Φhat, Y, hrun => by
      cases hrest with
      | @cons _ _ _ _ c1 _ σ1 _ _ h1 _ hR1 hc1 hrest1 hf1 =>
        simp only [reduceOnTheFlyFrom] at hrun
        split at hrun
        · exact absurd hrun (by simp)
        · rename_i B_kδ _
          split at hrun
          · exact absurd hrun (by simp)
          · rename_i Φrest Yrest hrec
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            set part := Partition.ofPred fun i => B_kδ i = true
            set I_k := (Layer.activation (S := Interval 𝕋) R).enclose
              ((L.toLayer (S := Interval 𝕋)).enclose (interval H))
            -- a point of `H_{k-2}`, and its value `v` after the exact layers `k-1` and `k`
            intro x hx
            set v : Vec ℝ _ := fun i => σ ((toRealMat L.W *ᵥ x + c) i) with hv
            -- line 5's box holds the merged neurons' values, computed at the float boxes
            have hvk : v ∈ construct I_k :=
              (Layer.activation_sound (S := Interval 𝕋) hR).enclose_outer _ _
                (Layer.linearWithError_mem (S := Interval 𝕋) L.W hc _ (interval_outer H hx))
            have hw : v ∘ part.right
                ∈ (⟨I_k.inf ∘ part.right, I_k.sup ∘ part.right⟩ : Interval 𝕋 _).construct :=
              fun i => hvk (part.right i)
            -- the survivors pass the trimmed layer `k-1`, then the activation
            have hrow : toRealMat (L.mergeRows part).W *ᵥ x + c ∘ part.left
                = (toRealMat L.W *ᵥ x + c) ∘ part.left := by
              funext i
              simp [Matrix.mulVec, dotProduct, toRealMat, ReducedLinear.mergeRows]
            have hcl : c ∘ part.left - toRealVec (L.mergeRows part).b
                ∈ (L.mergeRows part).I'.construct := fun i => hc (part.left i)
            have hA1 := Layer.linearWithError_mem (S := S) (L.mergeRows part).W hcl H hx
            rw [hrow] at hA1
            have hA2 := (Layer.activation_sound (S := S) hR).enclose_outer _ _ hA1
            -- the bucket's own values freeze layer `k+1`'s bias inside `mergeCols`'s box
            set W1 := toRealMat L1.W
            have hc' : c1 + W1.submatrix id part.right *ᵥ (v ∘ part.right)
                - toRealVec (L1.mergeCols part I_k).b ∈ (L1.mergeCols part I_k).I'.construct := by
              have hsplit : c1 + W1.submatrix id part.right *ᵥ (v ∘ part.right) - toRealVec L1.b
                  = (c1 - toRealVec L1.b) + W1.submatrix id part.right *ᵥ (v ∘ part.right) := by
                abel
              show _ - toRealVec L1.b ∈ _
              rw [hsplit]
              exact Interval.plus_outer _ _ (Set.add_mem_add hc1
                (Interval.mtimes_outer (L1.W.submatrix id part.right) _ ⟨_, hw, rfl⟩))
            have hval : W1 *ᵥ v + c1 = W1.submatrix id part.left *ᵥ (v ∘ part.left)
                + (c1 + W1.submatrix id part.right *ᵥ (v ∘ part.right)) := by
              rw [part.mulVec_split₂ W1 v]
              abel
            rw [hf1, hval]
            exact aux_reduceOnTheFlyFrom_outer rest1 _ _ R1 B1 hR1 hc' hrest1 hrec _ hA2


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] over floats: every instance of `Φ` maps `X` into the `Y` computed, and `Y` is
the reduced network's enclosure of `X`. -/
theorem reduceOnTheFly_outer {n m : ℕ} {X : S n} {Φ Φhat : ReducibleNetwork 𝕋 n m} {Y : S m}
    {f : Vec ℝ n → Vec ℝ m} (hΦ : Φ.Instance f)
    (hrun : reduceOnTheFly tol fuel X ρ Φ = some (Φhat, Y)) :
    f '' construct X ⊆ construct Y ∧ Y = Φhat.toNetwork.enclose X := by -- --- PROOF ---
  cases hΦ with
  | nil hid =>
    simp only [reduceOnTheFly, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨by rintro _ ⟨x, hx, rfl⟩; rw [hid]; exact hx, rfl⟩
  | @cons _ _ _ L c R _ B rest _ _ hR hc hrest hf =>
    refine ⟨?_, aux_reduceOnTheFlyFrom_enclose rest X L R B hrun⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hf]
    exact aux_reduceOnTheFlyFrom_outer rest X L R B hR hc hrest hrun x hx

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
