module

public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubsetNonemptyHull
public import CORALean.NN.Layers.Theorems.ActivationEncloses
public import CORALean.NN.Layers.Theorems.LinearWithErrorMem
public import CORALean.NN.Operations.Enclose
public import CORALean.NN.Operations.ReduceOnTheFly
public import CORALean.NN.Operations.ReducibleNetworkToNetwork
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# [1, Alg. 2] is sound

Every instance of the network maps the input set into the output set `Y` the algorithm
computed, at any scalar, and `Y` is the reduced network's own enclosure. The argument is
`ReducesAt`'s derivation read pointwise: at `k < κ` the look-ahead box `I_k`, computed at the
interval family, holds the merged neurons' values; the survivors pass the trimmed layers; and
the rest of the loop is invoked at the bias the merged values freeze layer `k+1` at, which the
box `mergeCols` gives it holds — `Interval.mtimes` and `Interval.plus` round outward. It holds
at every `le`, `tol`, `fuel` and `ρ`: which buckets come out never matters to soundness.

## Inputs
* `n` – input width
* `m` – output width
* `X` – input set
* `Φ` – reducible network
* `f` – map the network is an instance of

## Hypotheses
* `hΦ` – the network is an instance of the map

## Conclusion
* the output set holds the map's image and is the reduced network's enclosure

## References

* [1] [T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for Formal Verification".
      Transactions on Machine Learning Research,
      2025.](../../../../references/2023/ladner-tmlr-network-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Float Float.IntervalOuter Float.SoundFloatArithmetic
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [IntervalOuter S 𝕋] [OfInterval S 𝕋] {le : 𝕋 → 𝕋 → Bool} {tol : 𝕋}
  {fuel : ℕ} {ρ : 𝕋}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 10, 11 and 13 are the reduced layers' `enclose`, so `Y = H_κ` is `Φ̂_ρ`'s. -/
private theorem aux_reduceOnTheFlyFrom_enclose :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork 𝕋 n₁ m) (H : S n) (L : ReducedLinear 𝕋 n n₁)
      (R : Relaxation 𝕋) (hτ : ∃ σ : ℝ → ℝ, R.Encloses σ) (B : MergeBuckets 𝕋)
      {Φhat : ReducibleNetwork 𝕋 n m} {Y : S m},
      reduceOnTheFlyFrom le tol fuel ρ H L R hτ B rest = some (Φhat, Y) →
        Y = Φhat.toNetwork.enclose H
  | _, _, _, .nil, H, L, R, hτ, B, Φhat, Y, hrun => by
      simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      rfl
  | _, _, _, .cons L1 R1 hτ1 B1 rest1, H, L, R, hτ, B, Φhat, Y, hrun => by
      simp only [reduceOnTheFlyFrom] at hrun
      split at hrun
      · exact absurd hrun (by simp)
      · split at hrun
        · exact absurd hrun (by simp)
        · rename_i hrec
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          have hY := aux_reduceOnTheFlyFrom_enclose rest1 _ _ R1 hτ1 B1 hrec
          exact hY

/-- The loop from one `k` on, for every bias `c` the pending layer `L̂_{k-1}`'s box admits. -/
private theorem aux_reduceOnTheFlyFrom_outer :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork 𝕋 n₁ m) (H : S n) (L : ReducedLinear 𝕋 n n₁)
      (R : Relaxation 𝕋) (hτ : ∃ σ : ℝ → ℝ, R.Encloses σ) (B : MergeBuckets 𝕋)
      {σ : ℝ → ℝ} (_hR : R.Encloses σ) {c : Vec ℝ n₁}
      (_hc : c - toRealVec L.b ∈ L.I'.construct) {h : Vec ℝ n₁ → Vec ℝ m}
      (_hrest : rest.IsInstance h) {Φhat : ReducibleNetwork 𝕋 n m} {Y : S m},
      reduceOnTheFlyFrom le tol fuel ρ H L R hτ B rest = some (Φhat, Y) →
      ∀ x ∈ construct H, h (fun i => σ ((toRealMat L.W *ᵥ x + c) i)) ∈ construct Y
  | _, _, _, .nil, H, L, R, hτ, B, σ, hR, c, hc, _, hrest, Φhat, Y, hrun => by
      cases hrest with
      | nil hid =>
        simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        -- k = κ: the pending layer's box holds `c`, and the last activation encloses `σ`
        intro x hx
        rw [hid]
        exact (Layer.activation_encloses hR).enclose_outer _ _
          (Layer.linearWithError_mem L.W (Interval.construct_subset_nonemptyHull _ hc) H hx)
  | _, _, _, .cons L1 R1 hτ1 B1 rest1, H, L, R, hτ, B, σ, hR, c, hc, _, hrest, Φhat, Y, hrun => by
      cases hrest with
      | @cons _ _ _ _ c1 _ _ σ1 _ _ h1 _ hR1 hc1 hrest1 hf1 =>
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
            set I_k := (Layer.activation (S := ℐ𝒱[𝕋]) R).enclose
              ((L.toLayer (S := ℐ𝒱[𝕋])).enclose (interval H))
            -- a point of `H_{k-2}`, and its value `v` after the exact layers `k-1` and `k`
            intro x hx
            set v : Vec ℝ _ := fun i => σ ((toRealMat L.W *ᵥ x + c) i) with hv
            -- line 5's box holds the merged neurons' values, computed at the float boxes
            have hvk : v ∈ construct I_k :=
              (Layer.activation_encloses (S := ℐ𝒱[𝕋]) hR).enclose_outer _ _
                (Layer.linearWithError_mem (S := ℐ𝒱[𝕋]) L.W
                  (Interval.construct_subset_nonemptyHull _ hc) _ (interval_outer H hx))
            have hw : v ∘ part.right
                ∈ (⟨I_k.inf ∘ part.right, I_k.sup ∘ part.right⟩ : Interval (Vec 𝕋 _)).construct :=
              fun i => hvk (part.right i)
            -- the survivors pass the trimmed layer `k-1`, then the activation
            have hrow : toRealMat (L.mergeRows part).W *ᵥ x + c ∘ part.left
                = (toRealMat L.W *ᵥ x + c) ∘ part.left := by
              funext i
              simp [Matrix.mulVec, dotProduct, toRealMat, ReducedLinear.mergeRows]
            have hcl : c ∘ part.left - toRealVec (L.mergeRows part).b
                ∈ (L.mergeRows part).I'.construct := fun i => hc (part.left i)
            have hA1 := Layer.linearWithError_mem (S := S) (L.mergeRows part).W
              (Interval.construct_subset_nonemptyHull _ hcl) H hx
            rw [hrow] at hA1
            have hA2 := (Layer.activation_encloses (S := S) hR).enclose_outer _ _ hA1
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
            exact aux_reduceOnTheFlyFrom_outer rest1 _ _ R1 hτ1 B1 hR1 hc' hrest1 hrec _ hA2


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: every instance of `Φ` maps `X` into the `Y` computed, and `Y` is
the reduced network's enclosure of `X`. -/
theorem reduceOnTheFly_outer {n m : ℕ} {X : S n} {Φ : ReducibleNetwork 𝕋 n m}
    {f : Vec ℝ n → Vec ℝ m} (hΦ : Φ.IsInstance f) : -- --- CONCL ---
    ∀ Φhat Y, (Φhat, Y) ∈ reduceOnTheFly le tol fuel X ρ Φ →
      f '' construct X ⊆ construct Y ∧ Y = Φhat.toNetwork.enclose X := by -- --- PROOF ---
  intro Φhat Y (hrun : reduceOnTheFly le tol fuel X ρ Φ = some (Φhat, Y))
  cases hΦ with
  | nil hid =>
    simp only [reduceOnTheFly, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨by rintro _ ⟨x, hx, rfl⟩; rw [hid]; exact hx, rfl⟩
  | @cons _ _ _ L c R hτ _ B rest _ _ hR hc hrest hf =>
    refine ⟨?_, aux_reduceOnTheFlyFrom_enclose rest X L R hτ B hrun⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hf]
    exact aux_reduceOnTheFlyFrom_outer rest X L R hτ B hR hc hrest hrun x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
