module

public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubsetNonemptyHull
public import CORALean.NN.Layers.Theorems.ActivationLayerOfSound
public import CORALean.NN.Theorems.Real.InstanceOfInstanceNetwork
public import CORALean.NN.Theorems.ReduceOnTheFlyOuter
public import CORALean.NN.Theorems.ReducesAtCongr

@[expose] public section

/-!
# What [1, Alg. 2] returns is a reduction, and computes its own output set

ℝ-only, as `ReducesAt` is: it relates networks of layers, and an instance's bias, which
`freeze` folds a real bucket value into, is stored only at `𝕋 := ℝ`. `reduceOnTheFly_outer`
is the inclusion at every scalar; this is the stronger statement [1, Thm. 1]'s proof makes.

The derivation follows the loop step for step: at `k < κ` a `freeze` — the look-ahead box `I_k`
bounds every point of `H_{k-2}` pushed through `L̂_{k-1}` and `L_k`, which is its hypothesis,
and the rest of the loop, run once, serves every value `w` of the bucket because the reduced
layer `k+1` carries all of them in its box — and at `k = κ` a `widen` and a `keep`. The
invariant is over the pending layer `L̂_{k-1}`: whatever bias `c` within its box the original is
frozen at. Line 13's `Y` is `Φ̂_ρ`'s own enclosure of `X`, as `reduceOnTheFly_outer` shows.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]
  {le : ℝ → ℝ → Bool} {tol : ℝ} {fuel : ℕ} {ρ : ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop from one `k` on reduces the original frozen at any bias `c` the box of the
pending layer `L̂_{k-1}` admits. -/
theorem aux_reduceOnTheFlyFrom_reducesAt :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork ℝ n₁ m) (H : S n) (L : ReducedLinear ℝ n n₁)
      (R : Relaxation ℝ) (hτ : ∃ σ : ℝ → ℝ, R.Sound σ) {σ : ℝ → ℝ} (_hR : R.Sound σ)
      (B : MergeBuckets ℝ)
      {c : Vec ℝ n₁} (_hc : c - L.b ∈ L.I'.construct) {nn : NeuralNetwork S n₁ m}
      {h : Vec ℝ n₁ → Vec ℝ m} (_hrest : rest.InstanceNetwork nn h)
      {Φhat : ReducibleNetwork ℝ n m} {Y : S m},
      reduceOnTheFlyFrom le tol fuel ρ H L R hτ B rest = some (Φhat, Y) →
      NeuralNetwork.ReducesAt H
        (.layer (LinearLayer.mk L.W c) (.layer (ActivationLayer.of (n := n₁) _hR) nn))
        Φhat.toNetwork (fun x => h (fun i => σ ((L.W *ᵥ x + c) i)))
  | _, _, _, .nil, H, L, R, hτ, σ, hR, B, c, hc, _, h, hrest, Φhat, Y, hrun => by
      cases hrest with
      | nil hid =>
        simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        -- k = κ: the pending layer's box holds `c`, and the last activation is kept
        exact .widen H L.W c L.b L.I' hc (h := fun y => h fun i => σ (y i)) (fun _ => rfl)
          (.keep _ (ActivationLayer.of hR) (ActivationLayer.of_sound (S := S) hR) (fun _ => rfl)
            (.nil _ hid))
  | _, _, _, .cons L1 R1 hτ1 B1 rest1, H, L, R, hτ, σ, hR, B, c, hc, _, _, hrest, _, _, hrun => by
      cases hrest with
      | @cons _ _ _ _ c1 _ _ σ1 _ _ nn1 h1 _ hR1 hc1 hrest1 hf1 =>
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
            set I_k := (Layer.activation (S := fun n => Float.Interval (Vec ℝ n)) R).enclose
              ((L.toLayer (S := fun n => Float.Interval (Vec ℝ n))).enclose
                (Float.IntervalOuter.interval H))
            -- line 5's box bounds the exact layer `k` at every point that reaches it
            have hY : ∀ x ∈ construct H, (fun i => σ ((L.W *ᵥ x + c) i)) ∈ construct I_k :=
              fun x hx =>
                (Layer.activation_sound (S := fun n => Float.Interval (Vec ℝ n)) hR).enclose_outer
                _ _ (Layer.linearWithError_mem (S := fun n => Float.Interval (Vec ℝ n)) L.W
                  (Float.Interval.construct_subset_nonemptyHull _ hc) _
                  (Float.IntervalOuter.interval_outer H hx))
            refine .freeze H part L.W c L.b L.I' hc R hR L1.W c1 I_k hY
              (h := fun y => h1 (fun i => σ1 (y i))) (fun x => hf1 _) fun w hw => ?_
            -- the frozen bias lies in the box `mergeCols` gives layer `k+1`
            have hc' : c1 + L1.W.submatrix id part.right *ᵥ w - (L1.mergeCols part I_k).b
                ∈ (L1.mergeCols part I_k).I'.construct := by
              have hsplit : c1 + L1.W.submatrix id part.right *ᵥ w - L1.b
                  = (c1 - L1.b) + L1.W.submatrix id part.right *ᵥ w := by abel
              show c1 + L1.W.submatrix id part.right *ᵥ w - L1.b ∈ _
              rw [hsplit]
              exact Float.Interval.plus_outer _ _ (Set.add_mem_add hc1
                (Float.Interval.mtimes_outer (L1.W.submatrix id part.right) _ ⟨w, hw, rfl⟩))
            exact aux_reduceOnTheFlyFrom_reducesAt rest1 _ _ R1 hτ1 hR1 B1 hc' hrest1 hrec


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] returns a reduction of every instance of `Φ`, and `Y` is its enclosure of `X`. -/
theorem reduceOnTheFly_reducesAt {n m : ℕ} {X : S n} {Φ Φhat : ReducibleNetwork ℝ n m}
    {Y : S m} {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m} (hΦ : Φ.InstanceNetwork nn f)
    (hrun : reduceOnTheFly le tol fuel X ρ Φ = some (Φhat, Y)) :
    NeuralNetwork.ReducesAt X nn Φhat.toNetwork f
      ∧ Y = Φhat.toNetwork.enclose X := by -- --- PROOF ---
  -- the output set is the reduced network's enclosure at every scalar
  refine ⟨?_, (reduceOnTheFly_outer (instance_of_instanceNetwork hΦ) hrun).2⟩
  cases hΦ with
  | nil hid =>
    simp only [reduceOnTheFly, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact .nil X hid
  | @cons _ _ _ L c R hτ _ B rest _ _ _ hR hc hrest hf =>
    exact (aux_reduceOnTheFlyFrom_reducesAt rest X L R hτ hR B hc hrest hrun).congr hf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
