import CORALean.ContSet.Interval.Real.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
import CORALean.NN.ReduceOnTheFly
import CORALean.NN.Theorems.ReducesAtCongr

/-!
# What [1, Alg. 2] returns is a reduction, and computes its own output set

The derivation follows the loop step for step: at `k < κ` a `freeze` — the look-ahead box `I_k`
bounds every point of `H_{k-2}` pushed through `L̂_{k-1}` and `L_k`, which is its hypothesis,
and the rest of the loop, run once, serves every value `w` of the bucket because the reduced
layer `k+1` carries all of them in its box — and at `k = κ` a `widen` and a `keep`.

The invariant is over the pending layer `L̂_{k-1}`: whatever bias `c` within its box the
original is frozen at. Line 13's `Y` is `Φ̂_ρ`'s own enclosure of `X`, since lines 10 and 11
are exactly the reduced layers' `enclose`, so [1, Thm. 1] speaks of the set the loop computed.

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

open Matrix ContSet IntervalOuter

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]
  {le : ℝ → ℝ → Bool} {tol : ℝ} {fuel : ℕ} {ρ : ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 10, 11 and 13 are the reduced layers' `enclose`, so `Y = H_κ` is `Φ̂_ρ`'s. -/
theorem aux_reduceOnTheFlyFrom_enclose :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork n₁ m) (H : S n) (L : ReducedLinear n n₁)
      {σ : ℝ → ℝ} (R : Relaxation σ) (B : MergeBuckets ℝ) {Φhat : ReducibleNetwork n m}
      {Y : S m}, reduceOnTheFlyFrom le tol fuel ρ H L R B rest = some (Φhat, Y) →
        Y = Φhat.toNetwork.enclose H
  | _, _, _, .nil, H, L, _, R, B, Φhat, Y, hrun => by
      simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      rfl
  | _, _, _, .cons L1 R1 B1 rest1, H, L, _, R, B, Φhat, Y, hrun => by
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

/-- The loop from one `k` on reduces the original frozen at any bias `c` the box of the
pending layer `L̂_{k-1}` admits. -/
theorem aux_reduceOnTheFlyFrom_reducesAt :
    ∀ {n n₁ m : ℕ} (rest : ReducibleNetwork n₁ m) (H : S n) (L : ReducedLinear n n₁)
      {σ : ℝ → ℝ} (R : Relaxation σ) (B : MergeBuckets ℝ) {c : Vec ℝ n₁}
      (_hc : c - L.b ∈ construct L.I') {nn : NeuralNetwork S n₁ m} {h : Vec ℝ n₁ → Vec ℝ m}
      (_hrest : rest.Instance nn h) {Φhat : ReducibleNetwork n m} {Y : S m},
      reduceOnTheFlyFrom le tol fuel ρ H L R B rest = some (Φhat, Y) →
      NeuralNetwork.ReducesAt H (.cons (Layer.linear L.W c) (.cons (Layer.activation R) nn))
        Φhat.toNetwork (fun x => h (fun i => σ ((L.W *ᵥ x + c) i)))
  | _, _, _, .nil, H, L, _, R, B, c, hc, _, _, hrest, Φhat, Y, hrun => by
      cases hrest with
      | nil hid =>
        simp only [reduceOnTheFlyFrom, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        -- k = κ: the pending layer's box holds `c`, and the last activation is kept
        exact .widen H L.W c L.b L.I' hc (fun _ => rfl)
          (.keep _ (Layer.activation R) (Layer.activation_sound R) (fun _ => rfl) (.nil _ hid))
  | _, _, _, .cons L1 (σ := σ1) R1 B1 rest1, H, L, σ, R, B, c, hc, _, _, hrest, _, _, hrun => by
      cases hrest with
      | @cons _ _ _ _ c1 _ _ _ _ nn1 h1 _ hc1 hrest1 hf1 =>
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
            set I_k := (Layer.activation (S := ℐ𝒱) R).enclose
              ((L.toLayer (S := ℐ𝒱)).enclose (interval H))
            -- line 5's box bounds the exact layer `k` at every point that reaches it
            have hY : ∀ x ∈ construct H, (fun i => σ ((L.W *ᵥ x + c) i)) ∈ construct I_k :=
              fun x hx => (Layer.activation_sound (S := ℐ𝒱) R).enclose_outer _ _
                (Layer.linearWithError_mem (S := ℐ𝒱) L.W hc _ (interval_outer H hx))
            refine .freeze H part L.W c L.b L.I' hc R L1.W c1 I_k hY
              (h := fun y => h1 (fun i => σ1 (y i))) (fun x => hf1 _) fun w hw => ?_
            -- the frozen bias lies in the box `mergeCols` gives layer `k+1`
            have hc' : c1 + L1.W.submatrix id part.right *ᵥ w - (L1.mergeCols part I_k).b
                ∈ construct (L1.mergeCols part I_k).I' := by
              have hsplit : c1 + L1.W.submatrix id part.right *ᵥ w - L1.b
                  = (c1 - L1.b) + L1.W.submatrix id part.right *ᵥ w := by abel
              show c1 + L1.W.submatrix id part.right *ᵥ w - L1.b ∈ _
              rw [hsplit]
              exact Interval.plus_outer _ _ (Set.add_mem_add hc1
                (Interval.mtimes_outer _ _ ⟨w, hw, rfl⟩))
            exact aux_reduceOnTheFlyFrom_reducesAt rest1 _ _ R1 B1 hc' hrest1 hrec


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] returns a reduction of every instance of `Φ`, and `Y` is its enclosure of `X`. -/
theorem reduceOnTheFly_reducesAt {n m : ℕ} {X : S n} {Φ Φhat : ReducibleNetwork n m} {Y : S m}
    {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m} (hΦ : Φ.Instance nn f)
    (hrun : reduceOnTheFly le tol fuel X ρ Φ = some (Φhat, Y)) :
    NeuralNetwork.ReducesAt X nn Φhat.toNetwork f
      ∧ Y = Φhat.toNetwork.enclose X := by -- --- PROOF ---
  cases hΦ with
  | nil hid =>
    simp only [reduceOnTheFly, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨.nil X hid, rfl⟩
  | @cons _ _ _ L c _ R B rest _ _ _ hc hrest hf =>
    exact ⟨(aux_reduceOnTheFlyFrom_reducesAt rest X L R B hc hrest hrun).congr hf,
      aux_reduceOnTheFlyFrom_enclose rest X L R B hrun⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
