import CORALean.NN.Operations.NetworkConvergent
import CORALean.NN.Operations.PropagateAt
import CORALean.NN.Schedule

/-!
# Refinement converges to the exact output set

The other half of `PropagateAtOuter`: the image is always inside the propagated
set, and some schedule brings the propagated set inside the image widened by any
`ε`. Together they say refinement drives the enclosure onto the output set, and
neither statement needs a distance between sets.

The induction is the network's own, and the residual is what travels: the head
layer is refined until its residual is `ε / (2 (K + 1))`, the tail carries that
to at most `ε / 2`, and the tail's own schedule is asked for the other half. `K`
is where a Lipschitz hypothesis is unavoidable — a later layer amplifies an
earlier layer's residual, so a per-layer limit alone says nothing at the output.

`ε / (2 (K + 1))` rather than `ε / (2 K)`: `K` may be zero, and a division by it
would be the one case the statement is easiest in.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A schedule built by `Schedule.cons` runs its head layer at exactly the
pattern it was built from, which is what lets the induction hand one down. -/
theorem aux_propagateAt_cons (L : RefinableLayer S n m) (rest : RefinableNetwork S m k)
    (t : OrderPattern n) (sch : Schedule) (X : S n) :
    (RefinableNetwork.cons L rest).propagateAt (Schedule.cons t sch) X
      = rest.propagateAt sch (L.propagate t X) := by -- --- PROOF ---
  show rest.propagateAt (Schedule.tail (Schedule.cons t sch))
    (L.propagate (Schedule.head (Schedule.cons t sch) n) X) = _
  rw [Schedule.head_cons]
  rfl

/-- Two inflations compose into one: a residual left by the head layer and the
error the tail adds are both paid out of the same ball. -/
theorem aux_subset_inflate_trans {E C B : Set (Vec ℝ m)} {δ₁ δ₂ ε : ℝ}
    (hC : C ⊆ E + Metric.closedBall 0 δ₁) (hB : B ⊆ C + Metric.closedBall 0 δ₂)
    (hδ : δ₁ + δ₂ ≤ ε) : B ⊆ E + Metric.closedBall 0 ε := by -- --- PROOF ---
  intro y hy
  obtain ⟨c, hc, d₂, hd₂, rfl⟩ := hB hy
  obtain ⟨e, he, d₁, hd₁, rfl⟩ := hC hc
  rw [Metric.mem_closedBall, dist_zero_right] at hd₁ hd₂
  -- the two residuals travel together, and the triangle inequality is the whole cost
  have hball : d₁ + d₂ ∈ Metric.closedBall (0 : Vec ℝ m) ε := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (norm_add_le d₁ d₂) (le_trans (by linarith) hδ)
  have hmem := Set.add_mem_add he hball
  rwa [← add_assoc] at hmem

/-- A Lipschitz map carries an inflation to an inflation, the radius scaled:
this is how a residual left early reaches the output. -/
theorem aux_image_inflate_subset {k : ℕ} {f : Vec ℝ m → Vec ℝ k} {K : NNReal}
    (hK : LipschitzWith K f) (A : Set (Vec ℝ m)) (δ : ℝ) :
    f '' (A
      + Metric.closedBall 0 δ) ⊆ f '' A + Metric.closedBall 0 ((K : ℝ) * δ) := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, ha, d, hd, rfl⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hd
  -- the displacement is what the map moved, which the Lipschitz bound caps
  have hdist := hK.dist_le_mul (a + d) a
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left] at hdist
  have hball : f (a + d) - f a ∈ Metric.closedBall (0 : Vec ℝ k) ((K : ℝ) * δ) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans hdist (mul_le_mul_of_nonneg_left hd K.coe_nonneg)
  have hmem := Set.add_mem_add (show f a ∈ f '' A from ⟨a, ha, rfl⟩) hball
  have heq : f a + (f (a + d) - f a) = f (a + d) := by abel
  rwa [heq] at hmem


-- =======================================  MAIN THEOREM  ======================================= --

theorem RefinableNetwork.exists_schedule_propagateAt_subset :
    ∀ {n m : ℕ} (rn : RefinableNetwork S n m), rn.Convergent → ∀ (X : S n) (ε : ℝ), 0 < ε →
      ∃ sch : Schedule,
        construct (rn.propagateAt sch X) ⊆ rn.outputSet X + Metric.closedBall 0 ε
  | k, _, .nil, _, X, ε, hε => by
    refine ⟨fun _ _ => 0, fun y hy => ?_⟩
    -- the empty network propagates its input, and nothing has to be inflated
    have h0 : (0 : Vec ℝ k) ∈ Metric.closedBall (0 : Vec ℝ k) ε := by -- --- PROOF ---
      rw [Metric.mem_closedBall, dist_self]
      exact hε.le
    have hmem := Set.add_mem_add
      (show y ∈ (RefinableNetwork.nil : RefinableNetwork S k k).outputSet X from ⟨y, hy, rfl⟩) h0
    rwa [add_zero] at hmem
  | _, _, .cons L rest, hc, X, ε, hε => by
    obtain ⟨hL, ⟨K, hK⟩, hrest⟩ := hc
    have hKpos : (0 : ℝ) < 2 * ((K : ℝ) + 1) := by linarith [K.coe_nonneg]
    -- the head layer's residual, shrunk by what the tail will do to it
    obtain ⟨o, ho⟩ := hL X (ε / (2 * ((K : ℝ) + 1))) (div_pos hε hKpos)
    obtain ⟨sch, hsch⟩ := rest.exists_schedule_propagateAt_subset hrest
      (L.propagate o X) (ε / 2) (by linarith)
    refine ⟨Schedule.cons o sch, ?_⟩
    have hrad : (K : ℝ) * (ε / (2 * ((K : ℝ) + 1))) ≤ ε / 2 := by
      have hne : (2 * ((K : ℝ) + 1)) ≠ 0 := ne_of_gt hKpos
      have hcancel : (2 * ((K : ℝ) + 1)) * (ε / (2 * ((K : ℝ) + 1))) = ε := by field_simp
      nlinarith [K.coe_nonneg, (div_pos hε hKpos).le]
    have hset : rest.eval '' (L.eval '' construct X)
        = (RefinableNetwork.cons L rest).outputSet X := by
      rw [Set.image_image]
      rfl
    -- the head's residual, carried through the tail and paid at half the budget
    have himg : rest.eval '' construct (L.propagate o X)
        ⊆ (RefinableNetwork.cons L rest).outputSet X + Metric.closedBall 0 (ε / 2) := by
      refine subset_trans (Set.image_mono ho)
        (subset_trans (aux_image_inflate_subset hK _ _) ?_)
      rw [hset]
      exact Set.add_subset_add_left (Metric.closedBall_subset_closedBall hrad)
    rw [aux_propagateAt_cons]
    exact aux_subset_inflate_trans himg hsch (by linarith)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
