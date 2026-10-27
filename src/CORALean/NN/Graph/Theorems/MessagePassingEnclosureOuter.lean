module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PointMemConstruct
public import CORALean.NN.Graph.Operations.AdjAt
public import CORALean.NN.Graph.Operations.Degree
public import CORALean.NN.Graph.Operations.DegreeAt
public import CORALean.NN.Graph.Operations.MessagePassing
public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import CORALean.NN.Graph.Theorems.SmulEdgeHalf
public import CORALean.NN.Graph.Theorems.SqrtAffine
public import CORALean.NN.Graph.Theorems.UncertainDegreeBounds
public import CORALean.NN.Layers.Theorems.Real.Basic

@[expose] public section

/-!
# The message-passing enclosure contains the true message passing

[1, Prop. 4]'s guarantee for `𝒫 ⊇ D̃^(-1/2) Ã D̃^(-1/2)`: whatever the uncertain edges weigh, the
message-passing matrix that graph produces is a point of `𝒫`. One factor vector does it. The edge
weight `λₑ` is the factor `2λₑ - 1`, as `uncertainAdj_exact` reads it; node `j`'s residual factor is
what the relaxation left over at that node's actual degree, divided by the bound it came with (total
by cases: a zero error bounds the residual by zero). At those factors all three sets are exact, so
the only approximation is that the residuals do not range independently of the edges.

## Inputs
* `R` – relaxation of the inverse square root
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges

## Hypotheses
* `hR` – relaxation is sound for the inverse square root
* `hA` – adjacency entries are nonnegative
* `hlam` – edge weights lie in the unit interval

## Conclusion
* the graph's own message-passing matrix lies in the enclosure

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix PolyZonotope

variable {N m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the relaxation's affine map misses at node `j`'s actual degree. -/
private noncomputable def GNN.aux_residual (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) (j : Fin N) : ℝ :=
  invSqrt (GNN.degreeAt A U lam j)
    - (GNN.sqrtSlope R A U j * GNN.degreeAt A U lam j + GNN.sqrtOffset R A U j)

/-- The residual as a factor of its own: normalised by the bound it came with,
or zero, there being nothing to normalise by and nothing to carry. -/
private noncomputable def GNN.aux_resFactor (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) (j : Fin N) : ℝ :=
  if GNN.step_sqrtError R A U j = 0 then 0
  else GNN.aux_residual R A U lam j / GNN.step_sqrtError R A U j

/-- The factor vector the whole enclosure is read at: the edge weights rescaled,
then the residuals. -/
private noncomputable def GNN.aux_factors (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) : Fin (m + N) → ℝ :=
  Fin.addCases (fun e => 2 * lam e - 1) (GNN.aux_resFactor R A U lam)

/-- The entrywise product at `Mat`, read at one entry. -/
private theorem GNN.aux_hadamard_apply (X Y : Mat ℝ N N) (i j : Fin N) :
    (Entrywise.hadamardLin X) Y i j = X i j * Y i j := rfl

/-- `Fin.sum_univ_add` at the padded generator count, stated through the
projection because that is the form the goal has. -/
private theorem GNN.aux_sum_univ_uncertainAdjPad {β : Type} [AddCommMonoid β] {A : Mat ℝ N N}
    {U : Fin m → Fin N × Fin N} (f : Fin (m + N) → β) :
    ∑ k : Fin (GNN.step_uncertainAdjPad A U).h, f k
      = ∑ e, f (Fin.castAdd N e) + ∑ t, f (Fin.natAdd m t) :=
  Fin.sum_univ_add f

/-- The same at a broadcast's generator count, which is the same number read
through a different projection. -/
private theorem GNN.aux_sum_univ_sqrtBroadcast {β : Type} [AddCommMonoid β] {R : Relaxation ℝ}
    {A : Mat ℝ N N} {U : Fin m → Fin N × Fin N} {idx : Fin N → Fin N → Fin N}
    (f : Fin (m + N) → β) :
    ∑ k : Fin (GNN.step_sqrtBroadcast R A U idx).h, f k
      = ∑ e, f (Fin.castAdd N e) + ∑ t, f (Fin.natAdd m t) :=
  Fin.sum_univ_add f

/-- `R.sound` at the degree bracket: the residual never leaves its error. -/
private theorem GNN.aux_residual_le (R : Relaxation ℝ) (hR : R.Encloses invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1)
    (hA : ∀ a b, 0 ≤ A a b) (j : Fin N) :
    |GNN.aux_residual R A U lam j| ≤ GNN.step_sqrtError R A U j := by
  obtain ⟨_, hlo, hhi⟩ := GNN.degreeAt_bounds A U lam hlam hA j
  exact hR.sound hlo hhi

/-- The residual factor is spent exactly, in both branches: dividing by the
error and multiplying back, or a zero error forcing a zero residual. -/
private theorem GNN.aux_error_mul_resFactor (R : Relaxation ℝ) (hR : R.Encloses invSqrt)
    (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1)
    (hA : ∀ a b, 0 ≤ A a b) (j : Fin N) : -- --- CONCL ---
    GNN.step_sqrtError R A U j * GNN.aux_resFactor R A U lam j
      = GNN.aux_residual R A U lam j := by -- --- PROOF ---
  rw [GNN.aux_resFactor]
  split_ifs with h
  · -- no error to spend, so `aux_residual_le` leaves no residual either
    have hb := GNN.aux_residual_le R hR A U lam hlam hA j
    rw [h] at hb
    rw [h, zero_mul]
    exact (abs_nonpos_iff.mp hb).symm
  · field_simp

/-- Every factor is admissible: `2λ - 1` because `λ` is a weight, and a residual
factor because its numerator is bounded by its denominator. -/
private theorem GNN.aux_factors_abs_le (R : Relaxation ℝ) (hR : R.Encloses invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1)
    (hA : ∀ a b, 0 ≤ A a b) (k : Fin (m + N)) : -- --- CONCL ---
    |GNN.aux_factors R A U lam k| ≤ 1 := by -- --- PROOF ---
  refine Fin.addCases (fun e => ?_) (fun t => ?_) k
  · -- an edge factor is its weight rescaled to the unit interval around zero
    simp only [GNN.aux_factors, Fin.addCases_left, abs_le]
    exact ⟨by linarith [(hlam e).1], by linarith [(hlam e).2]⟩
  · simp only [GNN.aux_factors, Fin.addCases_right, GNN.aux_resFactor]
    split_ifs with h
    · rw [abs_zero]
      exact zero_le_one
    · -- a nonzero error is positive, since it bounds an absolute value
      have hb := GNN.aux_residual_le R hR A U lam hlam hA t
      have hpos : 0 < GNN.step_sqrtError R A U t :=
        lt_of_le_of_ne (le_trans (abs_nonneg _) hb) (Ne.symm h)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hb

/-- The padded adjacency at those factors is `Ã` itself: the residual half of
the generators is zero, and the edge half is `smul_edge_half` again. -/
private theorem GNN.aux_padPoint (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) : -- --- CONCL ---
    (GNN.step_uncertainAdjPad A U).point (GNN.aux_factors R A U lam)
      = GNN.adjAt A U lam + 1 := by -- --- PROOF ---
  rw [PolyZonotope.point, GNN.aux_sum_univ_uncertainAdjPad]
  simp only [GNN.step_uncertainAdjPad, PolyZonotope.monomial_identE, GNN.aux_factors,
    Fin.addCases_left, Fin.addCases_right, smul_zero, Finset.sum_const_zero, add_zero]
  -- one edge's half in the center plus its half in the generator is its weight
  have hedge : ∀ e, (1/2 : ℝ) • GNN.edgeMat (U e)
      + (2 * lam e - 1) • ((1/2 : ℝ) • GNN.edgeMat (U e)) = lam e • GNN.edgeMat (U e) := by
    intro e
    rw [← GNN.smul_edge_half]
    congr 1
    ring
  rw [GNN.adjAt, add_assoc (A + 1), ← Finset.sum_add_distrib]
  simp only [hedge]
  abel

/-- Either broadcast at those factors: node `idx i j`'s inverse square root,
exactly, which is `sqrt_affine` plus the residual the factor spends. -/
private theorem GNN.aux_broadcastPoint (R : Relaxation ℝ) (hR : R.Encloses invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (lam : Fin m → ℝ) (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1)
    (hA : ∀ a b, 0 ≤ A a b) (idx : Fin N → Fin N → Fin N) : -- --- CONCL ---
    (GNN.step_sqrtBroadcast R A U idx).point (GNN.aux_factors R A U lam)
      = fun i j => invSqrt (GNN.degreeAt A U lam (idx i j)) := by -- --- PROOF ---
  rw [PolyZonotope.point, GNN.aux_sum_univ_sqrtBroadcast]
  funext i j
  simp only [GNN.step_sqrtBroadcast, PolyZonotope.monomial_identE, GNN.aux_factors,
    Fin.addCases_left, Fin.addCases_right, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  -- only node `idx i j`'s own residual generator is nonzero in this entry
  have hres : ∑ t, GNN.aux_resFactor R A U lam t
      * (if idx i j = t then GNN.step_sqrtError R A U (idx i j) else 0)
      = GNN.aux_residual R A U lam (idx i j) := by
    have h : ∀ t : Fin N, GNN.aux_resFactor R A U lam t
        * (if idx i j = t then GNN.step_sqrtError R A U (idx i j) else 0)
        = if idx i j = t then GNN.step_sqrtError R A U (idx i j)
            * GNN.aux_resFactor R A U lam t else 0 := by
      intro t
      split_ifs <;> ring
    simp only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact GNN.aux_error_mul_resFactor R hR A U lam hlam hA (idx i j)
  -- the edge half is the affine form the relaxation was composed into
  have hedge : ∑ e, (2 * lam e - 1) * GNN.sqrtEdgeCoeff R A U (idx i j) e
      = ∑ e, GNN.sqrtEdgeCoeff R A U (idx i j) e * (2 * lam e - 1) :=
    Finset.sum_congr rfl fun e _ => mul_comm _ _
  rw [hedge, hres, ← add_assoc, ← GNN.sqrt_affine R A U lam (idx i j), GNN.aux_residual]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1]'s message-passing enclosure is sound: at any admissible edge weights, the
graph's own `D̃^(-1/2) Ã D̃^(-1/2)` is a point of it. -/
theorem GNN.messagePassing_mem_enclosure (R : Relaxation ℝ) (hR : R.Encloses invSqrt)
    (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) : -- --- CONCL ---
    GNN.messagePassing (GNN.adjAt A U lam)
      ∈ (GNN.messagePassingEnclosure R A U).construct := by -- --- PROOF ---
  have hinner := PolyZonotope.bilin_point (Entrywise.hadamardLin (α := Mat ℝ N N))
    (GNN.step_uncertainAdjPad A U) (GNN.step_sqrtRow R A U) rfl (GNN.aux_factors R A U lam)
  have houter := PolyZonotope.bilin_point (Entrywise.hadamardLin (α := Mat ℝ N N))
    ((GNN.step_uncertainAdjPad A U).bilin Entrywise.hadamardLin (GNN.step_sqrtRow R A U) rfl)
    (GNN.step_sqrtCol R A U) rfl (GNN.aux_factors R A U lam)
  -- the clamp in `invSqrt` costs nothing, the degrees being at least `1`
  have hone : ∀ k, (1 : ℝ) ≤ GNN.degreeAt A U lam k := fun k =>
    le_trans (GNN.degreeAt_bounds A U lam hlam hA k).1
      (GNN.degreeAt_bounds A U lam hlam hA k).2.1
  have hd : ∀ k, GNN.degree (GNN.adjAt A U lam) k = GNN.degreeAt A U lam k := fun _ => rfl
  -- the point of the enclosure is the message passing the graph actually has
  have hpt : (GNN.messagePassingEnclosure R A U).point (GNN.aux_factors R A U lam)
      = GNN.messagePassing (GNN.adjAt A U lam) := by
    refine houter.trans ?_
    rw [hinner]
    -- `Fin.cast` at a shared factor set is the identity, so all three read `a`
    show Entrywise.hadamardLin
        (Entrywise.hadamardLin ((GNN.step_uncertainAdjPad A U).point (GNN.aux_factors R A U lam))
          ((GNN.step_sqrtBroadcast R A U fun i _ => i).point (GNN.aux_factors R A U lam)))
        ((GNN.step_sqrtBroadcast R A U fun _ j => j).point (GNN.aux_factors R A U lam))
      = GNN.messagePassing (GNN.adjAt A U lam)
    rw [GNN.aux_padPoint R A U lam, GNN.aux_broadcastPoint R hR A U lam hlam hA,
      GNN.aux_broadcastPoint R hR A U lam hlam hA]
    funext i j
    simp only [GNN.aux_hadamard_apply, GNN.messagePassing, hd]
    rw [invSqrt_eq_of_one_le (hone i), invSqrt_eq_of_one_le (hone j), div_eq_mul_inv,
      mul_inv, ← mul_assoc]
  rw [← hpt]
  exact PolyZonotope.point_mem_construct _ (GNN.aux_factors_abs_le R hR A U lam hlam hA)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
