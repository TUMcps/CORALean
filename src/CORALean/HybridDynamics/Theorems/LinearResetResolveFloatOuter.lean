module

public import CORALean.HybridDynamics.Operations.LinearResetResolveFloat
public import CORALean.HybridDynamics.Operations.LinearResetResolve
public import Mathlib.Data.Fintype.Sigma
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The float `resolve` encloses the real resolved reset

The real `(A, B, c)` that `LinearReset.resolve` returns for the real values of the stored
matrices lies, entry by entry, in the interval matrices and the interval vector that
`resolveFloat` returns. An outer statement, with no hypothesis: the scatter of a column is a sum
over the coordinates it is written to, so the product of two scattered entries is a double sum of
products of stored entries, and each product and each sum is rounded in its own direction.
Every reset `x ↦ A x + B u + c` with `A`, `B`, `c` in the bounds is a candidate, the real one
among them; `resolve_apply` says what the real one computes.

## Inputs
* `A` – state matrix
* `B` – stacked input matrix
* `c` – offset
* `C` – output matrices
* `D` – feedthrough matrices
* `q` – output offsets
* `stateBinds` – state index maps
* `inputBinds` – input bindings

## Hypotheses
* none

## Conclusion
* resolved real reset lies in the interval result
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N g k : ℕ} {n m p : Fin k → ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum rounded down is below the sum of upper bounds of its terms. -/
private theorem aux_sumDown_le_of_le {l : ℕ} (f : Fin l → 𝕋) (r : Fin l → ℝ)
    (h : ∀ i, toReal (f i) ≤ r i) : toReal (sumDown f) ≤ ∑ i, r i :=
  (sumDown_le_sum f).trans (Finset.sum_le_sum fun i _ => h i)

/-- A sum rounded up is above the sum of lower bounds of its terms. -/
private theorem aux_le_sumUp_of_le {l : ℕ} (f : Fin l → 𝕋) (r : Fin l → ℝ)
    (h : ∀ i, r i ≤ toReal (f i)) : ∑ i, r i ≤ toReal (sumUp f) :=
  (Finset.sum_le_sum fun i _ => h i).trans (sum_le_sumUp f)

/-- The product of two scattered entries, as the rounded-down double sum of products. -/
private theorem aux_sumDown_ite_mul {n₁ n₂ : ℕ} (P : Fin n₁ → Prop) [DecidablePred P]
    (Q : Fin n₂ → Prop) [DecidablePred Q] (x : Fin n₁ → 𝕋) (y : Fin n₂ → 𝕋) :
    toReal (sumDown fun r => sumDown fun s => if P r ∧ Q s then mulDown (x r) (y s) else zero) ≤
      (∑ r, if P r then toReal (x r) else 0) * ∑ s, if Q s then toReal (y s) else 0 := by
  rw [Finset.sum_mul_sum]
  refine aux_sumDown_le_of_le _ _ fun r => aux_sumDown_le_of_le _ _ fun s => ?_
  by_cases hP : P r <;> by_cases hQ : Q s <;> simp [hP, hQ, toReal_zero, mulDown_le_mul]

/-- The product of two scattered entries, as the rounded-up double sum of products. -/
private theorem aux_ite_mul_le_sumUp {n₁ n₂ : ℕ} (P : Fin n₁ → Prop) [DecidablePred P]
    (Q : Fin n₂ → Prop) [DecidablePred Q] (x : Fin n₁ → 𝕋) (y : Fin n₂ → 𝕋) :
    (∑ r, if P r then toReal (x r) else 0) * (∑ s, if Q s then toReal (y s) else 0) ≤
      toReal (sumUp fun r => sumUp fun s => if P r ∧ Q s then mulUp (x r) (y s) else zero) := by
  rw [Finset.sum_mul_sum]
  refine aux_le_sumUp_of_le _ _ fun r => aux_le_sumUp_of_le _ _ fun s => ?_
  by_cases hP : P r <;> by_cases hQ : Q s <;> simp [hP, hQ, toReal_zero, mul_le_mulUp]

/-- A scattered entry times a stored one, rounded down. -/
private theorem aux_sumDown_ite_mul_const {n₁ : ℕ} (P : Fin n₁ → Prop) [DecidablePred P]
    (x : Fin n₁ → 𝕋) (y : 𝕋) :
    toReal (sumDown fun r => if P r then mulDown (x r) y else zero) ≤
      (∑ r, if P r then toReal (x r) else 0) * toReal y := by
  rw [Finset.sum_mul]
  refine aux_sumDown_le_of_le _ _ fun r => ?_
  by_cases hP : P r <;> simp [hP, toReal_zero, mulDown_le_mul]

/-- A scattered entry times a stored one, rounded up. -/
private theorem aux_ite_mul_const_le_sumUp {n₁ : ℕ} (P : Fin n₁ → Prop) [DecidablePred P]
    (x : Fin n₁ → 𝕋) (y : 𝕋) :
    (∑ r, if P r then toReal (x r) else 0) * toReal y ≤
      toReal (sumUp fun r => if P r then mulUp (x r) y else zero) := by
  rw [Finset.sum_mul]
  refine aux_le_sumUp_of_le _ _ fun r => ?_
  by_cases hP : P r <;> simp [hP, toReal_zero, mul_le_mulUp]

/-- Membership in a float interval vector, entry by entry. -/
private theorem aux_mem_vec_iff {l : ℕ} {I : Interval (Vec 𝕋 l)} {v : Vec ℝ l} :
    v ∈ I.construct ↔ ∀ i, toReal (I.inf i) ≤ v i ∧ v i ≤ toReal (I.sup i) :=
  ⟨fun h i => h i, fun h i => h i⟩

/-- A stored entry plus a sum over the inputs of all components, rounded down. -/
private theorem aux_addDown_sum_le (x : 𝕋) (f : ∀ i, Fin (m i) → 𝕋) (r : (Σ i, Fin (m i)) → ℝ)
    (h : ∀ i j, toReal (f i j) ≤ r ⟨i, j⟩) :
    toReal (addDown x (sumDown fun i => sumDown fun j => f i j)) ≤ toReal x + ∑ ij, r ij := by
  rw [Fintype.sum_sigma]
  exact (addDown_le_add _ _).trans (add_le_add le_rfl
    (aux_sumDown_le_of_le _ _ fun i => aux_sumDown_le_of_le _ _ fun j => h i j))

/-- A stored entry plus a sum over the inputs of all components, rounded up. -/
private theorem aux_sum_le_addUp (x : 𝕋) (f : ∀ i, Fin (m i) → 𝕋) (r : (Σ i, Fin (m i)) → ℝ)
    (h : ∀ i j, r ⟨i, j⟩ ≤ toReal (f i j)) :
    toReal x + ∑ ij, r ij ≤ toReal (addUp x (sumUp fun i => sumUp fun j => f i j)) := by
  rw [Fintype.sum_sigma]
  exact (add_le_add le_rfl
    (aux_le_sumUp_of_le _ _ fun i => aux_le_sumUp_of_le _ _ fun j => h i j)).trans
    (add_le_addUp _ _)

/-- The float update of one input encloses the real one, entry by entry. -/
private theorem aux_resolveUpdateFloat_outer (B : Mat 𝕋 N (∑ i, m i))
    (C : ∀ i, Mat 𝕋 (p i) (n i)) (D : ∀ i, Mat 𝕋 (p i) (m i)) (q : ∀ i, Vec 𝕋 (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (ij : Σ i, Fin (m i)) : -- --- CONCL ---
    let R := LinearReset.resolveUpdate (toRealMat B) (fun i => toRealMat (C i))
      (fun i => toRealMat (D i)) (fun i => toRealVec (q i)) stateBinds inputBinds ij
    let F := LinearReset.aux_resolveUpdateFloat B C D q stateBinds inputBinds ij
    (∀ a b, toReal (F.1.inf a b) ≤ R.1 a b ∧ R.1 a b ≤ toReal (F.1.sup a b)) ∧
      (∀ a col, toReal (F.2.1.inf a col) ≤ R.2.1 a col ∧ R.2.1 a col ≤ toReal (F.2.1.sup a col)) ∧
      (∀ a, toReal (F.2.2.inf a) ≤ R.2.2 a ∧ R.2.2 a ≤ toReal (F.2.2.sup a)) := by -- --- PROOF ---
  intro R F
  obtain ⟨i, j⟩ := ij
  rcases h : inputBinds i j with u' | ⟨c', l⟩
  · -- a globally bound input updates nothing, on both sides
    simp [R, F, LinearReset.resolveUpdate, LinearReset.aux_resolveUpdateFloat, h, toReal_zero]
  · -- a bound input: each entry is a product of scattered entries
    simp only [R, F, LinearReset.resolveUpdate, LinearReset.aux_resolveUpdateFloat, h, scatter,
      vecMulVec_apply, toRealMat, toRealVec]
    exact ⟨fun a b => ⟨aux_sumDown_ite_mul _ _ _ _, aux_ite_mul_le_sumUp _ _ _ _⟩,
      fun a col => ⟨aux_sumDown_ite_mul _ _ _ _, aux_ite_mul_le_sumUp _ _ _ _⟩,
      fun a => ⟨aux_sumDown_ite_mul_const _ _ _, aux_ite_mul_const_le_sumUp _ _ _⟩⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearReset.resolveFloat_outer (A : Mat 𝕋 N N) (B : Mat 𝕋 N (∑ i, m i)) (c : Vec 𝕋 N)
    (C : ∀ i, Mat 𝕋 (p i) (n i)) (D : ∀ i, Mat 𝕋 (p i) (m i)) (q : ∀ i, Vec 𝕋 (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N)
    (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) : -- --- CONCL ---
    let R := LinearReset.resolve (toRealMat A) (toRealMat B) (toRealVec c)
      (fun i => toRealMat (C i)) (fun i => toRealMat (D i)) (fun i => toRealVec (q i))
      stateBinds inputBinds
    let F := LinearReset.resolveFloat A B c C D q stateBinds inputBinds
    R.1 ∈ F.1.construct ∧ R.2.1 ∈ F.2.1.construct ∧ R.2.2 ∈ F.2.2.construct := by -- --- PROOF ---
  intro R F
  have hU := aux_resolveUpdateFloat_outer B C D q stateBinds inputBinds
  refine ⟨Interval.mem_mat_iff.2 fun a b => ?_, Interval.mem_mat_iff.2 fun a u => ?_,
    aux_mem_vec_iff.2 fun a => ?_⟩
  · -- `A`: the stored entry plus the updates
    simp only [R, F, LinearReset.resolve, LinearReset.resolveFloat, Matrix.add_apply,
      Matrix.sum_apply]
    exact ⟨aux_addDown_sum_le _ _ _ fun i j => ((hU ⟨i, j⟩).1 a b).1,
      aux_sum_le_addUp _ _ _ fun i j => ((hU ⟨i, j⟩).1 a b).2⟩
  · -- `B`: the global columns of the updated `B`, summed
    simp only [R, F, LinearReset.resolve, LinearReset.resolveFloat, Matrix.of_apply]
    rw [Fintype.sum_sigma]
    refine ⟨aux_sumDown_le_of_le _ _ fun i => aux_sumDown_le_of_le _ _ fun j => ?_,
      aux_le_sumUp_of_le _ _ fun i => aux_le_sumUp_of_le _ _ fun j => ?_⟩
    · by_cases hg : inputBinds i j = .global u
      · simp only [hg, if_true, Matrix.add_apply, Matrix.sum_apply]
        exact aux_addDown_sum_le _ _ _ fun i' j' => ((hU ⟨i', j'⟩).2.1 a _).1
      · simp [hg, toReal_zero]
    · by_cases hg : inputBinds i j = .global u
      · simp only [hg, if_true, Matrix.add_apply, Matrix.sum_apply]
        exact aux_sum_le_addUp _ _ _ fun i' j' => ((hU ⟨i', j'⟩).2.1 a _).2
      · simp [hg, toReal_zero]
  · -- `c`: the stored entry plus the updates
    simp only [R, F, LinearReset.resolve, LinearReset.resolveFloat, Pi.add_apply, Finset.sum_apply]
    exact ⟨aux_addDown_sum_le _ _ _ fun i j => ((hU ⟨i, j⟩).2.2 a).1,
      aux_sum_le_addUp _ _ _ fun i j => ((hU ⟨i, j⟩).2.2 a).2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
