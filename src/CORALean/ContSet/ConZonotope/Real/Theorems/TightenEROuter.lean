module

public import CORALean.ContSet.ConZonotope.Real.Operations.TightenER
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
public import CORALean.ContSet.Interval.Real.Theorems.DivBetweenEndpoints
public import CORALean.Global.FoldInduction
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `ConZonotope.tightenER` is sound for `B∞(A, b)`

Every coefficient vector of `B∞(A, b) = {ξ | Aξ = b, ‖ξ‖∞ ≤ 1}` lies in the box `E` that Algorithm 1
returns ([1, Alg. 1 (R)], [1, Alg. 1 (iteration)], [2, Alg. 1]) and, coordinate by coordinate, in
the intervals `R`, after any number of passes. That is what the emptiness test `E ∩ R = ∅ ⇒ Z = ∅`
needs.

It is not the property [1] and [2] print for `R`, that `R_j` contains
`{ξ_j | Aξ = b, |ξ_i| ≤ 1 ∀ i ≠ j}`: `R_j` is computed from the running `E`, which already used
`|ξ_j| ≤ 1`, and `tightenER_not_superset` is the one-row system where `R_j` excludes such a `ξ_j`.

## Inputs
* `nc` – number of constraints
* `ng` – number of generators
* `A` – constraint matrix
* `b` – constraint offset
* `k` – number of extra passes
* `β` – feasible coefficient vector

## Hypotheses
* `hbox` – the vector lies in the unit box
* `heq` – the vector solves the equations

## Conclusion
* the vector lies in the box and between the running bounds

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for constrained
      zonotopes". Automatica, 2022.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Row `i` of `Aξ = b`, solved for `βⱼ` with the other coefficients in `E`, lands between
`rowBound`'s two endpoints. -/
private theorem ConZonotope.aux_rowBound_mem {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng) {E : Interval (Vec ℝ ng)} {β : Vec ℝ ng} (h0 : A i j ≠ 0)
    (hβ : β ∈ E.construct) (hrow : (A *ᵥ β) i = b i) : -- --- CONCL ---
    min (ConZonotope.rowBound A b i j E).inf (ConZonotope.rowBound A b i j E).sup ≤ β j ∧
      β j ≤ max (ConZonotope.rowBound A b i j E).inf
        (ConZonotope.rowBound A b i j E).sup := by -- --- PROOF ---
  -- `Σ_{l≠j} a_il βl` lies inside the interval the same sum bounds entrywise
  have hS1 : (∑ l ∈ Finset.univ.erase j, min (A i l * E.inf l) (A i l * E.sup l))
      ≤ ∑ l ∈ Finset.univ.erase j, A i l * β l :=
    Finset.sum_le_sum fun l _ => (Interval.mul_between_endpoints (hβ l).1 (hβ l).2).1
  have hS2 : (∑ l ∈ Finset.univ.erase j, A i l * β l)
      ≤ ∑ l ∈ Finset.univ.erase j, max (A i l * E.inf l) (A i l * E.sup l) :=
    Finset.sum_le_sum fun l _ => (Interval.mul_between_endpoints (hβ l).1 (hβ l).2).2
  -- row `i` of `Aβ = b`, split at coordinate `j`
  have hrow' : A i j * β j + ∑ l ∈ Finset.univ.erase j, A i l * β l = b i := by
    rw [Finset.add_sum_erase Finset.univ (fun l => A i l * β l) (Finset.mem_univ j),
      ← hrow, Matrix.mulVec_apply_eq_sum]
  have h1 : b i - (∑ l ∈ Finset.univ.erase j, max (A i l * E.inf l) (A i l * E.sup l))
      ≤ A i j * β j := by linarith
  have h2 : A i j * β j
      ≤ b i - (∑ l ∈ Finset.univ.erase j, min (A i l * E.inf l) (A i l * E.sup l)) := by
    linarith
  exact Interval.div_between_endpoints h0 h1 h2

/-- Lines 3-5 keep a feasible coefficient vector inside `E` and inside every `R_j`. -/
private theorem ConZonotope.aux_tightenCoeffER_outer {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng) {β : Vec ℝ ng}
    {S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))}
    (hS : β ∈ S.1.construct ∧ ∀ k, S.2.1 k ≤ (β k : EReal) ∧ (β k : EReal) ≤ S.2.2 k)
    (hrow : (A *ᵥ β) i = b i) : -- --- CONCL ---
    β ∈ (ConZonotope.tightenCoeffER A b i j S).1.construct ∧
      ∀ k, (ConZonotope.tightenCoeffER A b i j S).2.1 k ≤ (β k : EReal) ∧
        (β k : EReal) ≤ (ConZonotope.tightenCoeffER A b i j S).2.2 k := by -- --- PROOF ---
  unfold ConZonotope.tightenCoeffER
  split_ifs with h0
  · exact hS
  obtain ⟨hE, hR⟩ := hS
  obtain ⟨hlo, hhi⟩ := ConZonotope.aux_rowBound_mem A b i j h0 hE hrow
  refine ⟨?_, ?_⟩
  · -- line 5: `E_j` met with the new bound, every other coordinate untouched
    intro k
    unfold ConZonotope.tightenCoeff
    rw [if_neg h0]
    rcases eq_or_ne k j with rfl | hk
    · show Function.update S.1.inf k (max (S.1.inf k)
            (min (ConZonotope.rowBound A b i k S.1).inf (ConZonotope.rowBound A b i k S.1).sup)) k
            ≤ β k
          ∧ β k ≤ Function.update S.1.sup k (min (S.1.sup k)
            (max (ConZonotope.rowBound A b i k S.1).inf (ConZonotope.rowBound A b i k S.1).sup)) k
      rw [Function.update_self, Function.update_self]
      exact ⟨max_le (hE k).1 hlo, le_min (hE k).2 hhi⟩
    · show Function.update S.1.inf j (max (S.1.inf j)
            (min (ConZonotope.rowBound A b i j S.1).inf (ConZonotope.rowBound A b i j S.1).sup)) k
            ≤ β k
          ∧ β k ≤ Function.update S.1.sup j (min (S.1.sup j)
            (max (ConZonotope.rowBound A b i j S.1).inf (ConZonotope.rowBound A b i j S.1).sup)) k
      rw [Function.update_of_ne hk, Function.update_of_ne hk]
      exact hE k
  · -- line 4: `R_j` met with the same bound, every other `R_k` untouched
    intro k
    rcases eq_or_ne k j with rfl | hk
    · simp only [Function.update_self]
      exact ⟨max_le (hR k).1 (EReal.coe_le_coe_iff.mpr hlo),
        le_min (hR k).2 (EReal.coe_le_coe_iff.mpr hhi)⟩
    · simp only [Function.update_of_ne hk]
      exact hR k

/-- One pass of lines 2-10 keeps the same invariant. -/
private theorem ConZonotope.aux_tightenPassER_outer {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    {β : Vec ℝ ng} {S : Interval (Vec ℝ ng) × ((Fin ng → EReal) × (Fin ng → EReal))}
    (hS : β ∈ S.1.construct ∧ ∀ k, S.2.1 k ≤ (β k : EReal) ∧ (β k : EReal) ≤ S.2.2 k)
    (heq : ∀ i, (A *ᵥ β) i = b i) : -- --- CONCL ---
    β ∈ (ConZonotope.tightenPassER A b S).1.construct ∧
      ∀ k, (ConZonotope.tightenPassER A b S).2.1 k ≤ (β k : EReal) ∧
        (β k : EReal) ≤ (ConZonotope.tightenPassER A b S).2.2 k := by -- --- PROOF ---
  unfold ConZonotope.tightenPassER
  refine Fin.foldl_induction (P := fun S : Interval (Vec ℝ ng) × ((Fin ng → EReal) ×
      (Fin ng → EReal)) => β ∈ S.1.construct ∧
        ∀ k, S.2.1 k ≤ (β k : EReal) ∧ (β k : EReal) ≤ S.2.2 k) nc _ S hS ?_
  intro S' i hS'
  exact Fin.foldl_induction (P := fun S : Interval (Vec ℝ ng) × ((Fin ng → EReal) ×
      (Fin ng → EReal)) => β ∈ S.1.construct ∧
        ∀ k, S.2.1 k ≤ (β k : EReal) ∧ (β k : EReal) ≤ S.2.2 k) ng _ S' hS'
    fun S'' j hS'' => ConZonotope.aux_tightenCoeffER_outer A b i j hS'' (heq i)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1 (R)], [1, Alg. 1 (iteration)] and [2, Alg. 1], after any number `k + 1` of passes:
every `β ∈ B∞(A, b)` lies in `E`, and `R_j ∋ β_j` for every `j`. -/
theorem ConZonotope.tightenER_outer {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc) (k : ℕ)
    {β : Vec ℝ ng} (hbox : ∀ j, |β j| ≤ 1) (heq : ∀ i, (A *ᵥ β) i = b i) : -- --- CONCL ---
    β ∈ (ConZonotope.tightenER A b k).1.construct ∧
      ∀ j, (ConZonotope.tightenER A b k).2.1 j ≤ (β j : EReal) ∧
        (β j : EReal) ≤ (ConZonotope.tightenER A b k).2.2 j := by -- --- PROOF ---
  unfold ConZonotope.tightenER
  -- line 1's state already holds `β`: `[-1, 1]` by the box, `[-∞, +∞]` trivially
  have h₀ : β ∈ (⟨fun _ => -1, fun _ => 1⟩ : Interval (Vec ℝ ng)).construct ∧
      ∀ j, ((fun _ => ⊥, fun _ => ⊤) : (Fin ng → EReal) × (Fin ng → EReal)).1 j
          ≤ (β j : EReal) ∧
        (β j : EReal) ≤ ((fun _ => ⊥, fun _ => ⊤) : (Fin ng → EReal) × (Fin ng → EReal)).2 j :=
    ⟨fun j => abs_le.mp (hbox j), fun _ => ⟨bot_le, le_top⟩⟩
  -- each further pass keeps it
  generalize (⟨fun _ => -1, fun _ => 1⟩ : Interval (Vec ℝ ng)) = E₀ at h₀ ⊢
  generalize ((fun _ => ⊥, fun _ => ⊤) : (Fin ng → EReal) × (Fin ng → EReal)) = R₀ at h₀ ⊢
  induction k + 1 generalizing E₀ R₀ with
  | zero => exact h₀
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      obtain ⟨h1, h2⟩ := ConZonotope.aux_tightenPassER_outer A b (S := (E₀, R₀)) h₀ heq
      exact ih _ _ ⟨h1, h2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
