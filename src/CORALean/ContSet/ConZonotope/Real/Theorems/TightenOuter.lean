module

public import CORALean.ContSet.ConZonotope.Real.Operations.Tighten
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenEndpoints
public import CORALean.ContSet.Interval.Real.Theorems.DivBetweenEndpoints
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `ConZonotope.tighten` is sound

Every feasible coefficient vector — one satisfying `Aξ = b` and `‖ξ‖∞ ≤ 1` — lies in the
box Algorithm 1 [2, Alg. 1] returns. This is the guarantee `Thm. 2`'s `E_k` (eq. 12) draws on: a
tightened bound is never so tight that it excludes a point the constraints actually
admit.

`aux_tightenCoeff_outer` is one row's step: it solves that row of `Aξ = b` for
coefficient `j`, bounding the rest of the sum by `mul_between_endpoints` the way
`Interval.mtimes_outer` does, then reads `βⱼ` back out of the product by
`div_between_endpoints`. `aux_tightenRow_outer` and `tighten_outer` carry that across a
row and across every row, by `Fin.foldl_induction`.

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
* [2] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Row `i` never tightens a feasible coefficient out of its box: solving that row of
`Aξ = b` for `βⱼ` places it between the same endpoints `tightenCoeff` computes. -/
theorem ConZonotope.aux_tightenCoeff_outer {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) (j : Fin ng) {E : Interval (Vec ℝ ng)} {β : Vec ℝ ng}
    (hβ : β ∈ E.construct) (hrow : (A *ᵥ β) i = b i) :
    β ∈ (ConZonotope.tightenCoeff A b i j E).construct := by -- --- PROOF ---
  unfold ConZonotope.tightenCoeff
  split_ifs with h0
  · exact hβ
  · intro k
    -- `k` is the coordinate `mem_construct_iff` asks about; only `j` itself can move
    rcases eq_or_ne k j with rfl | hk
    · -- the tightened coordinate: expose the `Function.update` this is, at its own index
      show Function.update E.inf k (max (E.inf k)
            (min (ConZonotope.rowBound A b i k E).inf (ConZonotope.rowBound A b i k E).sup)) k
            ≤ β k
          ∧ β k ≤ Function.update E.sup k (min (E.sup k)
            (max (ConZonotope.rowBound A b i k E).inf (ConZonotope.rowBound A b i k E).sup)) k
      rw [Function.update_self, Function.update_self]
      obtain ⟨hbin, hbsup⟩ := hβ k
      -- `rowBound`'s own two endpoints, spelled back out from `Finset.sum`
      have hR1 : (ConZonotope.rowBound A b i k E).inf
          = (b i - ∑ l ∈ Finset.univ.erase k, max (A i l * E.inf l) (A i l * E.sup l)) / A i k :=
        rfl
      have hR2 : (ConZonotope.rowBound A b i k E).sup
          = (b i - ∑ l ∈ Finset.univ.erase k, min (A i l * E.inf l) (A i l * E.sup l)) / A i k :=
        rfl
      -- `Σ_{l≠k} a_il βl` lies inside the interval the same sum bounds entrywise
      have hS1 : (∑ l ∈ Finset.univ.erase k, min (A i l * E.inf l) (A i l * E.sup l))
          ≤ ∑ l ∈ Finset.univ.erase k, A i l * β l :=
        Finset.sum_le_sum fun l _ => (Interval.mul_between_endpoints (hβ l).1 (hβ l).2).1
      have hS2 : (∑ l ∈ Finset.univ.erase k, A i l * β l)
          ≤ ∑ l ∈ Finset.univ.erase k, max (A i l * E.inf l) (A i l * E.sup l) :=
        Finset.sum_le_sum fun l _ => (Interval.mul_between_endpoints (hβ l).1 (hβ l).2).2
      -- row `i` of `Aβ = b`, split at coordinate `k`
      have hrow' : A i k * β k + ∑ l ∈ Finset.univ.erase k, A i l * β l = b i := by
        rw [Finset.add_sum_erase Finset.univ (fun l => A i l * β l) (Finset.mem_univ k),
          ← hrow, Matrix.mulVec_apply_eq_sum]
      have h1 : b i - (∑ l ∈ Finset.univ.erase k, max (A i l * E.inf l) (A i l * E.sup l))
          ≤ A i k * β k := by linarith
      have h2 : A i k * β k
          ≤ b i - (∑ l ∈ Finset.univ.erase k, min (A i l * E.inf l) (A i l * E.sup l)) := by
        linarith
      -- solve back for `βk` itself, then meet the box already known around it
      rw [hR1, hR2]
      obtain ⟨hlo, hhi⟩ := Interval.div_between_endpoints h0 h1 h2
      exact ⟨max_le hbin hlo, le_min hbsup hhi⟩
    · -- every other coordinate: `Function.update` at `j` never touches it
      show Function.update E.inf j (max (E.inf j)
              (min (ConZonotope.rowBound A b i j E).inf (ConZonotope.rowBound A b i j E).sup)) k
            ≤ β k
          ∧ β k ≤ Function.update E.sup j (min (E.sup j)
              (max (ConZonotope.rowBound A b i j E).inf (ConZonotope.rowBound A b i j E).sup)) k
      rw [Function.update_of_ne hk, Function.update_of_ne hk]
      exact hβ k

/-- Every row of `Aξ = b`, applied in turn, still leaves a feasible coefficient inside
the running box. -/
theorem ConZonotope.aux_tightenRow_outer {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc)
    (i : Fin nc) {E : Interval (Vec ℝ ng)} {β : Vec ℝ ng}
    (hβ : β ∈ E.construct) (hrow : (A *ᵥ β) i = b i) :
    β ∈ (ConZonotope.tightenRow A b i E).construct := by
  unfold ConZonotope.tightenRow
  exact Fin.foldl_induction (P := fun y => β ∈ y.construct) ng
    (fun E j => ConZonotope.tightenCoeff A b i j E) E hβ
    fun _ j hy => ConZonotope.aux_tightenCoeff_outer A b i j hy hrow


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]'s soundness: every point of the feasible coefficient box `B∞(A,b)` lies
in the interval enclosure `tighten` computes for it. -/
theorem ConZonotope.tighten_outer {nc ng : ℕ} (A : Mat ℝ nc ng) (b : Vec ℝ nc) {β : Vec ℝ ng}
    (hbox : ∀ j, |β j| ≤ 1) (heq : ∀ i, (A *ᵥ β) i = b i) :
    β ∈ (ConZonotope.tighten A b).construct := by -- --- PROOF ---
  unfold ConZonotope.tighten
  have hE₀ : β ∈ (⟨fun _ => -1, fun _ => 1⟩ : Interval (Vec ℝ ng)).construct :=
    fun k => abs_le.mp (hbox k)
  exact Fin.foldl_induction (P := fun y => β ∈ y.construct) nc
    (fun E i => ConZonotope.tightenRow A b i E) _ hE₀
    fun _ i hE => ConZonotope.aux_tightenRow_outer A b i hE (heq i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
