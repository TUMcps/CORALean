import CORALean.ContSet.Zonotope.Real.Operations.Aligned
import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedExact
import CORALean.ContSet.Zonotope.Real.Theorems.Convex
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# No aligned zonotope around `EW` gives the whole difference `Z ⊖ EW`

[1, Eq. 16] writes `{u ∈ U | ∀w ∈ W, Ax + Bu + Ew + K ∈ Z_k}` as the projection of
`Ax + Bu + K ∈ Z_k ⊖ Z(Z_k, EW)`; the second is only a subset. `Z` is the hexagon with
generators `(1, 0)`, `(0, 1)`, `(1, 1)` and `EW` the triangle `(0, 0)`, `(1, 0)`, `(1, 1)`.
`Z ⊖ EW` is `{z₀, z₁, z₀ - z₁ ∈ [-2, 1]}`, and for every aligned zonotope `Z̄ ⊇ EW`
(scalings in `[0, 1]`, any centre, so whatever (min-out)'s weights select) one of
`(-2, -1)`, `(1, 1)`, `(-1, -2)`, `(-2, 0)` is in `Z ⊖ EW` and not in `Z ⊖ Z̄`: the
triangle's three widths cannot all be matched by a centrally symmetric aligned
zonotope. At `A = B = E = I`, `K = 0`, `x = 0` and `U = Z` that is (16) with `⊊`.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The hexagon `Z`: generators `(1, 0)`, `(0, 1)`, `(1, 1)` around `0`. -/
abbrev aux_hex : Zonotope (Vec ℝ 2) := ⟨3, 0, ![![1, 0], ![0, 1], ![1, 1]]⟩

/-- A point of the hexagon has `|z₀|, |z₁|, |z₀ - z₁| ≤ 2`. -/
theorem aux_hex_bounds {z : Vec ℝ 2} (hz : z ∈ aux_hex.construct) :
    -2 ≤ z 0 ∧ z 0 ≤ 2 ∧ -2 ≤ z 1 ∧ z 1 ≤ 2 ∧ -2 ≤ z 0 - z 1 ∧ z 0 - z 1 ≤ 2 := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hz
  have h0 := abs_le.mp (hβ 0)
  have h1 := abs_le.mp (hβ 1)
  have h2 := abs_le.mp (hβ 2)
  simp only [aux_hex, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Conversely `|z₀|, |z₁|, |z₀ - z₁| ≤ 2` puts `z` in the hexagon, with
`θ₂ = max(z₀, z₁, 0) - 1`. -/
theorem aux_hex_mem {z : Vec ℝ 2} (h0 : |z 0| ≤ 2) (h1 : |z 1| ≤ 2) (h01 : |z 0 - z 1| ≤ 2) :
    z ∈ aux_hex.construct := by -- --- PROOF ---
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨hdl, hdu⟩ := abs_le.mp h01
  set t : ℝ := max (max (z 0) (z 1)) 0 - 1 with ht
  have hx0 := le_max_left (z 0) (z 1)
  have hx1 := le_max_right (z 0) (z 1)
  have hxm := le_max_left (max (z 0) (z 1)) 0
  have hzm := le_max_right (max (z 0) (z 1)) 0
  have hm0 : z 0 ≤ t + 1 := by rw [ht]; linarith
  have hm1 : z 1 ≤ t + 1 := by rw [ht]; linarith
  have hmz : -1 ≤ t := by rw [ht]; linarith
  -- `t + 1` is one of `z₀`, `z₁`, `0`
  have hcase : t + 1 = z 0 ∨ t + 1 = z 1 ∨ t + 1 = 0 := by
    rw [ht, sub_add_cancel]
    rcases max_choice (max (z 0) (z 1)) 0 with h | h
    · rw [h]; rcases max_choice (z 0) (z 1) with h' | h' <;> rw [h'] <;> simp
    · rw [h]; simp
  refine ⟨![z 0 - t, z 1 - t, t], fun j => ?_, ?_⟩
  · fin_cases j
    · show |z 0 - t| ≤ 1
      exact abs_le.mpr ⟨by rcases hcase with h | h | h <;> linarith, by linarith⟩
    · show |z 1 - t| ≤ 1
      exact abs_le.mpr ⟨by rcases hcase with h | h | h <;> linarith, by linarith⟩
    · show |t| ≤ 1
      exact abs_le.mpr ⟨hmz, by rcases hcase with h | h | h <;> linarith⟩
  · funext i
    fin_cases i <;> simp [aux_hex, Fin.sum_univ_three]

/-- `u ∈ Z ⊖ conv V` once `u + v ∈ Z` at each of the three vertices. -/
theorem aux_mem_minkowskiDiff {u : Vec ℝ 2} {V : Set (Vec ℝ 2)}
    (hV : ∀ v ∈ V, u + v ∈ aux_hex.construct) :
    u ∈ minkowskiDiff aux_hex.construct (convexHull ℝ V) := fun _ hs =>
  convexHull_min hV ((Zonotope.convex_construct aux_hex).translate_preimage_right u) hs

/-- `θ a` for `|θ| ≤ 1` and `a ≥ 0` lies in `[-a, a]`. -/
theorem aux_mul_bounds {θ a : ℝ} (hθ : |θ| ≤ 1) (ha : 0 ≤ a) : -a ≤ θ * a ∧ θ * a ≤ a := by
  obtain ⟨h1, h2⟩ := abs_le.mp hθ
  constructor <;> nlinarith


/-- A point of the aligned hexagon, by coordinates. -/
theorem aux_aligned_coords {c : Vec ℝ 2} {a : Fin 3 → ℝ} {y : Vec ℝ 2}
    (hy : y ∈ (aux_hex.aligned c a).construct) : ∃ θ : Fin 3 → ℝ, (∀ j, |θ j| ≤ 1) ∧
      y 0 = c 0 + θ 0 * a 0 + θ 2 * a 2 ∧ y 1 = c 1 + θ 1 * a 1 + θ 2 * a 2 := by
  obtain ⟨θ, hθ, rfl⟩ := hy
  refine ⟨θ, hθ, ?_, ?_⟩ <;> simp [Zonotope.aligned, aux_hex] <;> erw [Fin.sum_univ_three] <;>
    simp <;> ring

/-- The corner of the aligned hexagon at coefficients `θ`. -/
theorem aux_aligned_corner (c : Vec ℝ 2) (a θ : Fin 3 → ℝ) (hθ : ∀ j, |θ j| ≤ 1) :
    ![c 0 + θ 0 * a 0 + θ 2 * a 2, c 1 + θ 1 * a 1 + θ 2 * a 2]
      ∈ (aux_hex.aligned c a).construct := by
  refine ⟨θ, hθ, ?_⟩
  funext i
  fin_cases i <;> simp [Zonotope.aligned, aux_hex] <;> erw [Fin.sum_univ_three] <;> simp <;> ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 16]: for the hexagon and the triangle, every aligned zonotope around the
triangle misses a point of the true difference. -/
theorem Zonotope.minkowskiDiff_not_subset_minkDiffAligned :
    ∃ (Z : Zonotope (Vec ℝ 2)) (S : Set (Vec ℝ 2)), S = convexHull ℝ {![0, 0], ![1, 0], ![1, 1]} ∧
      ∀ (c : Vec ℝ 2) (a : Fin Z.h → ℝ), (∀ i, 0 ≤ a i ∧ a i ≤ 1) →
        S ⊆ (Z.aligned c a).construct →
        ∃ u ∈ minkowskiDiff Z.construct S,
          u ∉ (Z.minkDiffAligned (Z.aligned c a) rfl).construct := by -- --- PROOF ---
  refine ⟨aux_hex, _, rfl, fun c a ha hS => ?_⟩
  rw [aux_hex.minkDiffAligned_exact (aux_hex.aligned c a) rfl a (fun i => (ha i).1)
    (fun i => (ha i).2) (fun _ => rfl)]
  -- the triangle's vertices are in `Z̄`, which bounds `c` and `a` in each direction
  have hv : ∀ v ∈ ({![0, 0], ![1, 0], ![1, 1]} : Set (Vec ℝ 2)),
      v ∈ (aux_hex.aligned c a).construct := fun v hv => hS (subset_convexHull ℝ _ hv)
  obtain ⟨θ, hθ, e00, e01⟩ := aux_aligned_coords (hv ![0, 0] (by simp))
  obtain ⟨φ, hφ, e10, e11⟩ := aux_aligned_coords (hv ![1, 0] (by simp))
  obtain ⟨ψ, hψ, e20, e21⟩ := aux_aligned_coords (hv ![1, 1] (by simp))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e00 e01 e10 e11 e20 e21
  have ha0 := (ha 0).1
  have ha1 := (ha 1).1
  have ha2 := (ha 2).1
  have b := fun (t : Fin 3 → ℝ) (ht : ∀ j, |t j| ≤ 1) (j : Fin 3) => aux_mul_bounds (ht j) (ha j).1
  have hθ0 := b θ hθ 0; have hθ1 := b θ hθ 1; have hθ2 := b θ hθ 2
  have hφ0 := b φ hφ 0; have hφ1 := b φ hφ 1; have hφ2 := b φ hφ 2
  have hψ1 := b ψ hψ 1; have hψ2 := b ψ hψ 2
  -- a candidate `u` is in `Z ⊖ S` when `u + v ∈ Z` at the three vertices
  have hin : ∀ u : Vec ℝ 2, (∀ v ∈ ({![0, 0], ![1, 0], ![1, 1]} : Set (Vec ℝ 2)),
      |u 0 + v 0| ≤ 2 ∧ |u 1 + v 1| ≤ 2 ∧ |u 0 + v 0 - (u 1 + v 1)| ≤ 2) →
      u ∈ minkowskiDiff aux_hex.construct (convexHull ℝ {![0, 0], ![1, 0], ![1, 1]}) :=
    fun u hu => aux_mem_minkowskiDiff fun v hv => by
      obtain ⟨h0, h1, h2⟩ := hu v hv
      exact aux_hex_mem (by simpa using h0) (by simpa using h1) (by simpa using h2)
  -- and fails `Z ⊖ Z̄` once a corner `y` of `Z̄` puts `u + y` outside the hexagon
  have hout : ∀ (u : Vec ℝ 2) (t : Fin 3 → ℝ), (∀ j, |t j| ≤ 1) →
      (let y0 := u 0 + (c 0 + t 0 * a 0 + t 2 * a 2)
       let y1 := u 1 + (c 1 + t 1 * a 1 + t 2 * a 2)
       y0 < -2 ∨ 2 < y0 ∨ y1 < -2 ∨ 2 < y1 ∨ y0 - y1 < -2) →
      u ∉ minkowskiDiff aux_hex.construct (aux_hex.aligned c a).construct := by
    intro u t ht hy hu
    have := aux_hex_bounds (hu _ (aux_aligned_corner c a t ht))
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rcases hy with h | h | h | h | h <;> linarith
  have h1 : ∀ x : ℝ, |x| ≤ 1 ↔ -1 ≤ x ∧ x ≤ 1 := fun x => abs_le
  -- which corner depends on which of the five bounds the centre leaves slack
  by_cases hA : c 0 - a 0 - a 2 < 0
  · refine ⟨![-2, -1], hin _ ?_, hout _ ![-1, 0, -1] ?_ ?_⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> norm_num [abs_le]
    · intro j; fin_cases j <;> norm_num
    · left; simp; linarith
  by_cases hB : 1 < c 0 + a 0 + a 2
  · refine ⟨![1, 1], hin _ ?_, hout _ ![1, 0, 1] ?_ ?_⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> norm_num [abs_le]
    · intro j; fin_cases j <;> norm_num
    · right; left; simp; linarith
  by_cases hC : c 1 - a 1 - a 2 < 0
  · refine ⟨![-1, -2], hin _ ?_, hout _ ![0, -1, -1] ?_ ?_⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> norm_num [abs_le]
    · intro j; fin_cases j <;> norm_num
    · right; right; left; simp; linarith
  by_cases hD : 1 < c 1 + a 1 + a 2
  · refine ⟨![1, 1], hin _ ?_, hout _ ![0, 1, 1] ?_ ?_⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> norm_num [abs_le]
    · intro j; fin_cases j <;> norm_num
    · right; right; right; left; simp; linarith
  -- otherwise `c = (½, ½)`, and `S`'s width along `z₀ - z₁` forces `a₀ + a₁ ≥ 1`
  · refine ⟨![-2, 0], hin _ ?_, hout _ ![-1, 1, 0] ?_ ?_⟩
    · intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> norm_num [abs_le]
    · intro j; fin_cases j <;> norm_num
    · right; right; right; right; simp; linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
