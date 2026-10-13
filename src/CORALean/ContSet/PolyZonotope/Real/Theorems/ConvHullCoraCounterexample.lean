import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombExactOfDependent
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.FinCases

/-!
# The one-argument `convHull_` is not the convex hull

CORA documents `convHull_(pZ)` as the convex hull of `pZ`, but with one argument the code [1]
returns `linComb(pZ, pZ)`, the union of the chords between two points of
`pZ` (`PolyZonotope.linComb_exact_of_dependent`, for a set with no independent generators). The
chords of a curve need not fill its hull in dimension three: for the curve `γ(t) = (t, t², t⁴)`,
`t ∈ [-1, 1]`, the point `(0, 2/3, 2/3)` is a convex combination of the midpoint `(0, 1, 1)` of the
chord from `γ(-1)` to `γ(1)` and the point `γ(0) = 0`, but lies on no chord. A chord
`λ γ(s) + (1-λ) γ(t)` with `y = z` needs `λ s²(1-s²) + (1-λ) t²(1-t²) = 0`, so each atom is `-1`,
`0` or `1`, and the first moment `0` and second moment `2/3` cannot both hold. So the chord set is
not convex, hence not the convex hull of `pZ`. (The moment curve `(t, t², t³)` is no example: its
chords appear to fill the hull.) Read from the source, not run.

## References

* [1] `contSet/@polyZonotope/convHull_.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The curve `(t, t², t⁴)`, `t ∈ [-1, 1]`, as a polynomial zonotope: one factor, three
generators, and no independent ones. -/
theorem PolyZonotope.aux_curve_mem (x : Fin 3 → ℝ) :
    x ∈ (⟨1, 3, 0, 0, ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1],
        fun _ j => ![1, 2, 4] j, Fin.elim0⟩ : PolyZonotope (Fin 3 → ℝ)).construct
      ↔ ∃ t : ℝ, |t| ≤ 1 ∧ x = ![t, t ^ 2, t ^ 4] := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, ha, -, rfl⟩
    refine ⟨a 0, ha 0, ?_⟩
    funext i
    fin_cases i <;> simp [PolyZonotope.monomial, Fin.sum_univ_three]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun _ => t, Fin.elim0, fun _ => ht, fun j => j.elim0, ?_⟩
    funext i
    fin_cases i <;> simp [PolyZonotope.monomial, Fin.sum_univ_three]

/-- No chord of the curve reaches `(0, 2/3, 2/3)`: the third coordinate forces every atom to
`-1`, `0` or `1`, and then the first two coordinates cannot match. -/
theorem PolyZonotope.aux_no_chord (s t lam : ℝ) (hs : |s| ≤ 1) (ht : |t| ≤ 1) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (hx : lam * s + (1 - lam) * t = 0) (hy : lam * s ^ 2 + (1 - lam) * t ^ 2 = 2 / 3)
    (hz : lam * s ^ 4 + (1 - lam) * t ^ 4 = 2 / 3) : False := by -- --- PROOF ---
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [abs_le.mp hs]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_le.mp ht]
  -- `y - z` is a sum of two nonnegative terms, so both vanish
  have e1 : 0 ≤ lam * (s ^ 2 * (1 - s ^ 2)) :=
    mul_nonneg h0 (mul_nonneg (sq_nonneg s) (by linarith))
  have e2 : 0 ≤ (1 - lam) * (t ^ 2 * (1 - t ^ 2)) :=
    mul_nonneg (by linarith) (mul_nonneg (sq_nonneg t) (by linarith))
  have f1 : lam * (s ^ 2 * (1 - s ^ 2)) = 0 := by
    have : lam * (s ^ 2 * (1 - s ^ 2)) + (1 - lam) * (t ^ 2 * (1 - t ^ 2)) = 0 := by
      linear_combination hy - hz
    linarith
  have f2 : (1 - lam) * (t ^ 2 * (1 - t ^ 2)) = 0 := by
    have : lam * (s ^ 2 * (1 - s ^ 2)) + (1 - lam) * (t ^ 2 * (1 - t ^ 2)) = 0 := by
      linear_combination hy - hz
    linarith
  -- an atom with positive weight is `0` or `±1`: `a² = 0` or `a² = 1`
  have atom : ∀ a : ℝ, a ^ 2 * (1 - a ^ 2) = 0 → a ^ 2 = 0 ∨ a ^ 2 = 1 := fun a ha =>
    (mul_eq_zero.mp ha).imp id (fun h => by linarith)
  rcases mul_eq_zero.mp f1 with hl | hs'
  · -- `lam = 0`: `t² = 2/3` and `t²(1 - t²) = 0`
    subst hl
    have h23 : t ^ 2 = 2 / 3 := by linarith
    rcases atom t (by linarith) with h | h <;> rw [h23] at h <;> norm_num at h
  rcases mul_eq_zero.mp f2 with hl' | ht'
  · -- `lam = 1`: `s² = 2/3` and `s²(1 - s²) = 0`
    have hl1 : lam = 1 := by linarith
    subst hl1
    have h23 : s ^ 2 = 2 / 3 := by linarith
    rcases atom s hs' with h | h <;> rw [h23] at h <;> norm_num at h
  rcases atom s hs' with hs0 | hs1 <;> rcases atom t ht' with ht0 | ht1
  · -- both atoms `0`
    rw [hs0, ht0] at hy
    norm_num at hy
  · -- `s = 0`, `t² = 1`: the weight of `t` is `2/3`, and the mean `(2/3) t` is not `0`
    rw [hs0, ht1] at hy
    have s0 : s = 0 := pow_eq_zero_iff (by norm_num) |>.mp hs0
    rw [s0] at hx
    have h3 : (1 - lam) * t = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · rw [h] at ht1; norm_num at ht1
  · -- `s² = 1`, `t = 0`
    rw [hs1, ht0] at hy
    have t0 : t = 0 := pow_eq_zero_iff (by norm_num) |>.mp ht0
    rw [t0] at hx
    have h3 : lam * s = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · rw [h] at hs1; norm_num at hs1
  · -- both `±1`: the second moment is `1`
    rw [hs1, ht1] at hy
    norm_num at hy


-- =======================================  MAIN THEOREM  ======================================= --

/-- The chord set `linComb(pZ, pZ)` is not convex, so it is not the convex hull of `pZ`. -/
theorem PolyZonotope.convHull_cora_counterexample :
    ∃ pZ : PolyZonotope (Fin 3 → ℝ), ¬ Convex ℝ (pZ.linComb pZ).construct
      ∧ (pZ.linComb pZ).construct ≠ convexHull ℝ pZ.construct := by -- --- PROOF ---
  set pZ : PolyZonotope (Fin 3 → ℝ) := ⟨1, 3, 0, 0, ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1],
    fun _ j => ![1, 2, 4] j, Fin.elim0⟩ with hpZ
  -- the chord set is not convex
  have hnc : ¬ Convex ℝ (pZ.linComb pZ).construct := by
    intro hconv
    rw [← PolyZonotope.linComb_exact_of_dependent pZ pZ rfl rfl] at hconv
    -- the chord from `γ(1)` to `γ(-1)` has midpoint `(0, 1, 1)`, and `γ(0) = 0` is a chord point
    have hM : (![0, 1, 1] : Fin 3 → ℝ) ∈ segments pZ.construct pZ.construct :=
      ⟨![1, 1, 1], (PolyZonotope.aux_curve_mem _).mpr ⟨1, by simp, by simp⟩,
        ![-1, 1, 1], (PolyZonotope.aux_curve_mem _).mpr
          ⟨-1, by simp, by funext i; fin_cases i <;> norm_num⟩,
        1 / 2, ⟨by norm_num, by norm_num⟩, by funext i; fin_cases i <;> norm_num⟩
    have hO : (0 : Fin 3 → ℝ) ∈ segments pZ.construct pZ.construct :=
      ⟨0, (PolyZonotope.aux_curve_mem _).mpr ⟨0, by simp, by funext i; fin_cases i <;> simp⟩,
        0, (PolyZonotope.aux_curve_mem _).mpr ⟨0, by simp, by funext i; fin_cases i <;> simp⟩,
        1, ⟨by norm_num, by norm_num⟩, by simp⟩
    -- two thirds of the first and a third of the second would be a chord point
    obtain ⟨y₁, hy₁, y₂, hy₂, lam, ⟨hl0, hl1⟩, hq⟩ :=
      hconv hM hO (a := 2 / 3) (b := 1 / 3) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨s, hs, rfl⟩ := (PolyZonotope.aux_curve_mem _).mp hy₁
    obtain ⟨t, ht, rfl⟩ := (PolyZonotope.aux_curve_mem _).mp hy₂
    have c0 := congrFun hq 0
    have c1 := congrFun hq 1
    have c2 := congrFun hq 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Pi.zero_apply] at c0 c1 c2
    exact PolyZonotope.aux_no_chord s t lam hs ht hl0 hl1 (by linarith) (by linarith)
      (by linarith)
  refine ⟨pZ, hnc, fun h => hnc ?_⟩
  rw [h]
  exact convex_convexHull ℝ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
