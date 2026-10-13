module

public import CORALean.ContSet.Zonotope.Real.Operations.UnderS
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The under-approximation is the convex hull of the extremal points

[1, Sec. 5.1]: `Z̲ = ConvexHull({u ± gᵢ, i ∈ {1, …, ℓ}}) = {u + Σᵢ αᵢgᵢ : Σᵢ |αᵢ| ≤ 1}`. The
second set is convex and holds every `u ± gᵢ` (`α = ±eᵢ`), so it holds the hull. Back,
`u + Σᵢ αᵢgᵢ` is the convex combination of the points `u + sign(αᵢ)gᵢ` with weights `|αᵢ|`
and of `u`, the midpoint of `u ± g₁`, with weight `1 - Σᵢ |αᵢ|`. That needs a direction:
at `ℓ = 0` the hull is empty and the second set is `{u}`, so `0 < ℓ` is assumed.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n ℓ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.1]: for `ℓ > 0`, `{u + Σᵢ αᵢgᵢ : Σᵢ |αᵢ| ≤ 1} = ConvexHull({u ± gᵢ})`. -/
theorem Zonotope.underS_eq_convexHull (Z : Zonotope (Vec ℝ n)) (s : Fin ℓ → Vec ℝ n)
    (hℓ : 0 < ℓ) :
    Z.underS s = convexHull ℝ {x | ∃ i, x = Z.c + Z.extremalGen (s i) ∨
      x = Z.c - Z.extremalGen (s i)} := by -- --- PROOF ---
  set g := fun i => Z.extremalGen (s i) with hg
  set C := {x | ∃ i, x = Z.c + g i ∨ x = Z.c - g i}
  apply Set.eq_of_subset_of_subset
  · -- `u + Σᵢ αᵢgᵢ` as a convex combination of `u` and the `u + sign(αᵢ)gᵢ`
    rintro x ⟨α, hα, rfl⟩
    have hK := convex_convexHull ℝ C
    have hpm : ∀ i, Z.c + g i ∈ convexHull ℝ C ∧ Z.c - g i ∈ convexHull ℝ C := fun i =>
      ⟨subset_convexHull ℝ C ⟨i, Or.inl rfl⟩, subset_convexHull ℝ C ⟨i, Or.inr rfl⟩⟩
    -- `u` is the midpoint of `u ± g₀`
    have hu : Z.c ∈ convexHull ℝ C := by
      have h := hK (hpm ⟨0, hℓ⟩).1 (hpm ⟨0, hℓ⟩).2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      convert h using 1
      module
    -- `σᵢ = sign(αᵢ)`, so `|αᵢ| σᵢ = αᵢ` and `u + σᵢgᵢ` is one of the points
    set σ : Fin ℓ → ℝ := fun i => if 0 ≤ α i then 1 else -1
    have hσ : ∀ i, |α i| * σ i = α i := fun i => by
      simp only [σ]; split_ifs with h
      · rw [abs_of_nonneg h, mul_one]
      · rw [abs_of_neg (not_le.mp h)]; ring
    have hz : ∀ i, Z.c + σ i • g i ∈ convexHull ℝ C := fun i => by
      simp only [σ]; split_ifs
      · simpa using (hpm i).1
      · simpa [sub_eq_add_neg] using (hpm i).2
    -- weight `1 - Σᵢ |αᵢ|` on `u`, `|αᵢ|` on `u + σᵢgᵢ`
    let w : Option (Fin ℓ) → ℝ := fun o => o.elim (1 - ∑ i, |α i|) fun i => |α i|
    let z : Option (Fin ℓ) → Vec ℝ n := fun o => o.elim Z.c fun i => Z.c + σ i • g i
    have hmem := hK.sum_mem (t := Finset.univ) (w := w) (z := z)
      (fun o _ => by cases o <;> simp [w, hα, abs_nonneg])
      (by simp [w, Fintype.sum_option])
      (fun o _ => by cases o <;> simp [z, hu, hz])
    convert hmem using 1
    simp only [Fintype.sum_option, w, z, Option.elim, smul_add, Finset.sum_add_distrib,
      smul_smul, hσ, ← Finset.sum_smul]
    rw [sub_smul, one_smul]
    abel
  · -- the `α` form is convex and holds every `u ± gᵢ`
    refine convexHull_min ?_ ?_
    · rintro _ ⟨i, rfl | rfl⟩
      · exact ⟨fun k => if k = i then 1 else 0, by simp [apply_ite, Finset.sum_ite_eq'],
          by simp [ite_smul, Finset.sum_ite_eq', g]⟩
      · exact ⟨fun k => if k = i then -1 else 0, by simp [apply_ite, Finset.sum_ite_eq'],
          by simp [ite_smul, Finset.sum_ite_eq', g, sub_eq_add_neg]⟩
    · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ a b ha hb hab
      refine ⟨fun i => a * α i + b * β i, ?_, ?_⟩
      · -- `Σ |aαᵢ + bβᵢ| ≤ a Σ |αᵢ| + b Σ |βᵢ| ≤ 1`
        calc ∑ i, |a * α i + b * β i| ≤ ∑ i, (a * |α i| + b * |β i|) :=
              Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans (by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb])
          _ = a * ∑ i, |α i| + b * ∑ i, |β i| := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hα ha)
              (mul_le_mul_of_nonneg_left hβ hb)
          _ = 1 := by rw [mul_one, mul_one, hab]
      · simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
        conv_rhs => rw [show Z.c = (a + b) • Z.c by rw [hab, one_smul]]
        rw [add_smul]
        abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
