module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.VolumeEqSquare
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A zonotope is at least as large as the determinant of any n generators

[1, Sec. 4.2]: for a full-dimensional zonotope, `n` linearly independent generators
`G = (g_{j₁}, …, g_{jₙ})` give `vol(Z) ≥ |det G|`. The zonotope on those `n` generators lies in
`Z` and has volume `2ⁿ |det G|` (`Zonotope.volume_eq_of_h_eq`), the one `n`-subset being all
of them; it holds for any injective choice of `n` columns.

## Inputs
* `Z` – zonotope
* `J` – choice of `n` generator indices

## Hypotheses
* `hJ` – indices distinct

## Conclusion
* generator determinant is at most the volume of `Z`

## References

* [1] [M. Černý. "Goffin's algorithm for zonotopes". Kybernetika,
      2012.](../../../../../../references/2012/cerny-kybernetika-goffin-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2]: `|det (g_{j₁}, …, g_{jₙ})| ≤ vol(Z)` for distinct generators `j₁, …, jₙ`. -/
theorem Zonotope.abs_det_le_volume (Z : Zonotope (Vec ℝ n)) (J : Fin n → Fin Z.h)
    (hJ : Function.Injective J) : -- --- CONCL ---
    ENNReal.ofReal |(Matrix.of fun i k => Z.G (J k) i : Mat ℝ n n).det|
      ≤ MeasureTheory.volume Z.construct := by -- --- PROOF ---
  set Z' : Zonotope (Vec ℝ n) := ⟨n, Z.c, fun k => Z.G (J k)⟩ with hZ'
  -- the sub-zonotope on the chosen generators lies in `Z`
  have hsub : Z'.construct ⊆ Z.construct := by
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨Function.extend J β 0, fun j => ?_, ?_⟩
    · by_cases hj : ∃ k, J k = j
      · obtain ⟨k, rfl⟩ := hj
        rw [hJ.extend_apply]; exact hβ k
      · rw [Function.extend_apply' _ _ _ hj]; simp
    · -- only the terms in the range of `J` survive
      congr 1
      symm
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image J)) ?_,
        Finset.sum_image fun a _ b _ h => hJ h]
      · exact Finset.sum_congr rfl fun k _ => by rw [hJ.extend_apply]
      · intro j _ hj
        have : ¬ ∃ k, J k = j := by
          rintro ⟨k, rfl⟩; exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ k))
        rw [Function.extend_apply' _ _ _ this]; simp
  refine le_trans ?_ (MeasureTheory.measure_mono hsub)
  rw [Zonotope.volume_eq_of_h_eq Z' rfl]
  unfold Zonotope.volume
  refine ENNReal.ofReal_le_ofReal ?_
  -- among the `n`-subsets is `univ`, taken in order, and `2ⁿ ≥ 1`
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hemb : ∀ k, (Finset.univ : Finset (Fin n)).orderEmbOfFin hcard k = k := by
    intro k
    have := Finset.orderEmbOfFin_unique hcard (f := id) (fun x => Finset.mem_univ x)
      strictMono_id
    exact (congrFun this k).symm
  have hnn : ∀ S : Finset (Fin n), 0 ≤ (if hS : S.card = n then
      |(Matrix.of fun i k => Z'.G (S.orderEmbOfFin hS k) i : Mat ℝ n n).det| else 0) := by
    intro S; split_ifs <;> positivity
  have hterm := Finset.single_le_sum (fun S _ => hnn S)
    (Finset.mem_univ (Finset.univ : Finset (Fin n)))
  simp only [dif_pos hcard, hemb] at hterm
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hpos : 0 ≤ ∑ S : Finset (Fin n), (if hS : S.card = n then
      |(Matrix.of fun i k => Z'.G (S.orderEmbOfFin hS k) i : Mat ℝ n n).det| else 0) :=
    Finset.sum_nonneg fun S _ => hnn S
  calc |(Matrix.of fun i k => Z.G (J k) i : Mat ℝ n n).det| ≤ _ := hterm
    _ ≤ 2 ^ n * _ := le_mul_of_one_le_left hpos h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
