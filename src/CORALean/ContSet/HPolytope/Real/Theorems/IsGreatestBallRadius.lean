module

public import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
public import CORALean.Global.EuclideanNorm
public import Mathlib.Order.Lattice

@[expose] public section

/-!
# The largest ball around the origin in an H-polytope

[1, Def. 4] defines `⌊Z⌋² = min(b²)` from the halfspace representation `{A z ≤ b}` of `Z(G, 0)`
and derives it, [1, Eq. 10], as the squared radius of the largest ball around the centre inside
`Z`. That needs unit rows, which the derivation assumes ("if we assume that `aᵢ` is normed") and
the definition leaves out: a ball of radius `s` lies in `aᵀ x ≤ b` iff `s ‖a‖₂ ≤ b`. With unit
rows and `b ≥ 0` — the origin inside — the largest radius is `min b`, and its square `min(b²)`.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isGreatest_ball_radius (A : Mat ℝ q n) (b : Vec ℝ q) (hq : 0 < q)
    (hA : ∀ i, ‖A i‖₂ = 1) (hb : 0 ≤ b) :
    IsGreatest {s | 0 ≤ s ∧ ∀ x : Vec ℝ n, ‖x‖₂ ≤ s → x ∈ (HPolytope.ineqs A b).construct}
        (Finset.univ.inf' ⟨⟨0, hq⟩, Finset.mem_univ _⟩ b) ∧
      (Finset.univ.inf' ⟨⟨0, hq⟩, Finset.mem_univ _⟩ b) ^ 2 =
        Finset.univ.inf' ⟨⟨0, hq⟩, Finset.mem_univ _⟩ fun i => b i ^ 2 := by -- --- PROOF ---
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' hne b
  refine ⟨⟨⟨?_, fun x hx => HPolytope.mem_ineqs_iff.mpr fun i => ?_⟩, ?_⟩, ?_⟩
  · rw [hi₀]
    exact hb i₀
  -- Cauchy–Schwarz against each unit row
  · calc (A *ᵥ x) i = A i ⬝ᵥ x := rfl
      _ ≤ ‖A i‖₂ * ‖x‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
      _ = ‖x‖₂ := by rw [hA i, one_mul]
      _ ≤ _ := hx
      _ ≤ b i := Finset.inf'_le _ (Finset.mem_univ i)
  -- a larger ball pokes through the row with the least offset, at `s aᵢ`
  · rintro s ⟨hs, hball⟩
    rw [hi₀]
    have hmem := HPolytope.mem_ineqs_iff.mp (hball (s • A i₀) (by
      rw [norm₂_smul, hA i₀, mul_one, abs_of_nonneg hs])) i₀
    have : (A *ᵥ (s • A i₀)) i₀ = s * ‖A i₀‖₂ ^ 2 := by
      show A i₀ ⬝ᵥ (s • A i₀) = _
      rw [dotProduct_smul, dotProduct_self, smul_eq_mul]
    rw [this, hA i₀] at hmem
    simpa using hmem
  -- squaring is monotone on `b ≥ 0`
  · obtain ⟨i₁, -, hi₁⟩ := Finset.exists_mem_eq_inf' hne fun i => b i ^ 2
    rw [hi₀, hi₁]
    refine le_antisymm (pow_le_pow_left₀ (hb i₀) ?_ 2) ?_
    · rw [← hi₀]
      exact Finset.inf'_le _ (Finset.mem_univ i₁)
    · rw [← hi₁]
      exact Finset.inf'_le (fun i => b i ^ 2) (Finset.mem_univ i₀)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
