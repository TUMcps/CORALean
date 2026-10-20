module

public import CORALean.ContSet.HPolytope.Real.Theorems.NaiveHalfspaceValueLe

@[expose] public section

/-!
# Naive halfspace sampling's `False` is certain

The first half of `[1, Cor. 4.8]`: `Ê ⊄ Ẑ` if `r_hs > 1`. By `[1, Eq. 12]` the sampled value is
at most the radius `r(Ê, Ẑ)`, the largest facet value over `Ê`, so a value above `1` is a
point of `Ê` beyond a facet of `Ẑ = d + Z(H)`. The second half, `Ê ⊆ Ẑ` "with probability at
least `P_S(1 - r_hs)`", fails (`HPolytope.naiveHalfspace_printed_counterexample`).

## Inputs
* `p` – `ℝ≥0∞`
* `G` – linear map
* `c` – center of length `n`
* `d` – direction of length `n`
* `Λ` – `s × n` matrix
* `b` – offset vector of length `s`
* `N` – natural number
* `j` – indices indexed by `Fin N`

## Hypotheses
* `hb` – `∀ i, 0 < b i`
* `hsym` – every row has an opposite row with the same bound
* `hN` – `0 < N`
* `h` – the naive halfspace value exceeds `1`

## Conclusion
* naive halfspace sampling's `False` is certain

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ENNReal

variable {n s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.naiveHalfspace_not_subset (p : ℝ≥0∞) [Fact (1 ≤ p)] (G : E →ₗ[ℝ] Vec ℝ n)
    (c d : Vec ℝ n) {Λ : Mat ℝ s n} {b : Vec ℝ s} (hb : ∀ i, 0 < b i)
    (hsym : ∀ i, ∃ i', (∀ x, (Λ *ᵥ x) i' = -(Λ *ᵥ x) i) ∧ b i' = b i) {N : ℕ} (hN : 0 < N)
    (j : Fin N → Fin s) (h : 1 < HPolytope.naiveHalfspaceValue p G c d Λ b hN j) : -- --- CONCL ---
    ¬ {x | ∃ α : E, ‖α‖ ≤ 1 ∧ x = c + G α}
      ⊆ {x | ∀ i, (Λ *ᵥ (x - d)) i ≤ b i} := by -- --- PROOF ---
  -- the radius is attained at some `α`, and above `1`
  have hg := HPolytope.isGreatest_polyNorm_ellipsotope (Λ := Λ) G c d hb
  have hle := HPolytope.naiveHalfspaceValue_le p G c d hb hsym hg hN j
  obtain ⟨α, hα, hαr⟩ := hg.1
  have hgt : 1 < HPolytope.polyNorm Λ b (G α + c - d) := by
    have := lt_of_lt_of_le h hle
    rw [← hαr] at this
    exact this
  -- so some facet is violated
  have hv : ¬ ∀ i, (Λ *ᵥ (G α + c - d)) i / b i ≤ 1 := fun hall =>
    absurd (HPolytope.polyNorm_le_iff.mpr ⟨zero_le_one, hall⟩) (not_le.mpr hgt)
  simp only [not_forall, not_le] at hv
  obtain ⟨i, hi⟩ := hv
  intro hsub
  have := hsub ⟨α, by simpa using hα, rfl⟩ i
  rw [show c + G α - d = G α + c - d by abel] at this
  rw [lt_div_iff₀ (hb i)] at hi
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
