import CORALean.NN.Layers.Definitions.EvalPoly

/-!
# Padding changes no value of a polynomial

ℝ-only, the padding being exact: every added term is `0 · t ^ j`. That exactness is why a common
degree is no restriction, and what makes a layer's relaxations `Fin n → PolyRelaxation 𝕋 M`
rather than a ragged family.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPoly_padCoeffs {k M : ℕ} (c : Fin (k + 1) → ℝ) (h : k ≤ M) (t : ℝ) :
    evalPoly (padCoeffs c M) t = evalPoly c t := by -- --- PROOF ---
  -- both sides are one sum over ℕ, cut at a different length
  have hL : evalPoly (padCoeffs c M) t
      = ∑ j ∈ Finset.range (M + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j := by
    show (∑ i : Fin (M + 1), (if hj : (i : ℕ) < k + 1 then c ⟨(i : ℕ), hj⟩ else 0) * t ^ (i : ℕ))
      = _
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j) (M + 1)
  have hfin : (∑ i : Fin (k + 1),
        (if hj : (i : ℕ) < k + 1 then c ⟨(i : ℕ), hj⟩ else 0) * t ^ (i : ℕ))
      = ∑ j ∈ Finset.range (k + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j :=
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j) (k + 1)
  have hR : (∑ j ∈ Finset.range (k + 1), (if hj : j < k + 1 then c ⟨j, hj⟩ else 0) * t ^ j)
      = evalPoly c t := by
    rw [← hfin]
    -- inside `k + 1` the padding branch is never taken
    show _ = ∑ i : Fin (k + 1), c i * t ^ (i : ℕ)
    exact Finset.sum_congr rfl fun j _ => by rw [dif_pos j.isLt]
  rw [hL, ← hR]
  -- and past `k + 1` the padded coefficient is zero, so the term drops out
  have hsub : Finset.range (k + 1) ⊆ Finset.range (M + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  refine (Finset.sum_subset hsub ?_).symm
  intro j _ hj
  rw [dif_neg (by simpa using hj), zero_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
