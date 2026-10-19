module

public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The points of `linComb Z (EZ)`, by their coefficients

`Zonotope.linComb Z (Z.mtimes E)` is the `P` of [1, Lemma 2] (eq. 5): center `(c + Ec)/2`,
generators `(gⱼ + Egⱼ)/2`, `(gⱼ - Egⱼ)/2` and `(c - Ec)/2`, the two blocks pairing column for
column since `Z` and `EZ` have the same number of generators. Its points are exactly
`(z + Ez)/2 + (z' - Ez')/2` for `z = c + Σ βⱼgⱼ` and `z' = m c + Σ γⱼgⱼ`, every coefficient in
`[-1, 1]` — the reading [1]'s proof of Lemma 2 gives a point of `P`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The point named by coefficients `κ`, written through the three blocks' own
coefficients. -/
theorem Zonotope.aux_linComb_mtimes_eq (Z : Zonotope (Vec ℝ n)) (E : Mat ℝ n n)
    (κ : Fin (Z.h + Z.h + 1) → ℝ) : -- --- CONCL ---
    (Z.linComb (Z.mtimes E)).c + ∑ j : Fin (Z.h + Z.h + 1), κ j • (Z.linComb (Z.mtimes E)).G j
      = (2:ℝ)⁻¹ • ((Z.c + ∑ j, κ (Fin.castAdd 1 (Fin.castAdd Z.h j)) • Z.G j)
          + E *ᵥ (Z.c + ∑ j, κ (Fin.castAdd 1 (Fin.castAdd Z.h j)) • Z.G j))
        + (2:ℝ)⁻¹ • ((κ (Fin.natAdd (Z.h + Z.h) 0) • Z.c
            + ∑ j, κ (Fin.castAdd 1 (Fin.natAdd Z.h j)) • Z.G j)
          - E *ᵥ (κ (Fin.natAdd (Z.h + Z.h) 0) • Z.c
            + ∑ j, κ (Fin.castAdd 1 (Fin.natAdd Z.h j)) • Z.G j)) := by -- --- PROOF ---
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [Zonotope.linComb, Zonotope.mtimes]
  simp only [Fin.append_left, Fin.append_right]
  -- each block's sum, against the two halves it contributes to
  have hS : ∑ j : Fin Z.h, κ (Fin.castAdd 1 (Fin.castAdd Z.h j))
        • Zonotope.pairSum Z.G (fun j => E *ᵥ Z.G j) j
      = (2:ℝ)⁻¹ • (∑ j, κ (Fin.castAdd 1 (Fin.castAdd Z.h j)) • Z.G j)
        + (2:ℝ)⁻¹ • (E *ᵥ ∑ j, κ (Fin.castAdd 1 (Fin.castAdd Z.h j)) • Z.G j) := by
    rw [Matrix.mulVec_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Zonotope.pairSum, Fin.is_lt, dite_true, Fin.eta, Matrix.mulVec_smul]
    module
  have hD : ∑ j : Fin Z.h, κ (Fin.castAdd 1 (Fin.natAdd Z.h j))
        • Zonotope.pairDiff Z.G (fun j => E *ᵥ Z.G j) j
      = (2:ℝ)⁻¹ • (∑ j, κ (Fin.castAdd 1 (Fin.natAdd Z.h j)) • Z.G j)
        - (2:ℝ)⁻¹ • (E *ᵥ ∑ j, κ (Fin.castAdd 1 (Fin.natAdd Z.h j)) • Z.G j) := by
    rw [Matrix.mulVec_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Zonotope.pairDiff, Fin.is_lt, dite_true, Fin.eta, Matrix.mulVec_smul]
    module
  rw [hS, hD]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  module


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2], eq. 5: a point of `P = linComb Z (EZ)` is `(z + Ez)/2 + (z' - Ez')/2`, `z`, `z'`
spanned by `Z`'s generators — `z'` with its center scaled by `m` — at coefficients in
`[-1, 1]`, and every such point is in `P`. -/
theorem Zonotope.mem_linComb_mtimes_iff {Z : Zonotope (Vec ℝ n)} {E : Mat ℝ n n}
    {p : Vec ℝ n} : -- --- CONCL ---
    p ∈ (Z.linComb (Z.mtimes E)).construct ↔
      ∃ β γ : Fin Z.h → ℝ, ∃ m : ℝ, (∀ j, |β j| ≤ 1) ∧ (∀ j, |γ j| ≤ 1) ∧ |m| ≤ 1 ∧
        p = (2:ℝ)⁻¹ • ((Z.c + ∑ j, β j • Z.G j) + E *ᵥ (Z.c + ∑ j, β j • Z.G j))
          + (2:ℝ)⁻¹ • ((m • Z.c + ∑ j, γ j • Z.G j)
            - E *ᵥ (m • Z.c + ∑ j, γ j • Z.G j)) := by -- --- PROOF ---
  constructor
  · rintro ⟨κ, hκ, rfl⟩
    exact ⟨_, _, _, fun j => hκ _, fun j => hκ _, hκ _, Zonotope.aux_linComb_mtimes_eq Z E κ⟩
  · rintro ⟨β, γ, m, hβ, hγ, hm, rfl⟩
    -- the three blocks' coefficients, appended in the generators' order
    let κ : Fin (Z.h + Z.h + 1) → ℝ := Fin.append (Fin.append β γ) (fun _ : Fin 1 => m)
    have hκ : ∀ j, |κ j| ≤ 1 := by
      refine Fin.addCases (fun j => ?_) (fun _ => ?_)
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · simp only [κ, Fin.append_left]; exact hβ j
        · simp only [κ, Fin.append_left, Fin.append_right]; exact hγ j
      · simp only [κ, Fin.append_right]; exact hm
    refine ⟨κ, hκ, ?_⟩
    refine Eq.trans ?_ (Zonotope.aux_linComb_mtimes_eq Z E κ).symm
    simp only [κ, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
