module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriSumSqSplit

@[expose] public section

/-!
# The ordered pairs of `Fin (N + 1)`, numbered as `Zonotope.quadMapTri` numbers them

The double sum over `Fin (N + 1)` is the diagonal plus, once for each entry below it, both orders,
the entries numbered by columns (`step_quadMapTriRow`, `step_quadMapTriCol`) as `quadMapTri`
numbers its generators. From `quadMapTri_sum_sq_split` through `finSigmaFinEquiv`.

## Inputs
* `N` – number of generators
* `f` – the summand

## Hypotheses
* none

## Conclusion
* the double sum splits into the diagonal and the numbered entries below it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Finset


-- =======================================  MAIN THEOREM  ======================================= --

/-- `quadMapTri_sum_sq_split` over `Fin (N + 1)`, the entries below the diagonal numbered by
columns as `quadMapTri` does. -/
theorem Zonotope.quadMapTri_pairs_split (N : ℕ)
    (f : Fin (N + 1) → Fin (N + 1) → ℝ) : -- --- CONCL ---
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ u : Fin (Zonotope.step_quadMapTriPairs N),
      (f (Zonotope.step_quadMapTriRow N u) (Zonotope.step_quadMapTriCol N u) +
        f (Zonotope.step_quadMapTriCol N u)
          (Zonotope.step_quadMapTriRow N u)) := by -- --- PROOF ---
  set F : ℕ → ℕ → ℝ := fun a b => if h : a < N + 1 ∧ b < N + 1 then f ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
    with hF
  have hf : ∀ a b : Fin (N + 1), f a b = F a.val b.val := fun a b => by
    simp only [hF]; rw [dif_pos ⟨a.2, b.2⟩]
  -- the pairs, by the column `j` and the place `t` in it
  have hu : ∀ u : Fin (Zonotope.step_quadMapTriPairs N),
      f (Zonotope.step_quadMapTriRow N u) (Zonotope.step_quadMapTriCol N u) +
        f (Zonotope.step_quadMapTriCol N u) (Zonotope.step_quadMapTriRow N u)
      = (fun σ : Σ j : Fin N, Fin (N - j.val) =>
          F (σ.1.val + 1 + σ.2.val) σ.1.val + F σ.1.val (σ.1.val + 1 + σ.2.val))
        (finSigmaFinEquiv.symm u) := fun u => by
    simp only [Zonotope.step_quadMapTriRow, Zonotope.step_quadMapTriCol, hf]
  rw [Finset.sum_congr rfl fun u _ => hu u]
  have hσ := Equiv.sum_comp finSigmaFinEquiv.symm (fun σ : Σ j : Fin N, Fin (N - j.val) =>
          F (σ.1.val + 1 + σ.2.val) σ.1.val + F σ.1.val (σ.1.val + 1 + σ.2.val))
  rw [hσ, Fintype.sum_sigma]
  -- both sides in ranges
  have hl : ∑ a : Fin (N + 1), ∑ b : Fin (N + 1), f a b
      = ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), F a b := by
    simp_rw [hf]
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (N + 1), F a b.val) (N + 1)]
    exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => F a b) (N + 1)
  have hd : ∑ a : Fin (N + 1), f a a = ∑ a ∈ range (N + 1), F a a := by
    simp_rw [hf]
    exact Fin.sum_univ_eq_sum_range (fun a => F a a) (N + 1)
  have hp : ∑ j : Fin N, ∑ t : Fin (N - j.val),
        (F (j.val + 1 + t.val) j.val + F j.val (j.val + 1 + t.val))
      = ∑ j ∈ range N, ∑ t ∈ range (N - j), (F (j + 1 + t) j + F j (j + 1 + t)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ∑ t ∈ range (N - j),
      (F (j + 1 + t) j + F j (j + 1 + t))) N |>.symm]
    exact Finset.sum_congr rfl fun j _ =>
      Fin.sum_univ_eq_sum_range (fun t => F (j.val + 1 + t) j.val + F j.val (j.val + 1 + t))
        (N - j.val)
  rw [hl, hd, hp]
  exact Zonotope.quadMapTri_sum_sq_split F N

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
