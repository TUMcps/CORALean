module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The solution from `H` reads the data at `H` only

A step of [1, Thm. 3] and [1, Thm. 4]: when Problem 1′ with the constraints `H` has a unique
solution `Î_H` for all data, data agreeing on `H` give the same `Î_H`, as they give the same
problem. The proof's `Î_H` is so a function of the `d` data it is computed from.
## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipm_sol_congr {E Φ Y : Type} {N : ℕ} {𝒬 : Set E} {μQ : E → ℝ} {I : E → Φ → Set Y}
    {sol : Finset (Fin N) → (Fin N → Φ × Y) → E} {H : Finset (Fin N)}
    (hsol : ∀ x, sol H x ∈ 𝒬 ∧ (∀ t ∈ H, (x t).2 ∈ I (sol H x) (x t).1) ∧
      ∀ Q ∈ 𝒬, (∀ t ∈ H, (x t).2 ∈ I Q (x t).1) → Q ≠ sol H x → μQ (sol H x) < μQ Q)
    {x x' : Fin N → Φ × Y} (hxx : ∀ t ∈ H, x t = x' t) : -- --- STMT ---
    sol H x = sol H x' := by -- --- PROOF ---
  by_contra hne
  obtain ⟨h1, h2, h3⟩ := hsol x
  obtain ⟨h1', h2', h3'⟩ := hsol x'
  -- each solution is feasible for the other problem, and strictly worse there
  have a := h3 (sol H x') h1' (fun t ht => hxx t ht ▸ h2' t ht) (Ne.symm hne)
  have b := h3' (sol H x) h1 (fun t ht => (hxx t ht).symm ▸ h2 t ht) hne
  exact lt_asymm a b

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
