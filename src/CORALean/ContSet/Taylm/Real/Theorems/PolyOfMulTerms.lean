import CORALean.ContSet.Taylm.Real.Operations.MulTerms

/-!
# The product list evaluates to the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_mulTerms (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) :
    Taylm.polyOf (Taylm.mulTerms L₁ L₂) t
      = Taylm.polyOf L₁ t * Taylm.polyOf L₂ t := by -- --- PROOF ---
  induction L₁ with
  | nil => simp [Taylm.mulTerms]
  | cons a L₁ ih =>
    -- one row of the product: `a` times the whole second list
    have hin : ∀ L : List (ℝ × (Fin n → ℕ)),
        Taylm.polyOf (L.map fun b => (a.1 * b.1, a.2 + b.2)) t
          = a.1 * Taylm.monomial a.2 t * Taylm.polyOf L t := by
      intro L
      induction L with
      | nil => simp
      | cons b L ihL => simp [ihL, Taylm.monomial_add]; ring
    simp only [Taylm.mulTerms, List.flatMap_cons, Taylm.polyOf_append, Taylm.polyOf_cons] at *
    rw [hin, ih]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
