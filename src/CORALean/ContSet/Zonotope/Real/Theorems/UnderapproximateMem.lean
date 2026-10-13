module

public import CORALean.ContSet.Zonotope.Real.Operations.Underapproximate

@[expose] public section

/-!
# `underapproximate` returns points of the zonotope

Every point `underapproximate` returns is a point of the zonotope: the coefficients are the signs
`±1` or `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inner: every returned vertex lies in the zonotope. -/
theorem Zonotope.underapproximate_mem {n k : ℕ} (Z : Zonotope (Vec ℝ n)) (S : Fin k → Vec ℝ n)
    (i : Fin k) (b : Bool) : Z.underapproximate S i b ∈ Z.construct := by -- --- PROOF ---
  have hs : ∀ x : ℝ, |((SignType.sign x : SignType) : ℝ)| ≤ 1 := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  refine ⟨fun j => (if b then (1 : ℝ) else -1) * ((SignType.sign (S i ⬝ᵥ Z.G j) : SignType) : ℝ),
    fun j => ?_, ?_⟩
  · rw [abs_mul]
    have : |(if b then (1 : ℝ) else -1)| = 1 := by cases b <;> simp
    rw [this, one_mul]; exact hs _
  · simp only [Zonotope.underapproximate, Finset.smul_sum, smul_smul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
