module

public import CORALean.ContSet.SpectraShadow.Real.Operations.RepresentsaOrigin
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff

@[expose] public section

/-!
# `SpectraShadow.representsa_origin` is `{0}`

Every axis support is `0` exactly when the set is `{0}`, in a positive dimension: in dimension
`0` the loop is empty and CORA's `representsa_emptyObject` answers first.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* `hn` – `0 < n`

## Conclusion
* `representsa_origin` holds iff the shadow is `{0}`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.representsa_origin_iff (S : SpectraShadow (Vec ℝ n))
    (hn : 0 < n) : -- --- CONCL ---
    S.representsa_origin ↔ S.construct = {0} := by -- --- PROOF ---
  unfold SpectraShadow.representsa_origin
  constructor
  · intro h
    -- nonempty: the support in the first axis is `0`, not `⊥`
    have hne : S.construct ≠ ∅ := fun he =>
      absurd ((S.supportFunc_eq_bot_iff _).mpr he |>.symm.trans (h ⟨0, hn⟩).1) (by simp)
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    -- every member has both its coordinates' bounds at `0`
    have hzero : ∀ x ∈ S.construct, x = 0 := by
      intro x hx
      funext i
      have h1 := (S.le_supportFunc_of_mem (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) hx)
      have h2 := (S.le_supportFunc_of_mem (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) hx)
      rw [(h i).1] at h1
      rw [(h i).2] at h2
      have h1' : x i ≤ 0 := by simpa using h1
      have h2' : -x i ≤ 0 := by simpa using h2
      show x i = 0
      linarith
    ext x
    constructor
    · exact fun hx => hzero x hx
    · rintro rfl
      rw [← hzero x₀ hx₀]
      exact hx₀
  · -- the supremum over `{0}` is `0`
    intro h i
    constructor <;> simp [SpectraShadow.supportFunc, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
