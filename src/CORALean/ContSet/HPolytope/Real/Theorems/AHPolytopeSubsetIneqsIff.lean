module

public import CORALean.ContSet.HPolytope.Real.Theorems.AHPolytopeSubsetOfCert
public import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIff

@[expose] public section

/-!
# AH-polytope in H-polytope, exactly

`[1, Cor. 2]`: the case `Y = I`, `ȳ = 0` of `[1, Cor. 1]`, where the circumbody `Py` is an
H-polytope. The conditions (12) of `[1, Thm. 1]` are then necessary and sufficient, and are
linear in `Γ, β, Λ`: a linear program. "Only if" is `ineqs_subset_iff` on
`Px ⊆ {Hy X p ≤ hy - Hy x̄}`, so it needs `Px` nonempty, which is weaker than the
full-dimensionality `[1, Cor. 1]` asks for.

## Inputs
* `xbar` – mean of length `n`
* `X` – `n × nx` matrix
* `Hx` – `qx × nx` matrix
* `hx` – vector of length `qx`
* `Hy` – `qy × n` matrix
* `hy` – vector of length `qy`

## Hypotheses
* `hne` – the polytope `ineqs Hx hx` is nonempty

## Conclusion
* [1, Cor. 2]: `x̄ + X Px ⊆ Py` iff (12) of [1, Thm. 1] holds at `Y = I`, `ȳ = 0`

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx qx qy : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 2]: `x̄ + X Px ⊆ Py` iff (12) of [1, Thm. 1] holds at `Y = I`, `ȳ = 0`. -/
theorem HPolytope.ahPolytope_subset_ineqs_iff {xbar : Vec ℝ n} {X : Mat ℝ n nx}
    {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : Mat ℝ qy n} {hy : Vec ℝ qy}
    (hne : (HPolytope.ineqs Hx hx).construct.Nonempty) : -- --- CONCL ---
    HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx) ⊆ (HPolytope.ineqs Hy hy).construct ↔
      ∃ (Γ : Mat ℝ n nx) (β : Vec ℝ n) (Λ : Mat ℝ qy qx), X = (1 : Mat ℝ n n) * Γ ∧
        0 - xbar = (1 : Mat ℝ n n) *ᵥ β ∧ (∀ i j, 0 ≤ Λ i j) ∧ Λ * Hx = Hy * Γ ∧
          Λ *ᵥ hx ≤ hy + Hy *ᵥ β := by -- --- PROOF ---
  constructor
  · intro hsub
    -- `Px` lies in the H-polytope `{Hy X p ≤ hy - Hy x̄}`, so Lemma 1 gives `Λ`
    have hPx : (HPolytope.ineqs Hx hx).construct
        ⊆ (HPolytope.ineqs (Hy * X) (hy - Hy *ᵥ xbar)).construct := by
      intro p hp
      have hmem := hsub ⟨p, hp, rfl⟩
      rw [HPolytope.mem_ineqs_iff] at hmem ⊢
      intro i
      have := hmem i
      rw [mulVec_add, Pi.add_apply] at this
      rw [← mulVec_mulVec, Pi.sub_apply]
      linarith
    obtain ⟨Λ, hΛ, h1, h2⟩ := (HPolytope.ineqs_subset_iff hne).mp hPx
    refine ⟨X, -xbar, Λ, by simp, by simp, hΛ, h1, ?_⟩
    rw [mulVec_neg]
    intro i
    have := h2 i
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply, Pi.neg_apply]
    linarith
  · rintro ⟨Γ, β, Λ, hX, hβ, hΛ, h1, h2⟩
    intro x hx'
    -- Thm. 1 with `Y = I`, `ȳ = 0` puts `x` in `0 + I Py`
    obtain ⟨q, hq, hxq⟩ := HPolytope.ahPolytope_subset_of_cert (ybar := 0) (Y := 1)
      (Hy := Hy) (hy := hy) hX hβ hΛ h1 h2 hx'
    rw [hxq]
    simpa using hq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
