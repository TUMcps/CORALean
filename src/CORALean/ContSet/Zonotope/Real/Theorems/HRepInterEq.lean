module

public import CORALean.ContSet.Zonotope.Real.Operations.Shift
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq

@[expose] public section

/-!
# [1, Lemma 2]: the two translates, intersected

`Z_o = (c - h, G)` and `Z_t = (c + h, G)` meet in the halfspaces [1, Thm. 2]
gives `(c, G)`, with the offset lowered by `Δd_trans = |C h|` and nothing else
changed — the `C` is the same matrix, which is the point of the lemma.

One line of arithmetic once `Thm. 2` is available: `|A + H| ≤ Δ` and
`|A - H| ≤ Δ` together say exactly `|A| ≤ Δ - |H|`, whichever way `H` points.
Translation is `Zonotope.shift`, whose sign convention makes `Z.shift w` the
translate by `-w`, so `Z_o` is `Z.shift h` and `Z_t` is `Z.shift (-h)`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Δd_trans` in one line: both translates fit iff the centred one fits with
`|H|` to spare. -/
theorem aux_abs_add_sub (A H Δ : ℝ) :
    (|A + H| ≤ Δ ∧ |A - H| ≤ Δ) ↔ |A| ≤ Δ - |H| := by -- --- PROOF ---
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [abs_le] at h₁ h₂ ⊢
    rcases abs_cases H with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;>
      exact ⟨by linarith [h₁.1, h₁.2, h₂.1, h₂.2], by linarith [h₁.1, h₁.2, h₂.1, h₂.2]⟩
  · intro hle
    rw [abs_le] at hle
    have h₁ := neg_abs_le A
    have h₂ := le_abs_self A
    have h₃ := neg_abs_le H
    have h₄ := le_abs_self H
    exact ⟨abs_le.mpr ⟨by linarith [hle.1, hle.2], by linarith [hle.1, hle.2]⟩,
      abs_le.mpr ⟨by linarith [hle.1, hle.2], by linarith [hle.1, hle.2]⟩⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 2]: the intersection of the two translates, at the same `C` as
[1, Thm. 2] and the offset lowered by `Δd_trans = |C h|`. -/
theorem Zonotope.hRep_inter_eq {n : ℕ} (Z : Zonotope (Vec ℝ (n + 1))) (h : Vec ℝ (n + 1))
    (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤) :
    (Z.shift h).construct ∩ (Z.shift (-h)).construct
      = {x | ∀ S : Fin n → Fin Z.h, |Z.facetNormal S ⬝ᵥ (x - Z.c)|
          ≤ (∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ|) - |Z.facetNormal S ⬝ᵥ h|} := by -- --- PROOF ---
  rw [(Z.shift h).hRep_eq hspan, (Z.shift (-h)).hRep_eq hspan]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Zonotope.shift, Zonotope.facetNormal]
  -- one `S` at a time, with the translation split off the pairing
  have e₁ : ∀ p : Vec ℝ (n + 1), p ⬝ᵥ (x - (Z.c - h)) = p ⬝ᵥ (x - Z.c) + p ⬝ᵥ h := by
    intro p; rw [← dotProduct_add]; congr 1; abel
  have e₂ : ∀ p : Vec ℝ (n + 1), p ⬝ᵥ (x - (Z.c - -h)) = p ⬝ᵥ (x - Z.c) - p ⬝ᵥ h := by
    intro p; rw [← dotProduct_sub]; congr 1; abel
  rw [← forall_and]
  refine forall_congr' fun S => ?_
  rw [e₁, e₂]
  exact aux_abs_add_sub _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
