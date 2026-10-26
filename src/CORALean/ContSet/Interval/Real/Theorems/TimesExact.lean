module

public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.IsNonempty

@[expose] public section

/-!
# `Interval.times` is exactly the set of entrywise products of nonempty boxes

`times_outer` is the inclusion; the other direction picks each coordinate's factors by
`aux_exists_mul_eq`. Needs both boxes nonempty: with a crossed coordinate the corner hull is an
interval nobody multiplies into.

[1, Eq. 2]: the product is the hull of the four corner products, exactly.

## Inputs
* `I` – first interval box
* `J` – second interval box

## Hypotheses
* `hI` – `I` nonempty
* `hJ` – `J` nonempty

## Conclusion
* the product box is exactly the set of entrywise products

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". ARCH16. 3rd
      International Workshop on Applied Verification for Continuous and Hybrid Systems, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every value between the corner products is a product. -/
private theorem Interval.aux_exists_mul_eq {a b c d z : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hz₁ : Interval.mulLo a b c d ≤ z) (hz₂ : z ≤ Interval.mulHi a b c d) : -- --- CONCL ---
    ∃ y x, (a ≤ y ∧ y ≤ b) ∧ (c ≤ x ∧ x ≤ d) ∧ y * x = z := by -- --- PROOF ---
  set S : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Set.Icc a b ×ˢ Set.Icc c d) with hSdef
  have hS : IsPreconnected S :=
    (isPreconnected_Icc.prod isPreconnected_Icc).image _ continuous_mul.continuousOn
  have mem : ∀ y x, a ≤ y → y ≤ b → c ≤ x → x ≤ d → y * x ∈ S :=
    fun y x h₁ h₂ h₃ h₄ => ⟨(y, x), ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩, rfl⟩
  have hmin : ∀ u v : ℝ, u ∈ S → v ∈ S → min u v ∈ S := fun u v hu hv => by
    rcases min_choice u v with h | h <;> rw [h] <;> assumption
  have hmax : ∀ u v : ℝ, u ∈ S → v ∈ S → max u v ∈ S := fun u v hu hv => by
    rcases max_choice u v with h | h <;> rw [h] <;> assumption
  have hac := mem a c le_rfl hab le_rfl hcd
  have had := mem a d le_rfl hab hcd le_rfl
  have hbc := mem b c hab le_rfl le_rfl hcd
  have hbd := mem b d hab le_rfl hcd le_rfl
  have hlo : Interval.mulLo a b c d ∈ S := hmin _ _ (hmin _ _ hac had) (hmin _ _ hbc hbd)
  have hhi : Interval.mulHi a b c d ∈ S := hmax _ _ (hmax _ _ hac had) (hmax _ _ hbc hbd)
  obtain ⟨⟨y, x⟩, ⟨⟨hy₁, hy₂⟩, ⟨hx₁, hx₂⟩⟩, hyx⟩ := hS.Icc_subset hlo hhi ⟨hz₁, hz₂⟩
  exact ⟨y, x, ⟨hy₁, hy₂⟩, ⟨hx₁, hx₂⟩, hyx⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.times_exact {I J : Interval (Vec ℝ n)} (hI : I.IsNonempty)
    (hJ : J.IsNonempty) : -- --- CONCL ---
    (I.times J).construct =
      Set.image2 (fun x y i => x i * y i) I.construct J.construct := by -- --- PROOF ---
  refine Set.Subset.antisymm (fun z hz => ?_) (Interval.times_outer I J)
  have h : ∀ i, ∃ y x, (I.inf i ≤ y ∧ y ≤ I.sup i) ∧ (J.inf i ≤ x ∧ x ≤ J.sup i) ∧
      y * x = z i :=
    fun i => Interval.aux_exists_mul_eq (hI i) (hJ i) (hz i).1 (hz i).2
  choose y x hy hx hyx using h
  exact ⟨y, fun i => hy i, x, fun i => hx i, funext hyx⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
