module

public import CORALean.ContSet.Zoo.Real.Operations.Rdivide
public import CORALean.ContSet.Zoo.Real.Theorems.EnclosesIff
public import CORALean.ContSet.Taylm.Real.Theorems.RdivideOuter
public import CORALean.ContSet.Interval.Real.Theorems.RdivideExact

@[expose] public section

/-!
# `Zoo.rdivide` encloses the quotient

Under the members' own conditions on the denominator: the Taylor model's sign condition of
`Taylm.rdivide_outer`, and for the interval, that no denominator entry contains zero
(`Interval.rdivide_exact`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.rdivide_outer {Z₁ Z₂ : Zoo n} {f g : Vec ℝ n → ℝ} (h₁ : Z₁.Encloses f)
    (h₂ : Z₂.Encloses g)
    (hT : ∀ T, Z₂.taylm = some T →
      0 < min T.constCoef T.bounds.inf ∨ max T.constCoef T.bounds.sup < 0)
    (hI : ∀ I, Z₂.ivl = some I → ∀ i, 0 < I.inf i ∨ I.sup i < 0) : -- --- CONCL ---
    (Z₁.rdivide Z₂).Encloses fun t => f t / g t := by -- --- PROOF ---
  rw [Zoo.encloses_iff] at h₁ h₂ ⊢
  refine ⟨fun T hT' => ?_, fun I hI' t ht => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hT'
    exact Taylm.rdivide_outer (h₁.1 a ha) (h₂.1 b hb) (hT b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hI'
    have m₁ := h₁.2 a ha t ht
    have m₂ := h₂.2 b hb t ht
    rw [Interval.rdivide_exact (fun i => (m₁ i).1.trans (m₁ i).2)
      (fun i => (m₂ i).1.trans (m₂ i).2) (hI b hb)]
    exact ⟨_, m₁, _, m₂, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
