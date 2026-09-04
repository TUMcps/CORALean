import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.VPolytope.Float.Operations.LinComb

/-!
# `VPolytope.linComb` encloses every segment between the two

Nothing rounds, so there is no spill and `InflatedContSet`'s composition lemma is
not needed: the nominal halves land in the exact `linComb` and the error halves
in the interval one, each by its own layer's theorem.

The one obligation is that reading a concatenated vertex list as reals is the
same as concatenating the two read lists — `toReal` and `Fin.append` commute,
which `Fin.addCases` shows and nothing else needs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

theorem VPolytope.nominal_linComb (P₁ P₂ : VPolytope 𝕋 n) :
    nominal (P₁.linComb P₂) = (nominal P₁).linComb (nominal P₂) := by
  have hV : (fun (l : Fin (P₁.k + P₂.k)) i => toReal ((P₁.linComb P₂).V i l))
      = Fin.append (fun l i => toReal (P₁.V i l)) (fun l i => toReal (P₂.V i l)) := by
    funext l
    refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l <;> funext i <;>
      simp only [VPolytope.linComb, Fin.append_left, Fin.append_right]
  exact congrArg (Real.VPolytope.mk (P₁.k + P₂.k)) hV

-- the segment splits into a nominal segment and a segment of the two error boxes
theorem VPolytope.linComb_outer (P₁ P₂ : VPolytope 𝕋 n) :
    segments P₁.construct P₂.construct ⊆ (P₁.linComb P₂).construct := by
  rintro _ ⟨_, ⟨v₁, hv₁, e₁, he₁, rfl⟩, _, ⟨v₂, hv₂, e₂, he₂, rfl⟩, lam, hlam, rfl⟩
  refine ⟨lam • v₁ + (1 - lam) • v₂, ?_, lam • e₁ + (1 - lam) • e₂, ?_, ?_⟩
  · have h := Real.VPolytope.linComb_outer (nominal P₁) (nominal P₂)
      ⟨v₁, hv₁, v₂, hv₂, lam, hlam, rfl⟩
    rw [← VPolytope.nominal_linComb] at h
    exact h
  · exact Interval.linComb_outer _ _ ⟨e₁, he₁, e₂, he₂, lam, hlam, rfl⟩
  · show lam • v₁ + (1 - lam) • v₂ + (lam • e₁ + (1 - lam) • e₂)
        = lam • (v₁ + e₁) + (1 - lam) • (v₂ + e₂)
    rw [smul_add, smul_add]
    abel

end CORALean.Float
