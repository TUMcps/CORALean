import CORALean.ContSet.Zoo.Float.Operations.Rdivide
import CORALean.ContSet.Taylm.Float.Theorems.RdivideOuter
import CORALean.ContSet.Interval.Float.Theorems.RdivideOuter

/-!
# `Zoo.rdivide` encloses

As `plus`, under the members' own denominator certificates: the Taylor model's margin `hm`
(`Taylm.rdivide_outer`) and the interval's strict sign test `hJ` (`Interval.rdivide_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.rdivide_outer {Z₁ Z₂ : Zoo 𝕋 n} {f g : Vec ℝ n → ℝ} (h₁ : Z₁.Encloses f)
    (h₂ : Z₂.Encloses g)
    (hm : ∀ T, Z₂.taylm = some T → 0 < toReal (maximum (minimum T.constCoef T.bounds.1)
      (neg (maximum T.constCoef T.bounds.2))))
    (hJ : ∀ J, Z₂.ivl = some J →
      ∀ i, ltStrict zero (J.inf i) = true ∨ ltStrict (J.sup i) zero = true) :
    (Z₁.rdivide Z₂).Encloses fun t => f t / g t := by -- --- PROOF ---
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hT
    exact Taylm.rdivide_outer (h₁.1 a ha) (h₂.1 b hb) (hm b hb)
  · obtain ⟨a, b, ha, hb, rfl⟩ := Option.map₂_eq_some_iff.1 hI
    exact Interval.rdivide_outer _ _ (hJ b hb) ⟨_, h₁.2 a ha t ht, _, h₂.2 b hb t ht, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
