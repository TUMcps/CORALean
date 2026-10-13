module

public import CORALean.ContSet.Zoo.Float.Operations.Interval
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Interval.Float.Operations.IntersectionExact

@[expose] public section

/-!
# `Zoo.interval` encloses

The intersection of the members' enclosures contains the function's value at every box point: the
Taylor model through `Taylm.bounds_mem`, the intersection through `Interval.intersection_exact`.
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

theorem Zoo.interval_outer {Z : Zoo 𝕋 n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f)
    {I : Interval (Vec 𝕋 1)} (hI : Z.interval = some I) {t : Vec ℝ n}
    (ht : t ∈ Real.Taylm.box n) : (fun _ => f t : Vec ℝ 1) ∈ I.construct := by -- --- PROOF ---
  have hT : ∀ T, Z.taylm = some T → (fun _ => f t : Vec ℝ 1) ∈
      (⟨fun _ => T.bounds.1, fun _ => T.bounds.2⟩ : Interval (Vec 𝕋 1)).construct :=
    fun T hT i => Taylm.bounds_mem (h.1 T hT) ht
  unfold Zoo.interval at hI
  rcases hz : Z.taylm with _ | T <;> rcases hv : Z.ivl with _ | J <;>
    simp [hz, hv] at hI
  · exact hI ▸ h.2 J hv t ht
  · exact hI ▸ hT T hz
  · rw [← hI, Interval.intersection_exact]; exact ⟨hT T hz, h.2 J hv t ht⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
