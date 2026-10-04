import CORALean.ContDynamics.LinearSys.Operations.IsCanonicalFormFloat
import CORALean.ContDynamics.LinearSys.Theorems.EntryIsFloatSound

/-!
# A `true` from the float `isCanonicalForm` is a proof

One-sided: when `isCanonicalFormFloat` answers `true`, the real coefficients the floats denote are
in canonical form [1]. `false` says nothing, since `le` is only sound when it answers `true`.

## References

* [1] `contDynamics/@linearSys/isCanonicalForm.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q r s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One-sided: `true` gives the real system in canonical form. -/
theorem LinearSys.isCanonicalFormFloat_sound {B : Mat 𝕋 n m} {c : Vec 𝕋 n} {D : Mat 𝕋 r m}
    {k : Vec 𝕋 r} {E : Mat 𝕋 n q} {F : Mat 𝕋 r s}
    (h : LinearSys.isCanonicalFormFloat B c D k E F = true) :
    LinearSys.IsCanonicalForm (toRealMat B) (toRealVec c) (toRealMat D) (toRealVec k)
      (toRealMat E) (toRealMat F) := by -- --- PROOF ---
  unfold LinearSys.isCanonicalFormFloat at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨⟨⟨⟨⟨hm, hs⟩, hc⟩, hk⟩, hE⟩, hD⟩, hB⟩ := h
  refine ⟨hm, hs, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simpa [toRealVec, toReal_zero] using LinearSys.entryIsFloat_sound (hc i)
  · funext i
    simpa [toRealVec, toReal_zero] using LinearSys.entryIsFloat_sound (hk i)
  · funext i j
    simpa [toRealMat, toReal_zero] using LinearSys.entryIsFloat_sound (hE i j)
  · funext i j
    simpa [toRealMat, toReal_zero] using LinearSys.entryIsFloat_sound (hD i j)
  · intro i j
    have := LinearSys.entryIsFloat_sound (hB i j)
    by_cases hij : (i : ℕ) = (j : ℕ)
    · simpa [toRealMat, hij, toReal_one] using this
    · simpa [toRealMat, hij, toReal_zero] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
