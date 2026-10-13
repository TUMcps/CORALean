import CORALean.ContSet.HPolytope.Float.Operations.Not
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.not` lies inside the complement

For a positive `ε` the polytope `-a x ≤ -b - ε` is a subset of the complement of `a x ≤ b`: an
inner approximation, not the complement (which is open).
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

theorem HPolytope.not_inner {P Q : HPolytope 𝕋 (Vec 𝕋 n)} {ε : 𝕋} (hε : 0 < toReal ε)
    (h : P.not ε = some Q) : Q.construct ⊆ P.construct ᶜ := by -- --- PROOF ---
  obtain ⟨m, A, b, me, Ae, be⟩ := P
  unfold HPolytope.not at h
  split at h
  · rename_i hm
    simp only at hm
    obtain ⟨rfl, rfl⟩ := hm
    cases h
    -- a point in both would satisfy `-a x ≤ -b - ε` and `a x ≤ b`
    intro x hx hxP
    have h1 := (HPolytope.mem_construct_iff.mp hx).1 0
    have h2 := (HPolytope.mem_construct_iff.mp hxP).1 0
    simp only [Fin.cast_eq_self] at h1
    have hd := subDown_le_sub (neg (b 0)) ε
    simp only [toReal_neg] at hd
    -- the negated row sums to the negated sum
    have hsum : ∀ (f : Fin n → 𝕋), ∑ j, toReal (neg (f j)) * x j = -∑ j, toReal (f j) * x j := by
      intro f
      simp [toReal_neg, neg_mul, Finset.sum_neg_distrib]
    simp only [Matrix.mulVec, dotProduct, toRealMat] at h1 h2
    rw [hsum] at h1
    linarith
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
