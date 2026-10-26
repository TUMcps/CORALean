module

public import CORALean.ContSet.HPolytope.Float.Operations.Not
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.not` lies inside the complement

For a positive `ε` the polytope `-a x ≤ -b - ε` is a subset of the complement of `a x ≤ b`: an
inner approximation, not the complement (which is open).

## Inputs
* `P` – H-polytope
* `ε` – scalar

## Hypotheses
* `hε` – `0 < toReal ε`

## Conclusion
* `HPolytope.not` lies inside the complement
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.not_inner {P : HPolytope 𝕋 (Vec 𝕋 n)} {ε : 𝕋}
    (hε : 0 < toReal ε) : -- --- CONCL ---
    ∀ Q ∈ P.not ε,
      Q.construct ⊆ P.construct ᶜ := by -- --- PROOF ---
  intro Q (h : P.not ε = some Q)
  unfold HPolytope.not at h
  dsimp only at h
  split at h
  · rename_i hm
    cases h
    -- a point in both would satisfy `-a x ≤ -bU - ε` and `a x ≤ bU`
    intro x hx hxP
    have hxQ := HPolytope.absorbRounding_outer P hxP
    have hE : (P.absorbRounding).IsErrFree := HPolytope.isErrFree_of_origin rfl rfl rfl
    have h1 := ((HPolytope.mem_construct_iff (HPolytope.isErrFree_of_origin rfl rfl rfl)).mp hx).1 0
    have h2 := ((HPolytope.mem_construct_iff hE).mp hxQ).1 (Fin.cast hm.1.symm 0)
    have hd := subDown_le_sub (neg (P.absorbRounding.b (Fin.cast hm.1.symm 0))) ε
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
