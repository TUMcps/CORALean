module

public import CORALean.ContSet.Zonotope.Float.Operations.Underapproximate
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsPointSound

@[expose] public section

/-!
# `Zonotope.underapproximate` returns points of the zonotope

A returned point passed `Zonotope.containsPoint`, so it is a member (`containsPoint_sound`), or its
sums rounded down and up agree, so it is the real point `c + Σⱼ σⱼ gⱼ` of the coefficients
`σⱼ ∈ {-1, 0, 1}` the signs give, a member where the error box holds `0`. Inner only: no claim that
it is the vertex `c ± Σⱼ sign(sᵀ gⱼ) gⱼ` of the real definition.

## Inputs
* `Z` – zonotope
* `H` – candidate right inverse
* `s` – direction
* `b` – plus or minus vertex

## Hypotheses
* none

## Conclusion
* every returned point lies in the zonotope
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   03-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The signs are coefficients in `[-1, 1]`. -/
private theorem aux_abs_sign_le (Z : Zonotope (Vec 𝕋 n)) (s : Vec 𝕋 n) (b : Bool) (j : Fin Z.h) :
    |toReal (Z.step_underapproximateSign s b j)| ≤ 1 := by
  unfold Zonotope.step_underapproximateSign
  dsimp only
  split_ifs <;> simp [toReal_zero, toReal_neg, toReal_one]

/-- A candidate whose sums are exact is the real point of its coefficients, a member. -/
private theorem aux_exact_mem {Z : Zonotope (Vec 𝕋 n)} {s : Vec 𝕋 n} {b : Bool}
    (h : Z.step_underapproximateExact s b = true) : -- --- CONCL ---
    toRealVec (Z.step_underapproximateCandidate s b) ∈ Z.construct := by -- --- PROOF ---
  simp only [Zonotope.step_underapproximateExact, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  -- the real point of the sign coefficients is the candidate, the sums being squeezed exact
  have hnom : toRealVec (Z.step_underapproximateCandidate s b) ∈ nominalSet Z := by
    refine Zonotope.mem_nominalSet_iff.mpr
      ⟨fun j => toReal (Z.step_underapproximateSign s b j), aux_abs_sign_le Z s b, fun i => ?_⟩
    obtain ⟨⟨hc, -⟩, -⟩ := h i
    have hle := toReal_le_of_le hc
    simp only [Zonotope.step_underapproximateCandidate, Zonotope.step_underapproximateLower] at hle
    -- each rounding bounds the real value in the direction of the squeeze
    have h1 := add_le_addUp (Z.c i) (sumUp fun j => mulUp (Z.step_underapproximateSign s b j)
      (Z.G j i))
    have h2 := addDown_le_add (Z.c i) (sumDown fun j => mulDown (Z.step_underapproximateSign s b j)
      (Z.G j i))
    have h3 := sum_le_sumUp fun j => mulUp (Z.step_underapproximateSign s b j) (Z.G j i)
    have h4 := sumDown_le_sum fun j => mulDown (Z.step_underapproximateSign s b j) (Z.G j i)
    have h5 : ∑ j, toReal (mulUp (Z.step_underapproximateSign s b j) (Z.G j i))
        ≥ ∑ j, toReal (Z.G j i) * toReal (Z.step_underapproximateSign s b j) :=
      Finset.sum_le_sum fun j _ => by
        rw [mul_comm]; exact mul_le_mulUp _ _
    have h6 : ∑ j, toReal (mulDown (Z.step_underapproximateSign s b j) (Z.G j i))
        ≤ ∑ j, toReal (Z.G j i) * toReal (Z.step_underapproximateSign s b j) :=
      Finset.sum_le_sum fun j _ => by
        rw [mul_comm]; exact mulDown_le_mul _ _
    simp only [toRealVec]
    simp only [Zonotope.step_underapproximateCandidate] at hle ⊢
    linarith
  -- the error box holds `0`, so the point is the nominal one plus `0`
  have h0 : ∀ i, toReal (Z.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (Z.I_error.sup i) := fun i => by
    obtain ⟨⟨-, h1⟩, h2⟩ := h i
    have a := toReal_le_of_le h1
    have c := toReal_le_of_le h2
    rw [toReal_zero] at a c
    exact ⟨a, c⟩
  exact ⟨_, hnom, 0, h0, add_zero _⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.underapproximate_inner {Z : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z.h n} {s : Vec 𝕋 n}
    {b : Bool} : -- --- CONCL ---
    ∀ p ∈ Z.underapproximate H s b,
      toRealVec p ∈ Z.construct := by -- --- PROOF ---
  intro p (h : Z.underapproximate H s b = some p)
  unfold Zonotope.underapproximate at h
  dsimp only at h
  split_ifs at h with hc hv
  · cases h; exact Zonotope.containsPoint_sound hc
  · cases h; exact aux_exact_mem hv

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
