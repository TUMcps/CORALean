module

public import CORALean.ContSet.Zonotope.Float.Operations.ContainsMat
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsPointSound
public import CORALean.ContSet.Zonotope.Float.Theorems.VecExact

@[expose] public section

/-!
# `Zonotope.containsMat` is sound

Each stacked matrix is certified in the stacked zonotope (`containsPoint_sound`), which denotes
exactly the stackings of the members (`vec_exact`); stacking is injective, so the matrix itself is
a member.

## Inputs
* `Z` – matrix zonotope
* `H` – candidate right inverse of the stacked generators
* `S` – matrices

## Hypotheses
* `h` – `containsMat` answered `true`

## Conclusion
* every matrix of `S`, read as reals, is a member of `Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.containsMat_sound {Z : Zonotope (Mat 𝕋 m n)} {H : Mat 𝕋 Z.h (n * m)}
    {S : Fin p → Mat 𝕋 m n} (h : Z.containsMat H S = true) : -- --- CONCL ---
    ∀ k, toRealMat (S k) ∈ Z.toSet := by -- --- PROOF ---
  intro k
  simp only [Zonotope.containsMat, List.all_eq_true, List.mem_finRange, forall_const] at h
  -- the stacked matrix is in the stacked zonotope, the stackings of the members
  have hk := Zonotope.containsPoint_sound (h k)
  rw [Zonotope.vec_exact] at hk
  obtain ⟨M, hM, hMk⟩ := hk
  -- and the stacking is injective
  have e : matVecEquiv (toRealMat (S k)) = matVecEquiv M := by
    rw [hMk]
    rfl
  rwa [matVecEquiv.injective e]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
