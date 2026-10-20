module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow

@[expose] public section

/-!
# Membership in the nominal shadow, in the stored fields

Every enclosure proof at this layer splits a point into a nominal part and an
error, and this is the form it reads the nominal part in: the exact layer's
variables and inequality with the stored floats put through `toReal`, and the
point read coordinatewise.

Proofs use it rather than going through `nominal` because through it every size is
`S.m` and `S.k`, where the instance gives the equal-but-distinct `(nominal S).m`
that `rw` reads apart.

## Inputs
* `S` – spectrahedral shadow
* `x` – point of length `n`

## Hypotheses
* none

## Conclusion
* `x` lies in the nominal shadow iff some `β` makes the combination positive semidefinite
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.mem_nominalSet_iff {S : SpectraShadow 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet S ↔ ∃ β : Vec ℝ S.m,
      (toRealMat S.A₀ + ∑ i, β i • toRealMat (S.A i)).PosSemidef ∧
        ∀ i, x i = toReal (S.c i) + ∑ j, toReal (S.G j i) * β j := by -- --- PROOF ---
  constructor
  · rintro ⟨β, hβ, hx⟩
    exact ⟨β, hβ, fun i => (congrFun hx i).trans
      (Entrywise.add_sum_smul_apply (toRealVec S.c) (fun j i => toReal (S.G j i)) β i)⟩
  · rintro ⟨β, hβ, hx⟩
    exact ⟨β, hβ, funext fun i => (hx i).trans
      (Entrywise.add_sum_smul_apply (toRealVec S.c) (fun j i => toReal (S.G j i)) β i).symm⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
