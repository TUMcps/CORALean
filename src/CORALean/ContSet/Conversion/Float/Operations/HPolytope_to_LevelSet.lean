module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# A float polytope as a level set — the construction

`HPolytope.levelSet` is the construction; `HPolytope_to_LevelSet` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `levelSet(P)`: `A x - b ≤ 0`, then `Ae x - be.sup ≤ 0` and `be.inf - Ae x ≤ 0`. -/
def HPolytope.levelSet (P : HPolytope 𝕋 (Vec 𝕋 n)) : Real.LevelSet n where
  m := P.m + (P.me + P.me)
  f x := Fin.append (fun i => (toRealMat P.A *ᵥ x) i - toReal (P.b i))
    (Fin.append (fun r => (toRealMat P.Ae *ᵥ x) r - toReal (P.be.sup r))
      fun r => toReal (P.be.inf r) - (toRealMat P.Ae *ᵥ x) r)
  op := Fin.append (fun _ => .le) (Fin.append (fun _ => .le) fun _ => .le)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
