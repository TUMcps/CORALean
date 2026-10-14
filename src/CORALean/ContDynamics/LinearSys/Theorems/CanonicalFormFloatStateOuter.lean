module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFormFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.RecentreSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float canonical form holds every state input

`B (uVec + u) + c + E w` with `u ∈ U`, `w ∈ W` is in `U_ ⊕ u_` [1]: the centred zonotopes carry
what moves, the box `u_` the rest. All quantities are the real values of stored floats; an outer
statement.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalFormFloat_state_outer (sys : LinearSys 𝕋 n)
    (U : Zonotope (Vec 𝕋 sys.m)) (uVec : Vec 𝕋 sys.m) (W : Zonotope (Vec 𝕋 sys.r))
    (V : Zonotope (Vec 𝕋 sys.s)) (vVec : Vec 𝕋 sys.s)
    {u : Vec ℝ sys.m} (hu : u ∈ U.construct) {w : Vec ℝ sys.r} (hw : w ∈ W.construct) :
    let G := sys.canonicalFormFloat U uVec W V vVec
    toRealMat sys.B *ᵥ (toRealVec uVec + u) + toRealVec sys.c + toRealMat sys.E *ᵥ w ∈
      G.2.1.construct + G.2.2.1.construct := by -- --- PROOF ---
  intro G
  -- the part that moves, `B (u - centerU) + E (w - centerW)`, and the offset
  refine ⟨toRealMat sys.B *ᵥ (u - toRealVec U.c) + toRealMat sys.E *ᵥ (w - toRealVec W.c), ?_,
    toRealMat sys.B *ᵥ toRealVec uVec + toRealMat sys.B *ᵥ toRealVec U.c + toRealVec sys.c +
      toRealMat sys.E *ᵥ toRealVec W.c, ?_, ?_⟩
  · -- `B (u - centerU)` is in `B U₀` and `E (w - centerW)` in `E W₀`
    exact Zonotope.plus_outer _ _ (Set.add_mem_add
      (Zonotope.mtimes_outer sys.B _ ⟨_, Zonotope.sub_centre_mem_recentre hu, rfl⟩)
      (Zonotope.mtimes_outer sys.E _ ⟨_, Zonotope.sub_centre_mem_recentre hw, rfl⟩))
  · -- the offset, four boxes
    exact Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
      ⟨_, Interval.mtimes_outer sys.B _ ⟨_, Interval.mem_point uVec, rfl⟩, _,
        Interval.mtimes_outer sys.B _ ⟨_, Interval.mem_point U.c, rfl⟩, rfl⟩,
      _, Interval.mem_point sys.c, rfl⟩, _,
      Interval.mtimes_outer sys.E _ ⟨_, Interval.mem_point W.c, rfl⟩, rfl⟩
  · -- the two parts add up to the point
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
