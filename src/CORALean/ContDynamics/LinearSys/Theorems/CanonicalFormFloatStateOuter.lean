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
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q r s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalFormFloat_state_outer (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    (c : Vec 𝕋 n) (out : OutputEq 𝕋 n m r) (k : Vec 𝕋 r) (E : Mat 𝕋 n q) (F : Mat 𝕋 r s)
    (U : Zonotope (Vec 𝕋 m)) (uVec : Vec 𝕋 m) (W : Zonotope (Vec 𝕋 q)) (V : Zonotope (Vec 𝕋 s))
    (vVec : Vec 𝕋 s)
    {u : Vec ℝ m} (hu : u ∈ U.construct) {w : Vec ℝ q} (hw : w ∈ W.construct) :
    let G := sys.canonicalFormFloat B c out k E F U uVec W V vVec
    toRealMat B *ᵥ (toRealVec uVec + u) + toRealVec c + toRealMat E *ᵥ w ∈
      G.2.2.1.construct + G.2.2.2.1.construct := by -- --- PROOF ---
  intro G
  -- the part that moves, `B (u - centerU) + E (w - centerW)`, and the offset
  refine ⟨toRealMat B *ᵥ (u - toRealVec U.c) + toRealMat E *ᵥ (w - toRealVec W.c), ?_,
    toRealMat B *ᵥ toRealVec uVec + toRealMat B *ᵥ toRealVec U.c + toRealVec c +
      toRealMat E *ᵥ toRealVec W.c, ?_, ?_⟩
  · -- `B (u - centerU)` is in `B U₀` and `E (w - centerW)` in `E W₀`
    exact Zonotope.plus_outer _ _ (Set.add_mem_add
      (Zonotope.mtimes_outer B _ ⟨_, Zonotope.sub_centre_mem_recentre hu, rfl⟩)
      (Zonotope.mtimes_outer E _ ⟨_, Zonotope.sub_centre_mem_recentre hw, rfl⟩))
  · -- the offset, four boxes
    exact Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
      ⟨_, Interval.mtimes_outer B _ ⟨_, Interval.mem_point uVec, rfl⟩, _,
        Interval.mtimes_outer B _ ⟨_, Interval.mem_point U.c, rfl⟩, rfl⟩,
      _, Interval.mem_point c, rfl⟩, _,
      Interval.mtimes_outer E _ ⟨_, Interval.mem_point W.c, rfl⟩, rfl⟩
  · -- the two parts add up to the point
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
