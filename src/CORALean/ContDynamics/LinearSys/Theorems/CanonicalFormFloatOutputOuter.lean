module

public import CORALean.ContDynamics.LinearSys.Operations.CanonicalFormFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float canonical form holds every output input

`D (uVec + u) + k + F (vVec + v)` with `u ∈ U`, `v ∈ V` is in `V_ ⊕ v_` [1]. All quantities are
the real values of stored floats; an outer statement.

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

theorem LinearSys.canonicalFormFloat_output_outer (sys : LinearSys 𝕋 n)
    (U : Zonotope (Vec 𝕋 sys.m)) (uVec : Vec 𝕋 sys.m) (W : Zonotope (Vec 𝕋 sys.r))
    (V : Zonotope (Vec 𝕋 sys.s)) (vVec : Vec 𝕋 sys.s)
    {u : Vec ℝ sys.m} (hu : u ∈ U.construct) {v : Vec ℝ sys.s}
    (hv : v ∈ V.construct) : -- --- CONCL ---
    let G := sys.canonicalFormFloat U uVec W V vVec
    toRealMat sys.D *ᵥ (toRealVec uVec + u) + toRealVec sys.k + toRealMat sys.F *ᵥ
        (toRealVec vVec + v) ∈
      G.2.2.2.1.construct + G.2.2.2.2.construct := by -- --- PROOF ---
  intro G
  -- the part that moves, `D u + F (v - centerV)`, and the offset
  refine ⟨toRealMat sys.D *ᵥ u + toRealMat sys.F *ᵥ (v - toRealVec V.c), ?_,
    toRealMat sys.D *ᵥ toRealVec uVec + toRealVec sys.k +
      toRealMat sys.F *ᵥ (toRealVec V.c + toRealVec vVec), ?_, ?_⟩
  · -- `u` is `(u - centerU) + centerU`, in `U₀ ⊕ {centerU}`, and `v - centerV` is in `V₀`
    have hu' : u ∈ (Zonotope.plus U.recenter (Zonotope.point U.c)).construct := by
      have := Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.sub_center_mem_recenter hu)
        (show toRealVec U.c ∈ (Zonotope.point U.c).construct by
          rw [Zonotope.construct_point]; exact rfl))
      rwa [sub_add_cancel] at this
    exact Zonotope.plus_outer _ _ (Set.add_mem_add
      (Zonotope.mtimes_outer sys.D _ ⟨_, hu', rfl⟩)
      (Zonotope.mtimes_outer sys.F _ ⟨_, Zonotope.sub_center_mem_recenter hv, rfl⟩))
  · -- the offset, three boxes
    exact Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
      ⟨_, Interval.mtimes_outer sys.D _ ⟨_, Interval.mem_point uVec, rfl⟩, _,
        Interval.mem_point sys.k, rfl⟩, _,
      Interval.mtimes_outer sys.F _ ⟨_, Interval.plus_outer _ _
        ⟨_, Interval.mem_point V.c, _, Interval.mem_point vVec, rfl⟩, rfl⟩, rfl⟩
  · -- the two parts add up to the point
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
