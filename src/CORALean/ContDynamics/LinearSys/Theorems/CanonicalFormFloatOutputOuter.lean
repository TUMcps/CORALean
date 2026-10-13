import CORALean.ContDynamics.LinearSys.Operations.CanonicalFormFloat
import CORALean.ContSet.Zonotope.Float.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float canonical form holds every output input

`D (uVec + u) + k + F (vVec + v)` with `u ∈ U`, `v ∈ V` is in `V_ ⊕ v_` [1]. All quantities are
the real values of stored floats; an outer statement.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q r s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.canonicalFormFloat_output_outer (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    (c : Vec 𝕋 n) (out : OutputEq 𝕋 n m r) (k : Vec 𝕋 r) (E : Mat 𝕋 n q) (F : Mat 𝕋 r s)
    (U : Zonotope (Vec 𝕋 m)) (uVec : Vec 𝕋 m) (W : Zonotope (Vec 𝕋 q)) (V : Zonotope (Vec 𝕋 s))
    (vVec : Vec 𝕋 s)
    {u : Vec ℝ m} (hu : u ∈ U.construct) {v : Vec ℝ s} (hv : v ∈ V.construct) :
    let G := sys.canonicalFormFloat B c out k E F U uVec W V vVec
    toRealMat out.D *ᵥ (toRealVec uVec + u) + toRealVec k + toRealMat F *ᵥ (toRealVec vVec + v) ∈
      G.2.2.2.2.1.construct + G.2.2.2.2.2.construct := by -- --- PROOF ---
  intro G
  -- the part that moves, `D u + F (v - centerV)`, and the offset
  refine ⟨toRealMat out.D *ᵥ u + toRealMat F *ᵥ (v - toRealVec V.c), ?_,
    toRealMat out.D *ᵥ toRealVec uVec + toRealVec k +
      toRealMat F *ᵥ (toRealVec V.c + toRealVec vVec), ?_, ?_⟩
  · -- `u` is `(u - centerU) + centerU`, in `U₀ ⊕ {centerU}`, and `v - centerV` is in `V₀`
    have hu' : u ∈ (Zonotope.plus U.recentre (Zonotope.point U.c)).construct := by
      have := Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.sub_centre_mem_recentre hu)
        (show toRealVec U.c ∈ (Zonotope.point U.c).construct by
          rw [Zonotope.construct_point]; exact rfl))
      rwa [sub_add_cancel] at this
    exact Zonotope.plus_outer _ _ (Set.add_mem_add
      (Zonotope.mtimes_outer out.D _ ⟨_, hu', rfl⟩)
      (Zonotope.mtimes_outer F _ ⟨_, Zonotope.sub_centre_mem_recentre hv, rfl⟩))
  · -- the offset, three boxes
    exact Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
      ⟨_, Interval.mtimes_outer out.D _ ⟨_, Interval.mem_point uVec, rfl⟩, _,
        Interval.mem_point k, rfl⟩, _,
      Interval.mtimes_outer F _ ⟨_, Interval.plus_outer _ _
        ⟨_, Interval.mem_point V.c, _, Interval.mem_point vVec, rfl⟩, rfl⟩, rfl⟩
  · -- the two parts add up to the point
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
