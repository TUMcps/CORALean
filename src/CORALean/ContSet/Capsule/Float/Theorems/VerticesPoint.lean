import CORALean.ContSet.Capsule.Float.Operations.Vertices
import CORALean.ContSet.Capsule.Float.Theorems.RepresentsaPointSound
import CORALean.ContSet.Capsule.Real.Theorems.VerticesMemFrontier

/-!
# `Capsule.vertices` of a point capsule

Where the float test certifies a point capsule, the list is the one box `[c, c]`, and its point
`c` is the exact layer's single vertex, on the frontier of the capsule.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.vertices_point (p k : ℕ) {C : Capsule 𝕋 2} (h : C.representsa_point = true) :
    C.vertices p k = [Interval.point C.c] ∧
      ∃ x ∈ (Interval.point C.c).construct, x ∈ frontier C.construct := by -- --- PROOF ---
  refine ⟨by simp [Capsule.vertices, h], ?_⟩
  -- the nominal capsule is a point
  have hn : Real.Capsule.representsa_point C.nominal :=
    (Real.Capsule.representsa_point_iff (by norm_num) C.nominal).mp
      (Capsule.representsa_point_sound (by norm_num) h)
  refine ⟨toRealVec C.c, fun _ => ⟨le_rfl, le_rfl⟩, ?_⟩
  have hr : 0 ≤ C.nominal.r := le_of_eq (Eq.symm hn.2)
  refine Real.Capsule.vertices_mem_frontier C.nominal hr _ ?_
  simp [Real.Capsule.vertices, hn]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
