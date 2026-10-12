import CORALean.ContSet.VPolytope.Float.Operations.MatPolytope
import CORALean.ContSet.VPolytope.Real.Theorems.MatPolytopeExact

/-!
# `VPolytope.matPolytope` is exactly the image under the column embedding

Exact: no entry is rounded, so the set the float `matPolytope` stands for is the image of the
input's set under `v ↦ (v · ·)`, nominal part and error box alike.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.matPolytope_exact (P : VPolytope 𝕋 n) :
    (fun v => (fun i _ => v i : Mat ℝ n 1)) '' P.construct
      = ContSet.construct (P.matPolytope : GVPolytope (Mat 𝕋 n 1)) := by -- --- PROOF ---
  have hnom : (fun v => (fun i _ => v i : Mat ℝ n 1)) '' nominalSet P
      = nominalSet (P.matPolytope : GVPolytope (Mat 𝕋 n 1)) :=
    CORALean.Real.VPolytope.matPolytope_exact (nominal P)
  ext y
  constructor
  · rintro ⟨x, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨_, hnom ▸ ⟨a, ha, rfl⟩, fun i _ => b i, ?_, rfl⟩
    · rintro ⟨i, j⟩
      exact hb i
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a0, ha0, rfl⟩ := hnom ▸ ha
    refine ⟨a0 + fun i => b i 0, ⟨a0, ha0, _, ?_, rfl⟩, ?_⟩
    · intro i
      exact hb (i, 0)
    · funext i j
      rw [Subsingleton.elim j 0]
      rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
