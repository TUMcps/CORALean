module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_LevelSet

@[expose] public section

/-!
# A float polytope as a level set

CORA's `levelSet(polytope)` on the stored floats: the affine function `A x - b`, every
component `<= 0`. A float equality row carries an interval right-hand side, so it becomes two
components, `Ae x - be.sup <= 0` and `be.inf - Ae x <= 0`, where the exact layer has one `=`.
The level set holds its constraint function as data and nothing is rounded: the stored numbers
are read as reals, and the conversion denotes exactly the float polytope's set.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.levelSet_exact (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    P.levelSet.construct = P.nominal.construct := by -- --- PROOF ---
  ext x
  show (∀ i, Real.CompOp.holds (Fin.append (fun _ => .le) (Fin.append (fun _ => .le)
    fun _ => .le) i) (Fin.append (fun i => (toRealMat P.A *ᵥ x) i - toReal (P.b i)
      - |toReal (P.b_error i)|)
      (Fin.append (fun r => (toRealMat P.Ae *ᵥ x) r - toReal (P.be r) - |toReal (P.be_error r)|)
        fun r => toReal (P.be r) - (toRealMat P.Ae *ᵥ x) r - |toReal (P.be_error r)|) i)) ↔ _
  -- the three blocks of components, each its own family of rows
  rw [Real.LevelSet.forall_append_holds, Real.LevelSet.forall_append_holds,
    HPolytope.mem_nominal_iff]
  simp only [Real.CompOp.holds, sub_nonpos, abs_le]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i => by linarith [h1 i], fun r => ⟨by linarith [h3 r], by linarith [h2 r]⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by linarith [h1 i], fun r => by linarith [(h2 r).2],
      fun r => by linarith [(h2 r).1]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
