import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.translate`, over a floating-point scalar

The first operation at this layer that actually rounds, and the one that shows
why the equality right-hand side is an interval.

Shifting moves each bound by what its own row reads off the shift, which is a
dot product and so inexact. An inequality absorbs that by rounding its bound up:
the halfspace only grows. An equality has no single direction to grow in, so
both ends of its interval move outward — down at `inf`, up at `sup` — and the
row stays satisfiable. A point right-hand side could not have done this, and no
ambient error box would have rescued it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def HPolytope.translate (t : Vec 𝕋 n) (P : HPolytope 𝕋 n) : HPolytope 𝕋 n where
  m := P.m
  A := P.A
  b := fun i => addUp (P.b i) (dotUp (P.A i) t)
  me := P.me
  Ae := P.Ae
  be := ⟨fun i => addDown (P.be.inf i) (dotDown (P.Ae i) t),
         fun i => addUp (P.be.sup i) (dotUp (P.Ae i) t)⟩

variable [SoundFloatArithmetic 𝕋]

theorem HPolytope.translate_outer (t : Vec 𝕋 n) (P : HPolytope 𝕋 n) :
    (toRealVec t + ·) '' P.construct ⊆ (HPolytope.translate t P).construct := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hy
  -- a row reads the shifted point as what it read of each part
  have hsplit : ∀ {m : ℕ} (M : Mat 𝕋 m n) (i : Fin m),
      (toRealMat M *ᵥ (toRealVec t + y)) i
        = (∑ j, toReal (M i j) * toReal (t j)) + (toRealMat M *ᵥ y) i := by
    intro m M i
    rw [Matrix.mulVec_add]
    rfl
  -- each bound shifts by what its own row reads of `t`, rounded outward
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · show (toRealMat P.A *ᵥ (toRealVec t + y)) i ≤ toReal (addUp (P.b i) (dotUp (P.A i) t))
    rw [hsplit P.A i]
    have h := add_le_addUp (P.b i) (dotUp (P.A i) t)
    have h' := le_dotUp (P.A i) t
    linarith [hle i]
  · show toReal (addDown (P.be.inf i) (dotDown (P.Ae i) t))
      ≤ (toRealMat P.Ae *ᵥ (toRealVec t + y)) i
    rw [hsplit P.Ae i]
    have h := addDown_le_add (P.be.inf i) (dotDown (P.Ae i) t)
    have h' := dotDown_le (P.Ae i) t
    linarith [(heq i).1]
  · show (toRealMat P.Ae *ᵥ (toRealVec t + y)) i
      ≤ toReal (addUp (P.be.sup i) (dotUp (P.Ae i) t))
    rw [hsplit P.Ae i]
    have h := add_le_addUp (P.be.sup i) (dotUp (P.Ae i) t)
    have h' := le_dotUp (P.Ae i) t
    linarith [(heq i).2]

end CORALean.Float
