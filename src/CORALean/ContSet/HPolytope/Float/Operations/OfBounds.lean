import CORALean.ContSet.HPolytope.Float.Operations.OfMat
import CORALean.Global.LinProg.Float.API

/-!
# `HPolytope.ofBounds`, over a floating-point scalar

The same shape as the exact layer's: rows the caller names, right-hand sides
that certificates supply. What changes is that a right-hand side is now a float,
which is why the certificates are `FloatBound`s — the rounding has already been
paid where each bound was combined, and nothing rounds here.

No equality rows, so `be` stays empty and the layer's interval right-hand side
never comes into it. An enclosure has no equalities to state: it is slack by
construction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ} {S : Set (Vec ℝ n)}

/-- Row `i` of a float matrix, as the functional over ℝ that it denotes. Every
bound below is stated against one of these. -/
abbrev rowLin (M : Mat 𝕋 q n) (i : Fin q) : Vec ℝ n →ₗ[ℝ] ℝ :=
  Real.HPolytope.rowLin (toRealMat M) i

def HPolytope.ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S (rowLin Aq i)) :
    HPolytope 𝕋 n :=
  HPolytope.ineqs Aq fun i => (u i).val

theorem HPolytope.subset_ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S (rowLin Aq i)) :
    S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun x hx => HPolytope.mem_ineqs_iff.mpr fun i => (u i).le x hx

end CORALean.Float
