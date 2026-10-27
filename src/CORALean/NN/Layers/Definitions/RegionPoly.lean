module

public import CORALean.NN.Layers.Definitions.PolyRelaxation

@[expose] public section

/-!
# A polynomial valid on one region of the domain
One entry of the struct array CORA's `findRegionPolys` returns: the region `[l, u]` (an end
may be infinite), the coefficients of a polynomial, and the error `d` it is allowed. `Encloses`
is that the polynomial and error enclose `σ` on the region; `Fits` adds that the region is the
stated one and the error at most the tolerance, all measured on the coefficients stored.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- A region (`none` for an infinite end), a polynomial on it and its error. -/
structure RegionPoly (𝕋 : Type) where
  lo : Option 𝕋
  hi : Option 𝕋
  deg : ℕ
  coeffs : Fin (deg + 1) → 𝕋
  err : 𝕋

/-- That `t` lies in the region. -/
def RegionPoly.covers (r : RegionPoly 𝕋) (t : ℝ) : Prop :=
  (∀ a, r.lo = some a → toReal a ≤ t) ∧ (∀ b, r.hi = some b → t ≤ toReal b)

/-- That the stored polynomial and error enclose `σ` at every point of the region. -/
def RegionPoly.Encloses (r : RegionPoly 𝕋) (σ : ℝ → ℝ) : Prop :=
  ∀ t, r.covers t → |σ t - Real.evalPoly (fun k => toReal (r.coeffs k)) t| ≤ toReal r.err

/-- A region `[l, u]` that encloses `σ` with an error at most the tolerance `tol`. -/
def RegionPoly.Fits (σ : ℝ → ℝ) (tol l u : 𝕋) (r : RegionPoly 𝕋) : Prop :=
  r.lo = some l ∧ r.hi = some u ∧ r.Encloses σ ∧ toReal r.err ≤ toReal tol

/-- An accepted region with the end of it the search stopped at, which is where the next one
starts. -/
structure RegionPoly.Found (𝕋 : Type) where
  region : RegionPoly 𝕋
  edge : 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
