import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSum
import CORALean.ContSet.Ellipsoid.Float.Instances

/-!
# A precision parameter, named by the caller

`Ellipsoid.plus` carries a free parameter, so there is no `Plus` for instance
search to find. What there is instead is `plusInstance`, a `def` the caller
applies to its own choice, and this file is the evidence that that is enough: an
algorithm written against `Plus` runs at an ellipsoid with no line of it
changed, and the operation it ends up calling is the parameterized one at the
value the caller passed.

`LinearSys.inputTaylorSum` is the algorithm here because `Plus` and
`Mtimes (Mat ℝ)` are exactly what it asks for and exactly what an ellipsoid has.
The reachability loops still do not run at one, and not for this reason:
`Reduce`, `LinComb`, `OfInterval` and `Mtimes ℐ` are missing *operations*, not
missing room for a parameter, and `ContSet.lean`'s docstring is where the two
are kept apart.

The float layer's parameter is the two scalings with the inequality they owe,
which is a wider family than `l`'s. No generic algorithm runs there yet — its
`Mtimes` is over `Mat 𝕋`, not `Mat ℝ` — so what is recorded is that the instance
is lawful and that `⊞` reads at a float ellipsoid.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet

/-- The input Taylor sum at an ellipsoid, the scaling fixed once for the whole
sum. `inputTaylorSum` is unchanged and unaware; the `letI` is the entire cost of
running it here. -/
noncomputable def ellipsoidInputTaylorSum {n : ℕ} {l : ℝ} (hl : 0 < l)
    (sys : LinearSys ℝ n) (r : ℝ) (U : Ellipsoid n) : ℕ → Ellipsoid n :=
  letI := Ellipsoid.plusInstance hl
  sys.inputTaylorSum r U

/-- What the generic recursion unfolds to: the caller's `l`, in the operation
the representation actually implements. -/
example {n : ℕ} {l : ℝ} (hl : 0 < l) (sys : LinearSys ℝ n) (r : ℝ) (U : Ellipsoid n)
    (i : ℕ) :
    ellipsoidInputTaylorSum hl sys r U (i + 1)
      = Ellipsoid.plus l (ellipsoidInputTaylorSum hl sys r U i)
          (Mtimes.mtimes (sys.inputTerm r (i + 1)) U) :=
  rfl

/-- The instance is lawful, and its law is the operation's own theorem. -/
example {n : ℕ} {l : ℝ} (hl : 0 < l) (E₁ E₂ : Ellipsoid n) :
    construct E₁ + construct E₂ ⊆ construct (Ellipsoid.plus l E₁ E₂) := by
  letI := Ellipsoid.plusInstance hl
  exact Plus.plus_outer E₁ E₂

end CORALean.Real

namespace CORALean.Float

open Pointwise ContSet SoundFloatArithmetic

/-- The same at the float layer, where the parameter is the two scalings and the
certificate they carry. Stated through `⊞`, so what is checked is that the
notation reads here at all. -/
example {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {s₁ s₂ : 𝕋}
    (hne₁ : toReal s₁ ≠ 0) (hne₂ : toReal s₂ ≠ 0)
    (hs : 1 / toReal s₁ ^ 2 + 1 / toReal s₂ ^ 2 ≤ 1) (E₁ E₂ : Ellipsoid 𝕋 n) :
    letI := Ellipsoid.plusInstance hne₁ hne₂ hs
    construct E₁ + construct E₂ ⊆ construct (E₁ ⊞ E₂) := by
  letI := Ellipsoid.plusInstance hne₁ hne₂ hs
  exact Plus.plus_outer E₁ E₂

end CORALean.Float
