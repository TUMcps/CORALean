import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# Matrix zonotopes over a floating-point scalar: the representation

CORA's `matZonotope` [1, Eq. (8)] in `𝕋`: a centre matrix, a family of generator matrices,
and an interval-matrix error box holding what rounding has cost. `nominal` is the exact
layer's `Zonotope (Mat ℝ m n)` the stored floats describe, so each operation's guarantee
goes through the real one.

A type of its own rather than `Float.Zonotope` re-indexed by its ambient type, as `Interval`
was. `Float.Zonotope 𝕋 n` stores its generators as one matrix `Mat 𝕋 n h`, reads them by
coordinate (`radius`, `reduce`, `mtimes`), and is an `InflatedContSet`, a class fixed at
`Vec ℝ n` with a `Vec`-valued error box; some three hundred files use it. Re-indexing it
would move all of them for one new instance at `Mat`, whereas the matrix operations share
no code with the vector ones beyond `Interval`. So the duplication is a structure and a
`construct`, and `MatZonotope` denotes `nominal + E` exactly as `InflatedContSet.construct`
does, at `Mat ℝ m n`.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure MatZonotope (𝕋 : Type) (m n : ℕ) where
  h : ℕ
  c : Mat 𝕋 m n
  G : Fin h → Mat 𝕋 m n
  E : Interval (Mat 𝕋 m n)

/-- The exact matrix zonotope the stored floats describe. -/
def MatZonotope.nominal [SoundFloatArithmetic 𝕋] (Z : MatZonotope 𝕋 m n) :
    CORALean.Real.Zonotope (Mat ℝ m n) :=
  ⟨Z.h, toRealMat Z.c, fun j => toRealMat (Z.G j)⟩

def MatZonotope.construct [SoundFloatArithmetic 𝕋] (Z : MatZonotope 𝕋 m n) : Set (Mat ℝ m n) :=
  Z.nominal.construct + Z.E.construct

/-! ## Storage

Every field is a function type, so a product of products is a closure over its whole
history; `materialise` stores the centre, every generator and the box, and is the identity
(`materialise_eq`). `matPow` and the Taylor sum apply it at each step. -/

def MatZonotope.materialise (Z : MatZonotope 𝕋 m n) : MatZonotope 𝕋 m n :=
  let c : Vector (Vector 𝕋 n) m := Vector.ofFn fun i => Vector.ofFn (Z.c i)
  let G : Vector (Vector (Vector 𝕋 n) m) Z.h :=
    Vector.ofFn fun k => Vector.ofFn fun i => Vector.ofFn (Z.G k i)
  { h := Z.h
    c := fun i j => (c[i.val]'i.isLt)[j.val]'j.isLt
    G := fun k i j => ((G[k.val]'k.isLt)[i.val]'i.isLt)[j.val]'j.isLt
    E := Z.E.materialiseMat }

omit [FloatOps 𝕋] in
@[simp] theorem MatZonotope.materialise_eq (Z : MatZonotope 𝕋 m n) : Z.materialise = Z := by
  simp [MatZonotope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
