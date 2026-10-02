import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# Level sets: the representation

CORA's `levelSet`: the points at which a vector-valued function `f` meets a comparison with
zero in every component, `{x | ∀ i, f x i ⋈ᵢ 0}` with `⋈ᵢ ∈ {≤, <, =}`. CORA stores a
symbolic equation `eq`, its variables `vars` and the operator list `compOp`, and compiles the
equation to the handle `funHan`; the denotation only needs the handle, so `f` is a plain function
`Vec ℝ n → Vec ℝ m` and `op` the operator list (CORA's single operator for all components is the
constant list). The symbolic parts (`vars`, `solved`, `der`, `solvable`) have no counterpart:
they serve CORA's derivative-based methods, not the set. `m` is a field, as the generator count
of a zonotope is, so stacking constraints stays inside one type.

No convexity, boundedness or interval extension is assumed: a level set is whatever `f`
makes it, and `f` is arbitrary. Real layer only, since a real function has no machine form.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's `compOp` entries `'<='`, `'<'` and `'=='`. -/
inductive CompOp where
  | le
  | lt
  | eq

/-- What the comparison of a value with zero says. -/
def CompOp.holds : CompOp → ℝ → Prop
  | .le, v => v ≤ 0
  | .lt, v => v < 0
  | .eq, v => v = 0

/-- `m` constraints `f x i ⋈ᵢ 0` on `n` variables. -/
structure LevelSet (n : ℕ) where
  m : ℕ
  f : Vec ℝ n → Vec ℝ m
  op : Fin m → CompOp

/-- The points meeting every constraint. -/
def LevelSet.construct (L : LevelSet n) : Set (Vec ℝ n) :=
  {x | ∀ i, (L.op i).holds (L.f x i)}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
