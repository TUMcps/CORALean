module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Cos
public import CORALean.ContSet.Interval.Real.Operations.CoshHi
public import CORALean.ContSet.Interval.Real.Operations.CoshLo
public import CORALean.ContSet.Interval.Real.Operations.Mask
public import CORALean.ContSet.Interval.Real.Operations.Or
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin
public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-!
# `ContSet/Interval/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  `Interval.acos`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/acos`: the arccosine is strictly decreasing on `[-1, 1]`, so the corners swap,
so it acts on the two bounds, coordinate by coordinate. -/
noncomputable def Interval.acos (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.arccos (I.sup i)
  sup := fun i => Real.arccos (I.inf i)

end CORALean.Real


-- =====================================  `Interval.asin`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/asin`: the arcsine is strictly increasing on `[-1, 1]`, so it acts on the two
bounds, coordinate by coordinate. -/
noncomputable def Interval.asin (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.arcsin (I.inf i)
  sup := fun i => Real.arcsin (I.sup i)

end CORALean.Real


-- ====================================  `Interval.center`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- The midpoint: CORA's `center`, one half of the split an enclosure proof reads
a box's point through — a centre plus a bounded deviation `Interval.radius`
gives, related to it by `Theorems/AbsSubCenterLe`. -/
noncomputable def Interval.center (I : Interval α) : α := (2:ℝ)⁻¹ • (I.inf + I.sup)

end CORALean.Real


-- ===================================  `Interval.convHull`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/convHull_` at two intervals: it ends in `I | S`, so it is `or`. The hull of
two boxes is not their union, and the box hull is the smallest box containing it. -/
def Interval.convHull (I₁ I₂ : Interval α) : Interval α := I₁.or I₂

end CORALean.Real


-- =====================================  `Interval.cosh`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/cosh`, coordinate by coordinate: the three cases (range left of `0`, right of
`0`, or containing `0`) are `coshLo` and `coshHi`. -/
noncomputable def Interval.cosh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Interval.coshLo (I.inf i) (I.sup i)
  sup := fun i => Interval.coshHi (I.inf i) (I.sup i)

end CORALean.Real


-- =====================================  `Interval.empty`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `interval.empty(n)`, which is an `n × 0` interval. The model here has no zero-width
interval, so the empty box is a crossed one: lower bound `1`, upper bound `0`, in every
coordinate. -/
def Interval.empty (n : ℕ) : Interval (Vec ℝ n) := ⟨fun _ => 1, fun _ => 0⟩

end CORALean.Real


-- =================================  `Interval.enclosePoints`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/enclosePoints`: the smallest box containing a finite, nonempty family of
points, the coordinatewise minimum and maximum (CORA's `min(points,[],2)`, `max(points,[],2)`). -/
def Interval.enclosePoints {κ : Type} [Fintype κ] [Nonempty κ] (p : κ → α) : Interval α where
  inf := ofEntry fun i => Finset.univ.inf' Finset.univ_nonempty fun k => entry (p k) i
  sup := ofEntry fun i => Finset.univ.sup' Finset.univ_nonempty fun k => entry (p k) i

end CORALean.Real


-- ====================================  `Interval.infimum`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/infimum`: the lower bound. -/
def Interval.infimum (I : Interval α) : α := I.inf

end CORALean.Real


-- ======================================  `Interval.le`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/le`: `I ≤ J` holds when `J`'s lower bound is below `I`'s and `I`'s upper bound
is below `J`'s, in every coordinate. That is a containment test, `I ⊆ J`, not an order on the
points. -/
def Interval.le (I J : Interval α) : Prop :=
  ∀ i, entry J.inf i ≤ entry I.inf i ∧ entry I.sup i ≤ entry J.sup i

end CORALean.Real


-- ====================================  `Interval.isequal`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/isequal` at two intervals: both bounds agree, which is containment both ways
(`Interval.le` each way). CORA compares up to a tolerance (default `eps`); this is the exact test,
tolerance zero. `Theorems/IsequalIff` says what it decides: equality of the denoted sets. -/
def Interval.isequal (I J : Interval α) : Prop := I.le J ∧ J.le I

end CORALean.Real


-- ======================================  `Interval.log`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/log`: the logarithm is increasing on `(0, ∞)`, so it acts on the two bounds,
coordinate by coordinate. -/
noncomputable def Interval.log (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.log (I.inf i)
  sup := fun i => Real.log (I.sup i)

end CORALean.Real


-- ======================================  `Interval.lt`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/lt`: the strict version of `le`, both bounds of `I` strictly inside `J`'s in
every coordinate. -/
def Interval.lt (I J : Interval α) : Prop :=
  ∀ i, entry J.inf i < entry I.inf i ∧ entry I.sup i < entry J.sup i

end CORALean.Real


-- =====================================  `Interval.minus`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/minus` at two intervals: `[a, b] - [c, d] = [a - d, b - c]`. -/
def Interval.minus (I₁ I₂ : Interval α) : Interval α where
  inf := I₁.inf - I₂.sup
  sup := I₁.sup - I₂.inf

end CORALean.Real


-- ====================================  `Interval.mtimes`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- CORA's `@interval/mtimes`: each row takes the lower endpoint of every product
and the upper one, so a negative `M i k` swaps the bounds it multiplies. -/
def Interval.mtimes (M : Mat ℝ m n) (I : Interval (Vec ℝ n)) : Interval (Vec ℝ m) where
  inf := fun i => ∑ k, min (M i k * I.inf k) (M i k * I.sup k)
  sup := fun i => ∑ k, max (M i k * I.inf k) (M i k * I.sup k)

end CORALean.Real


-- =====================================  `Interval.mulHi`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- The greatest of the four.

The greatest of the four corner products of two scalar intervals. -/
def Interval.mulHi (a b c d : ℝ) : ℝ := max (max (a * c) (a * d)) (max (b * c) (b * d))

end CORALean.Real


-- =====================================  `Interval.mulLo`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

/-- The least of the four corner products of `[a, b]` and `[c, d]`.

The least of the four corner products of two scalar intervals. -/
def Interval.mulLo (a b c d : ℝ) : ℝ := min (min (a * c) (a * d)) (min (b * c) (b * d))

end CORALean.Real


-- ====================================  `Interval.origin`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

/-- CORA's `@interval/origin`: the point interval at the origin of `ℝⁿ`. -/
def Interval.origin (n : ℕ) : Interval (Vec ℝ n) := Interval.point 0

end CORALean.Real


-- =====================================  `Interval.plus`  ====================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   01-September-2026
-- Reviewed:      ---

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/plus`: bounds add. -/
def Interval.plus (I₁ I₂ : Interval α) : Interval α where
  inf := I₁.inf + I₂.inf
  sup := I₁.sup + I₂.sup

end CORALean.Real


-- ====================================  `Interval.project`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- CORA's `@interval/project`: the bounds at the chosen coordinates, in the chosen order, which may
repeat. -/
def Interval.project (I : Interval (Vec ℝ n)) (dims : Fin m → Fin n) : Interval (Vec ℝ m) where
  inf := fun k => I.inf (dims k)
  sup := fun k => I.sup (dims k)

end CORALean.Real


-- =================================  `Interval.quadMapMixed`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {m n : ℕ}

/-- CORA's `@interval/quadMap(I₁, I₂, Q)`: the two-box form, `(x₁, x₂) ↦ x₁ᵀQₖx₂` over two
boxes, bounded through their zonotopes and `Zonotope.bilin`. -/
noncomputable def Interval.quadMapMixed (Q : Fin m → Mat ℝ n n) (I₁ I₂ : Interval (Vec ℝ n)) :
    Interval (Vec ℝ m) :=
  (Zonotope.bilin (PolyZonotope.quadBilin Q) I₁.zonotope I₂.zonotope).interval

end CORALean.Real


-- ====================================  `Interval.radius`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- Half the width: CORA's `rad`, the other half of the centre-deviation split
`Interval.center` gives a box's point. `Theorems/AbsSubCenterLe` is the bound
relating the two. -/
noncomputable def Interval.radius (I : Interval α) : α := (2:ℝ)⁻¹ • (I.sup - I.inf)

end CORALean.Real


-- ==============================  `Interval.representsa_origin`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/representsa_` at type `origin` with tolerance `0`: both bounds are zero. -/
def Interval.representsa_origin (I : Interval α) : Prop := I.inf = 0 ∧ I.sup = 0

end CORALean.Real


-- =====================================  `Interval.sign`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/sign`: `interval(sign(I.inf), sign(I.sup))`, the hull of the image. -/
noncomputable def Interval.sign (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.sign (I.inf i)
  sup := fun i => Real.sign (I.sup i)

end CORALean.Real


-- ======================================  `Interval.sin`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/sin`: `cos (I - π/2)`, the box shifted by `π/2` in every coordinate. -/
noncomputable def Interval.sin (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) :=
  let J : Interval (Vec ℝ n) :=                                     -- I - pi/2
    { inf := fun i => I.inf i - Real.pi / 2, sup := fun i => I.sup i - Real.pi / 2 }
  Interval.cos J

end CORALean.Real


-- ===================================  `Interval.supremum`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/supremum`: the upper bound. -/
def Interval.supremum (I : Interval α) : α := I.sup

end CORALean.Real


-- =====================================  `Interval.tanh`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's `@interval/tanh`: the hyperbolic tangent is strictly increasing and continuous on all of
`ℝ`, so it acts on the two bounds, coordinate by coordinate. -/
noncomputable def Interval.tanh (I : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Real.tanh (I.inf i)
  sup := fun i => Real.tanh (I.sup i)

end CORALean.Real


-- ===================================  `Interval.transpose`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {m n : ℕ}

/-- CORA's `@interval/transpose`: transpose both bound matrices. -/
def Interval.transpose (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ n m) where
  inf := I.inf.transpose
  sup := I.sup.transpose

end CORALean.Real


-- =====================================  `Interval.tril`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {m n : ℕ}

/-- CORA's `@interval/tril`: MATLAB's `tril(·, K)` on both bounds, which keeps the entries
on or below the `K`-th superdiagonal (`j ≤ i + K`) and
zeroes the rest. CORA requires `K ≥ 0` and defaults it to `0`, so `K : ℕ`. -/
def Interval.tril (K : ℕ) (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ m n) :=
  I.mask (fun i j => (j : ℕ) ≤ (i : ℕ) + K)

end CORALean.Real


-- =====================================  `Interval.triu`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {m n : ℕ}

/-- CORA's `@interval/triu`: MATLAB's `triu(·, K)` on both bounds, which keeps the entries
on or above the `K`-th superdiagonal (`i + K ≤ j`) and
zeroes the rest. CORA requires `K ≥ 0` and defaults it to `0`, so `K : ℕ`. -/
def Interval.triu (K : ℕ) (I : Interval (Mat ℝ m n)) : Interval (Mat ℝ m n) :=
  I.mask (fun i j => (i : ℕ) + K ≤ (j : ℕ))

end CORALean.Real


-- ====================================  `Interval.uminus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/uminus`: negation swaps the bounds, `[a, b]` becoming `[-b, -a]`. -/
def Interval.uminus (I : Interval α) : Interval α where
  inf := -I.sup
  sup := -I.inf

end CORALean.Real


-- =====================================  `Interval.uplus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

/-- CORA's `@interval/uplus`: unary plus, the identity. -/
def Interval.uplus (I : Interval α) : Interval α := I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
