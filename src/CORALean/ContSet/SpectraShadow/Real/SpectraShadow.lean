module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# Spectrahedral shadows: the representation

CORA's `spectraShadow` [1]: the projection of a spectrahedron, the set of every `c + G β` for which
the linear matrix inequality `A₀ + Σᵢ βᵢ Aᵢ ⪰ 0` holds. `⪰` is Mathlib's `Matrix.PosSemidef`, so the
matrices are real and a point satisfies the inequality only if the combination is symmetric. CORA
stacks the matrices as `[A0 A1 ... Am]`; here `A₀` and the family `A` are separate fields, so `plus`
can append two families without renumbering. Every convex set a conic program can describe is of
this form, the representation a sum or an image can always land in. Membership, emptiness and the
support function are semidefinite programs, so none is computed: `construct` is the specification.
Over any real module, as a zonotope is.

## References

* [1] `contSet/@spectraShadow/spectraShadow.m`, CORA (Sep. 2025). The header
      cites T. Netzer, "Spectrahedra and Their Shadows", Habilitation thesis,
      Universität Leipzig, 2011, which is not cited here: no numbered result of
      it is used.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

structure SpectraShadow (α : Type) where
  /-- The size of the matrices in the inequality. -/
  k : ℕ
  /-- The number of free variables `β`, and of generators. -/
  m : ℕ
  A₀ : Mat ℝ k k
  A : Fin m → Mat ℝ k k
  c : α
  G : Fin m → α

def SpectraShadow.construct (S : SpectraShadow α) : Set α :=
  {x | ∃ β : Fin S.m → ℝ, (S.A₀ + ∑ i, β i • S.A i).PosSemidef ∧ x = S.c + ∑ i, β i • S.G i}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
