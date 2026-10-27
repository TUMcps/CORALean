module

public import CORALean.ContSet.Zonotope.Real.Definitions.ZonotopeNorm
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.polymax`

`[1, Alg. 2]` (maximal polyhedral norm), CORA's `contains_(Z, S, 'exact:polymax')`: for
each facet `ηᵢ x ≤ hᵢ` of `Z₂`, the vertex of `Z₁` furthest along `ηᵢ` takes the sign of
`ηᵢ gⱼ / hᵢ` per generator; `Z₁ ⊆ Z₂` iff none of these `s` vertices has
`‖v - c₂‖_{Z₂} > 1`. `halfspace(Z₂)` is supplied, as the representation of `Z₂` moved to the
origin (`[1, Def. 3]` needs `0` inside for the signs to be right). The printed listing tests
`‖x - c₂‖` at the sign vector `x ∈ ℝ^{m₁}` itself and writes `νᵢ` for `ηᵢ`; it is the vertex
`c₁ + G₁ x` that is tested here.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `s` – facet count
* `H` – facet normal matrix
* `h` – facet offsets

## Output
* `true` iff the maximization certifies the test

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Alg. 2]` against the facets `{H x ≤ h}` of `Z₂ - c₂`. -/
noncomputable def Zonotope.polymax (Z₁ Z₂ : Zonotope (Vec ℝ n)) {s : ℕ} (H : Mat ℝ s n)
    (h : Vec ℝ s) : Bool :=
  -- 4. for `i = 1, …, s` and `j = 1, …, m₁`, `x_j ← 1` if `η_iᵀ g_j / h_i ≥ 0`, else `-1`
  let x : Fin s → Fin Z₁.h → ℝ := fun i j => if (H *ᵥ Z₁.G j) i / h i ≥ 0 then 1 else -1
  -- 5. the vertex `c₁ + G₁ x` is what is tested, not `x` itself; `(H, h)` is given
  let v : Fin s → Vec ℝ n := fun i => Z₁.c + ∑ j, x i j • Z₁.G j
  -- 6. return False if some `‖v - c₂‖_{Z₂} > 1`, and True otherwise
  if ∀ i, ¬ Z₂.zonotopeNorm (v i - Z₂.c) > 1 then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
