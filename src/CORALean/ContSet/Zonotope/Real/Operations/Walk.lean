import CORALean.ContSet.Conversion.Real.Zonotope_to_VPolytope

/-!
# `Zonotope.walk`

The `2 (h + 1)` corners of a zonotope along a generator order, CORA's walk of `zonotope/polygon`
in two dimensions: `c - Σ g + 2 Σ_{j<k} g` for `k = 0 … h` and the same mirrored through the
centre. For generators in one half-plane, sorted by angle, these are the vertices of the
zonotope (`Zonotope.construct_subset_walk`); for any order they are corners.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The corners with `+` on the generators before `k` (first block) and after (second). -/
def Zonotope.walk (Z : Zonotope α) : Fin ((Z.h + 1) + (Z.h + 1)) → α :=
  Fin.append (fun k => Z.corner fun j => decide (j.val < k.val))
    (fun k => Z.corner fun j => !decide (j.val < k.val))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
