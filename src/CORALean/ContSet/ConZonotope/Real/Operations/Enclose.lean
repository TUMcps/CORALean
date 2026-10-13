import CORALean.ContSet.ConZonotope.Real.ConZonotope

/-!
# `ConZonotope.enclose`

CORA's `@conZonotope/enclose`: encloses `cZ₁` and an affine image `cZ₂` of it,
the two carrying the *same* constraint system — `hh` lines up the coefficient
counts, which is what lets `cZ₂`'s constraints be read at `cZ₁`'s index.

Unlike CORA, which refuses the general case by throwing, the hypothesis here is
a precondition of `enclose_outer` alone: the shape below type-checks for any two
constrained zonotopes of equal `h`, and only the soundness proof asks that `P`
agree too. `P` itself carries no constraint on the two fresh blocks the
construction adds, which is what CORA's zero-padded `A` says as well.

Not a `LinComb` instance, for the same reason `Zonotope.minkDiffAligned` is not
a `MinkDiff` one: `hh` is a fact about the particular pair of operands, and
`linComb` already covers every pair, so this sits beside it as the cheaper
construction for the aligned case. Only an enclosure of the segment between the
two sets, even where the constraints agree — `enclose_outer` is as far as the
guarantee goes.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre and generator average and half-difference, CORA's `enclose`
construction. `hh` casts `cZ₂`'s generators and constraints against `cZ₁`'s
own index. -/
noncomputable def ConZonotope.enclose (cZ₁ cZ₂ : ConZonotope α) (hh : cZ₁.h = cZ₂.h) :
    ConZonotope α :=
  let mid := (2:ℝ)⁻¹ • (cZ₁.c + cZ₂.c)                          -- the segment's midpoint
  -- generators both keep
  let shared := fun j => (2:ℝ)⁻¹ • (cZ₁.G j + cZ₂.G (Fin.cast hh j))
  -- generators they differ on
  let apart := fun j => (2:ℝ)⁻¹ • (cZ₁.G j - cZ₂.G (Fin.cast hh j))
  let half := fun _ : Fin 1 => (2:ℝ)⁻¹ • (cZ₁.c - cZ₂.c)         -- the segment's own generator
  { h := cZ₁.h + cZ₁.h + 1
    c := mid
    G := Fin.append (Fin.append shared apart) half
    P := cZ₁.P.comap ((blockLeft cZ₁.h cZ₁.h).comp (blockLeft (cZ₁.h + cZ₁.h) 1)) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
