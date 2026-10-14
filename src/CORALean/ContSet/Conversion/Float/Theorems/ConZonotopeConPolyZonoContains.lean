module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeSatisfiesConPolyZono

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope, over a

floating-point scalar

Nothing rounds. The constraint matrix is the two blocks of `P` stacked, the
upper bounds are `P`'s own, and the error box is carried across, so the only
value computed is the lower bound an inequality does not have — and it is
computed upward in absolute value, which makes it a bound rather than a cut.

Not routed through the exact layer's conversion. There a constraint is a
functional and the coefficients have to be read back off it; here they are
already a matrix, and the exact layer's `HPolytope` reading of a float one
turns each interval-valued equality into a pair of inequalities, so the two
constructions do not agree row for row even though they denote the same set.
Membership is the shorter argument.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

-- the point survives as it stands: identity exponents make every monomial a factor
theorem ConZonotope.conPolyZono_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.conPolyZono.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨β, fun _ => 0, hβ, fun j => j.elim0,
    ConZonotope.satisfies_conPolyZono cZ hβ hP, fun i => ?_⟩
  rw [hx i]
  simp only [ConZonotope.conPolyZono, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Real.PolyZonotope.monomial_identE]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
