module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemPadVarsIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCartProdIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.LinComb
public import CORALean.ContSet.ConPolyZono.Real.Theorems.LinCombOuter
public import CORALean.ContSet.PolyZonotope.Real.Theorems.LinCombValueDependent

@[expose] public section

/-!
# `linComb` is exactly the linear combination where neither set has independent generators

The result is [1, Prop. 8], stated there for the representation of [1, Def. 5], which carries no
independent generators; hence the hypothesis `qI = 0` on both sides. `linComb_outer` is `⊆` and
needs none. `⊇` is `PolyZonotope.linComb_value_dependent`, reached at `toPolyZonotope`.

What the constraints add is that each endpoint must lie in its *own* set:
`PolyLevelSet.mem_padVars_iff` with `PolyLevelSet.mem_cartProd_iff` says the combined system holds
iff each operand's does at the factors it came with, so the fresh factor, which neither system
reads, is free to be the segment parameter.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Hypotheses
* `h₁` – first has no independent generators
* `h₂` – second has no independent generators

## Conclusion
* the linear combination is the result's set

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       11-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.linComb_exact_of_dependent (cPZ₁ cPZ₂ : ConPolyZono α)
    (h₁ : cPZ₁.qI = 0) (h₂ : cPZ₂.qI = 0) : -- --- CONCL ---
    Set.linComb cPZ₁.construct cPZ₂.construct = (cPZ₁.linComb cPZ₂).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (ConPolyZono.linComb_outer cPZ₁ cPZ₂) ?_
  rintro x ⟨a, β, hβ, hsat, rfl⟩
  -- the combined system, split back into the two operands' own and the fresh factor's box
  obtain ⟨hcp, hlast⟩ := (PolyLevelSet.mem_padVars_iff _ (Interval.unit 1) a).mp hsat
  obtain ⟨hs₁, hs₂⟩ := (PolyLevelSet.mem_cartProd_iff cPZ₁.cons cPZ₂.cons _).mp hcp
  -- the fresh factor, whose unit bound is the segment parameter's `λ ∈ [0,1]`
  obtain ⟨hl₀, hl₁⟩ := abs_le.mp ((Interval.mem_unit_iff _).mp hlast (0 : Fin 1))
  exact ⟨cPZ₁.c + ∑ i, PolyZonotope.monomial cPZ₁.E
        (fun k => a (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k))) i • cPZ₁.G i
      + ∑ j, (0 : ℝ) • cPZ₁.GI j,
    ⟨fun k => a (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k)), fun _ => 0,
      fun _ => by simp, hs₁, rfl⟩,
    cPZ₂.c + ∑ i, PolyZonotope.monomial cPZ₂.E
        (fun k => a (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k))) i • cPZ₂.G i
      + ∑ j, (0 : ℝ) • cPZ₂.GI j,
    ⟨fun k => a (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k)), fun _ => 0,
      fun _ => by simp, hs₂, rfl⟩,
    (1 + a (Fin.natAdd (cPZ₁.p + cPZ₂.p) (0 : Fin 1))) / 2, ⟨by linarith, by linarith⟩,
    PolyZonotope.linComb_value_dependent cPZ₁.toPolyZonotope cPZ₂.toPolyZonotope h₁ h₂ a β⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
