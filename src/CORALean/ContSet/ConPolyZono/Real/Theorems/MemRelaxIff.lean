module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.ExistsRelaxIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE

@[expose] public section

/-!
# What `ConPolyZono.relax` denotes

The points of `cPZ` with each constraint row met to within `|sᵢ|`. The constraint is
`PolyLevelSet.relax`, whose slack factors in `[-1, 1]` are exactly that
(`PolyLevelSet.exists_relax_iff`), and the generators do not read them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generator monomials ignore the slack factors. -/
theorem ConPolyZono.aux_monomial_relax (cPZ : ConPolyZono α) (s : Vec ℝ cPZ.cons.m)
    (a : Fin (cPZ.p + cPZ.cons.m) → ℝ) :
    PolyZonotope.monomial (cPZ.relax s).E a
      = PolyZonotope.monomial cPZ.E (fun k => a (Fin.castAdd cPZ.cons.m k)) :=
  funext fun l => ConPolyZono.monomial_padE cPZ.E cPZ.cons.m a l


-- =======================================  MAIN THEOREM  ======================================= --

/-- The relaxed set's points are the original's with every row met to within `|sᵢ|`. -/
theorem ConPolyZono.mem_relax_iff [AddCommGroup α] [Module ℝ α] (cPZ : ConPolyZono α)
    (s : Vec ℝ cPZ.cons.m) {x : α} : -- --- STMT ---
    x ∈ (cPZ.relax s).construct ↔
      ∃ a : Fin cPZ.p → ℝ, ∃ β : Fin cPZ.qI → ℝ, (∀ k, |a k| ≤ 1) ∧ (∀ j, |β j| ≤ 1)
        ∧ (∀ i, |(cPZ.cons.A *ᵥ PolyZonotope.monomial cPZ.cons.R a) i - cPZ.cons.b i| ≤ |s i|)
        ∧ x = cPZ.c + ∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i
          + ∑ j, β j • cPZ.GI j := by -- --- PROOF ---
  constructor
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    -- the factor vector splits into the old factors and the slack, which is in `[-1, 1]`
    refine ⟨fun k => a (Fin.castAdd cPZ.cons.m k), β, fun k => ha _, hβ,
      (PolyLevelSet.exists_relax_iff cPZ.cons_eq s _).mp
        ⟨fun i => a (Fin.natAdd cPZ.p i), fun i => ha _, ?_⟩, ?_⟩
    · rwa [Fin.append_castAdd_natAdd]
    · rw [hx, ConPolyZono.aux_monomial_relax]
      rfl
  · rintro ⟨a, β, ha, hβ, hs, hx⟩
    -- the slack each row needs, in `[-1, 1]`
    obtain ⟨γ, hγ, hmem⟩ := (PolyLevelSet.exists_relax_iff cPZ.cons_eq s a).mpr hs
    have hleft : (fun k => Fin.append a γ (Fin.castAdd cPZ.cons.m k)) = a :=
      funext fun k => Fin.append_left a γ k
    have hbox : ∀ k, |Fin.append a γ k| ≤ 1 :=
      Fin.addCases (fun k => by simpa using ha k) (fun i => by simpa using hγ i)
    refine ⟨Fin.append a γ, β, hbox, hβ, hmem, ?_⟩
    rw [hx]
    show _ = cPZ.c + ∑ i, PolyZonotope.monomial (cPZ.relax s).E (Fin.append a γ) i • cPZ.G i
      + ∑ j, β j • cPZ.GI j
    rw [ConPolyZono.aux_monomial_relax, hleft]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
