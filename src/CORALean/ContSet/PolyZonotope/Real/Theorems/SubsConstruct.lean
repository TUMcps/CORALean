module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsPoint

@[expose] public section

/-!
# `subs` denotes the substituted set

The set `subs(pZ, pZin, idu)` denotes is exactly `pZ`'s with each replaced factor `idu ii` set to
output `ii` of `pZin`, over the unit box of the result's factors and of `pZ`'s independent
generators. This is an equality, and it is the one CORA's expansion into terms is meant to
compute; the replaced value is not required to stay in `[-1, 1]`, so the set is not a subset of
`pZ`'s unless `pZin` stays in the unit box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `subs` is exactly the substitution, as a set. -/
theorem PolyZonotope.subs_construct (pZ : PolyZonotope α) {nu : ℕ}
    (pZin : PolyZonotope (Vec ℝ nu)) (idu : Fin nu → Fin pZ.p)
    (share : Fin pZin.p → Option (Fin pZ.p)) (hidu : Function.Injective idu) : -- --- STMT ---
    (pZ.subs pZin idu share).construct
      = {x | ∃ a : Fin (pZ.p + pZin.p) → ℝ, ∃ γ : Fin pZ.q → ℝ,
          (∀ k, |a k| ≤ 1) ∧ (∀ j, |γ j| ≤ 1) ∧
          x = pZ.point (Function.extend idu
                (fun ii => pZin.point (fun j => a (pZ.subsFactor pZin share j)) ii)
                (fun k => a (Fin.castAdd pZin.p k))) + ∑ j, γ j • pZ.GI j} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨a, β, ha, hβ, hx⟩
    refine ⟨a, β, ha, hβ, ?_⟩
    rw [← PolyZonotope.subs_point pZ pZin idu share hidu a]
    exact hx
  · rintro ⟨a, β, ha, hβ, hx⟩
    refine ⟨a, β, ha, hβ, ?_⟩
    rw [hx, ← PolyZonotope.subs_point pZ pZin idu share hidu a]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
