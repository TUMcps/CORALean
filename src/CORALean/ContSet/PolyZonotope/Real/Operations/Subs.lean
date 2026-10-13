module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsTerms
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsFactor

@[expose] public section

/-!
# `PolyZonotope.subs`

CORA's `@polyZonotope/subs(pZ, pZin, idu)`: the dependent factors `idu` of `pZ` are replaced by the
outputs of the polynomial zonotope `pZin` (no independent generators), whose own factors become
factors of the result, shared with `pZ`'s where the identifiers agree.

Each generator is scaled by `∏ᵢ αᵤ(ᵢ)^e`; substituting `αᵤ(ᵢ) = (pZin)ᵢ(β)` gives a product of
powers of polynomials in `β`, expanded into one generator per term (`subsXprod`, `subsTerms`).
CORA then merges equal columns and moves constant ones into the centre
(`removeRedundantExponents`, `priv_removeZeroExponents`): same set, left out. Its shortcut for a
`pZin` without centre and at most one monomial per output computes the same terms.

Identifiers are indices: `idu i` is the factor of `pZ` that output `i` replaces, the result's
factors are `pZ`'s (the replaced ones left as zero rows) and then `pZin`'s (`subsFactor`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `subs(pZ, pZin, idu)`. -/
noncomputable def PolyZonotope.subs (pZ : PolyZonotope α) {nu : ℕ} (pZin : PolyZonotope (Vec ℝ nu))
    (idu : Fin nu → Fin pZ.p) (share : Fin pZin.p → Option (Fin pZ.p)) : PolyZonotope α :=
  -- the replaced factors
  let S : Finset (Fin pZ.p) := Finset.univ.image idu
  -- one generator of the result per term of each `Xprod`
  let terms := pZ.subsTerms pZin idu
  { p := pZ.p + pZin.p
    h := terms.length
    q := pZ.q
    c := pZ.c
    G := fun l => (terms.get l).2.1 • pZ.G (terms.get l).1
    -- the exponents of `pZ`'s remaining factors, and those of the term in `pZin`'s factors
    E := fun r l =>
      Fin.addCases (fun k => if k ∈ S then 0 else pZ.E k (terms.get l).1) (fun _ => 0) r
        + ∑ j ∈ Finset.univ.filter (fun j => pZ.subsFactor pZin share j = r),
            (terms.get l).2.2 j
    GI := pZ.GI }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
