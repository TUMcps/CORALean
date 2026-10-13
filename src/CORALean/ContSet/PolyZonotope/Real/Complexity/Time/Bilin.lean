module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Bilin
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.bilinCost`

Asserted, not proved, and the count the representation is expensive for:
`Operations/Bilin.lean` builds one generator per *pair* of extended columns,
`(h₁+1)(h₂+1)` of them, each one application of `f` and each carrying an
exponent column that is `p` additions. Nothing else is computed — the
independent block is empty and the centre is zero.

What one `f` costs is a parameter, as in `mapCost` and for the same reason: `f`
is any bilinear map, so a caller with no bound on it has no bound here. `mulCost`
is this at the entrywise product and `quadMapDepCost` at the quadratic form
family.

The `p` exponent additions are counted at unit price alongside the scalar work.
They are arithmetic, not indexing, and counting them can only make the bound
larger — which is the safe direction for an upper bound.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.bilin` costs at a pairing costing at most `cf` per
application: one `f` and `p` exponent additions per pair of extended columns. -/
def PolyZonotope.bilinCost (cf : Cost) (p h₁ h₂ : ℕ) : Cost :=
  ((h₁ + 1) * (h₂ + 1)) • (cf + ⟨p⟩)

/-- Monotone in the factor count and in both generator counts, so bounds on the
operands' sizes give a bound on the cost. -/
theorem PolyZonotope.bilinCost_mono {p p' h₁ h₁' h₂ h₂' : ℕ} (cf : Cost)
    (hp : p ≤ p') (h1 : h₁ ≤ h₁') (h2 : h₂ ≤ h₂') :
    PolyZonotope.bilinCost cf p h₁ h₂ ≤ PolyZonotope.bilinCost cf p' h₁' h₂' :=
  Nat.mul_le_mul (Nat.mul_le_mul (Nat.succ_le_succ h1) (Nat.succ_le_succ h2))
    (Nat.add_le_add_left hp _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
