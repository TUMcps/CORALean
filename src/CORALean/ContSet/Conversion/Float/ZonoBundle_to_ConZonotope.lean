module

public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component, over a floating-point scalar

Through `ZonoBundle.zonotope i`, then the constrained zonotope with nothing to
satisfy. Whichever component `i` names, the guarantee holds.

`conZonotopeAll` keeps every member instead: the first member's constrained
zonotope intersected, one `ConZonotope.intersection` at a time, with each of the
others, which is CORA's `conZonotope(zB)` — every member's generators side by
side, tied together by agreement rows. Outer, as each intersection is, so the
whole bundle lies inside it; needs a first member, `0 < k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `cZ` intersected with each member of a family in turn. -/
def ZonoBundle.aux_interFrom (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : {k : ℕ} →
    (Fin k → Zonotope (Vec 𝕋 n)) →
    ConZonotope 𝕋 (Vec 𝕋 n)
  | 0, _ => cZ
  | _ + 1, Z => ZonoBundle.aux_interFrom (cZ.intersection (Z 0).conZonotope) fun i => Z i.succ

theorem ZonoBundle.aux_subset_interFrom {S : Set (Vec ℝ n)} :
    ∀ {k : ℕ} (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (Z : Fin k → Zonotope (Vec 𝕋 n)),
      S ⊆ cZ.construct → (∀ i, S ⊆ (Z i).construct) →
      S ⊆ (ZonoBundle.aux_interFrom cZ Z).construct := by -- --- PROOF ---
  intro k
  induction k with
  | zero => intro cZ _ h _; exact h
  | succ k ih =>
    intro cZ Z h hZ
    refine ih _ _ (fun x hx => ConZonotope.intersection_outer _ _ ⟨h hx, ?_⟩) fun i => hZ i.succ
    exact Zonotope.conZonotope_contains _ (hZ 0 hx)


def ZonoBundle.conZonotope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  (zB.zonotope i).conZonotope

/-- Every member at once: the first member's constrained zonotope, intersected
with each of the rest. -/
def ZonoBundle.conZonotopeAll (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) : ConZonotope
    𝕋 (Vec 𝕋 n) :=
  ZonoBundle.aux_interFrom (zB.conZonotope ⟨0, hk⟩)
    fun (i : Fin (zB.k - 1)) => zB.zonotope ⟨i + 1, by omega⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conZonotope_contains _)

theorem ZonoBundle.conZonotopeAll_contains (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.conZonotopeAll hk).construct :=
  ZonoBundle.aux_subset_interFrom _ _ (zB.conZonotope_contains ⟨0, hk⟩)
    fun _ => zB.zonotope_contains _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
