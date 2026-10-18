module

public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffRowOffset
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalCompPermAbs
public import CORALean.ContSet.Zonotope.Real.Theorems.FacetNormalEqZeroOfNotInjective
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffHRepEq
public import Mathlib.LinearAlgebra.Matrix.Dual

@[expose] public section

/-!
# [1, Thm. 3] at the `Bool × Finset` indexing of its rows

`Zonotope.minkowskiDiff_hRep_eq` has one `|·|` row per selection `S : Fin n → Fin Z_m.h`, [1,
Thm. 2]'s own indexing. `Zonotope.gen_removable_iff` and `Zonotope.gen_not_required_iff` count
over `Bool × Finset (Fin Z_m.h)` instead, one row per signed generator subset. This is the bridge:
the same set, `Z_m ⊖ Z_s`, at the rows `Zonotope.minkDiffRowNormal`/`Zonotope.minkDiffRowOffset`.

The two indexings agree because a selection is either non-injective, where its normal is `0` and
its row holds trivially, or a reordering of the increasing selection of its image, where the normal
changes by a sign; and the `±` pair of each subset is the two rows `true` and `false`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A signed row holds exactly when the sign times the unsigned normal's pairing at `x − (c⁽ᵐ⁾ −
c⁽ˢ⁾)` is within `Δd − Δd_trans`. -/
theorem aux_row_iff {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 2))) (b : Bool)
    (T : Finset (Fin Zm.h)) (hT : T.card = n + 1) (x : Vec ℝ (n + 2)) : -- --- STMT ---
    dotProductEquiv ℝ _ (Zm.minkDiffRowNormal (b, T)) x ≤ Zm.minkDiffRowOffset Zs (b, T)
      ↔ (if b then (1 : ℝ) else -1) *
            (Zm.facetNormal (T.orderEmbOfFin hT) ⬝ᵥ (x - (Zm.c - Zs.c)))
          ≤ (∑ υ, |Zm.facetNormal (T.orderEmbOfFin hT) ⬝ᵥ Zm.G υ|) -
              ∑ υ,
                |Zm.facetNormal (T.orderEmbOfFin hT) ⬝ᵥ Zs.G υ| := by -- --- PROOF ---
  have hs : |(if b then (1 : ℝ) else -1)| = 1 := by cases b <;> simp
  have hn : Zm.minkDiffRowNormal (b, T)
      = (if b then (1 : ℝ) else -1) • Zm.facetNormal (T.orderEmbOfFin hT) := by
    simp [Zonotope.minkDiffRowNormal, hT]
  have habs : ∀ w : Vec ℝ (n + 2),
      |Zm.minkDiffRowNormal (b, T) ⬝ᵥ w| = |Zm.facetNormal (T.orderEmbOfFin hT) ⬝ᵥ w| := by
    intro w
    rw [hn, smul_dotProduct, smul_eq_mul, abs_mul, hs, one_mul]
  simp only [dotProductEquiv_apply_apply, Zonotope.minkDiffRowOffset, habs]
  simp only [hn, smul_dotProduct, smul_eq_mul, dotProduct_sub, mul_sub]
  constructor <;> intro h <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3] at `Bool × Finset` rows: `Z_m ⊖ Z_s` is cut out by the signed generator subsets of
size `n + 1`, at `Zonotope.minkDiffRowNormal` and `Zonotope.minkDiffRowOffset`. -/
theorem Zonotope.minkowskiDiff_rows_eq {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 2)))
    (hspan : Submodule.span ℝ (Set.range Zm.G) = ⊤) : -- --- STMT ---
    minkowskiDiff Zm.construct Zs.construct
      = {x | ∀ j : Bool × Finset (Fin Zm.h), j.2.card = n + 1 →
          dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤
            Zm.minkDiffRowOffset Zs j} := by -- --- PROOF ---
  classical
  have h3 := Zm.minkowskiDiff_hRep_eq (n := n + 1) Zs hspan
  rw [h3]
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- each signed subset is the increasing selection of it, up to the sign
    rintro hx ⟨b, T⟩ hT
    refine (aux_row_iff Zm Zs b T hT x).mpr ?_
    have hle := hx (T.orderEmbOfFin hT)
    calc _ ≤ |(if b then (1 : ℝ) else -1) *
            (Zm.facetNormal (T.orderEmbOfFin hT) ⬝ᵥ (x - (Zm.c - Zs.c)))| := le_abs_self _
      _ = |Zm.facetNormal (T.orderEmbOfFin hT) ⬝ᵥ (x - (Zm.c - Zs.c))| := by
        cases b <;> simp only [Bool.false_eq_true, if_true, if_false, one_mul, neg_one_mul, abs_neg]
      _ ≤ _ := hle
  · -- a selection repeats a generator, or reorders a subset's increasing selection
    intro hx S
    by_cases hinj : Function.Injective S
    · set T : Finset (Fin Zm.h) := Finset.univ.image S with hTdef
      have hT : T.card = n + 1 := by
        rw [hTdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      set S0 := T.orderEmbOfFin hT with hS0
      -- every entry of `S` lies in its image
      have hmem : ∀ i, S i ∈ T := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ _)
      -- the reordering taking the increasing selection to `S`
      set iso := T.orderIsoOfFin hT with hiso
      have hinj' : Function.Injective fun i => iso.symm ⟨S i, hmem i⟩ := fun i k hik => by
        have := iso.symm.injective hik
        exact hinj (congrArg Subtype.val this)
      set σ : Equiv.Perm (Fin (n + 1)) :=
        Equiv.ofBijective _ ⟨hinj', Finite.injective_iff_surjective.mp hinj'⟩ with hσdef
      have hσ : S = S0 ∘ σ := by
        funext i
        have : (iso (iso.symm ⟨S i, hmem i⟩) : Fin Zm.h) = S i := by
          rw [OrderIso.apply_symm_apply]
        rw [← this, Finset.coe_orderIsoOfFin_apply] at *
        simp [hσdef, hS0]
      -- the `true` and `false` rows of the subset are the two sides of the absolute value
      have hpos := (aux_row_iff Zm Zs true T hT x).mp (hx (true, T) hT)
      have hneg := (aux_row_iff Zm Zs false T hT x).mp (hx (false, T) hT)
      simp only [if_true, one_mul] at hpos
      simp only [Bool.false_eq_true, if_false, neg_one_mul] at hneg
      -- so the entries of the row, and its offset, are those at the increasing selection
      have hD : ∀ y : Vec ℝ (n + 2), |Zm.facetNormal S ⬝ᵥ y| = |Zm.facetNormal S0 ⬝ᵥ y| := by
        intro y
        rw [hσ]
        rw [dotProduct_comm, dotProduct_comm (Zm.facetNormal S0)]
        exact Zm.abs_dot_facetNormal_comp_perm S0 σ y
      rw [hD, Finset.sum_congr rfl fun υ _ => hD (Zm.G υ),
        Finset.sum_congr rfl fun υ _ => hD (Zs.G υ)]
      exact abs_le.mpr ⟨by linarith, hpos⟩
    · rw [Zm.facetNormal_eq_zero_of_not_injective S hinj]
      simp
end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
