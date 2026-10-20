module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Float.Operations.CartProd
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact

@[expose] public section

/-!
# `ZonoBundle.cartProd` is exact

For two nonempty bundles, the product's set is the pair of the two intersections, read through
`Fin.append`: a point lies in every pair `(i, j)`'s product iff its two halves lie in every
member of their bundle. `Fin.append` is injective, so the halves are determined by the point, and
the nonemptiness hypotheses are what let one member of the other bundle stand in for the pair.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Hypotheses
* `h₁` – first bundle has a member
* `h₂` – second bundle has a member

## Conclusion
* the product's set is the pairing of the two sets
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.cartProd_exact (zB₁ : ZonoBundle (Vec 𝕋 n₁)) (zB₂ : ZonoBundle (Vec 𝕋 n₂))
    (h₁ : 0 < zB₁.k) (h₂ : 0 < zB₂.k) : -- --- CONCL ---
    (zB₁.cartProd zB₂).construct =
      (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
        (zB₁.construct ×ˢ zB₂.construct) := by -- --- PROOF ---
  ext z
  -- membership in one pair's product, through the member-wise exactness
  have hp : ∀ p : Fin (zB₁.k * zB₂.k), z ∈ ((zB₁.cartProd zB₂).Z p).construct ↔
      ∃ xy : Vec ℝ n₁ × Vec ℝ n₂,
        (xy.1 ∈ (zB₁.Z (finProdFinEquiv.symm p).1).construct ∧
          xy.2 ∈ (zB₂.Z (finProdFinEquiv.symm p).2).construct) ∧ Fin.append xy.1 xy.2 = z := by
    intro p
    show z ∈ (Zonotope.cartProd (zB₁.Z (finProdFinEquiv.symm p).1)
      (zB₂.Z (finProdFinEquiv.symm p).2)).construct ↔ _
    rw [Zonotope.cartProd_exact]
    rfl
  -- the halves of `z`, which every pair's preimage must agree with
  have hz : ∀ (xp : Vec ℝ n₁) (yp : Vec ℝ n₂), Fin.append xp yp = z →
      xp = (fun i => z (Fin.castAdd n₂ i)) ∧ yp = fun i => z (Fin.natAdd n₁ i) := by
    rintro xp yp rfl
    exact ⟨funext fun i => (Fin.append_left xp yp i).symm,
      funext fun i => (Fin.append_right xp yp i).symm⟩
  constructor
  · intro h
    have h' : ∀ p, z ∈ ((zB₁.cartProd zB₂).Z p).construct := SetIntersection.mem_construct_ofFn.1 h
    refine ⟨(fun i => z (Fin.castAdd n₂ i), fun i => z (Fin.natAdd n₁ i)),
      ⟨SetIntersection.mem_construct_ofFn.2 fun i => ?_,
        SetIntersection.mem_construct_ofFn.2 fun j => ?_⟩, ?_⟩
    · -- pair `(i, 0)` stands in for member `i` of the first bundle
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := (hp _).1 (h' (finProdFinEquiv (i, ⟨0, h₂⟩)))
      simp only [Equiv.symm_apply_apply] at ha
      exact (hz a b hab).1 ▸ ha
    · -- pair `(0, j)` stands in for member `j` of the second bundle
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩ := (hp _).1 (h' (finProdFinEquiv (⟨0, h₁⟩, j)))
      simp only [Equiv.symm_apply_apply] at hb
      exact (hz a b hab).2 ▸ hb
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    refine SetIntersection.mem_construct_ofFn.2 fun p => (hp p).2 ⟨(x, y), ⟨?_, ?_⟩, rfl⟩
    · exact SetIntersection.mem_construct_ofFn.1 hx _
    · exact SetIntersection.mem_construct_ofFn.1 hy _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
