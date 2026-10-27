module

public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerApproxImage
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerGeneralSubsetImage
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerSpecialSubsetImage

@[expose] public section

/-!
# `innerApproxImage` returns inner boxes

Every box `innerApproxImage` returns was accepted by `innerSpecial` or `innerGeneral`, whose
guarantees put it inside the image of the domain `X` under the dependent point map; how the
search reached it, and whether `Y_` encloses the image of `X_`, does not matter. This is the
inner half of [1, Alg. 1]: the union of the boxes of `LInside` lies in `range(f, x)`.

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `tol` – tolerance
* `inv` – matrix inverse routine
* `iter` – number of iterations
* `depth` – splitting depth
* `X₀` – inner factor box

## Hypotheses
* none

## Conclusion
* every returned box lies in the image of the factor box

## References

* [1] [A. Goldsztejn and L. Jaulin. "Inner approximation of the range of vector-valued functions".
      Reliable Computing, 2010.](../../../../../../references/2010/goldsztejn-rc-inner-range.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.innerApproxImage_subset_image (pZ : PolyZonotope (Vec 𝕋 n))
    (X : Interval (Vec 𝕋 pZ.p)) (tol : 𝕋) (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k)
    (iter depth : ℕ) (X₀ : Interval (Vec 𝕋 pZ.p)) : -- --- CONCL ---
    ∀ Y ∈ PolyZonotope.innerApproxImage pZ X tol inv iter depth X₀,
      Y.construct ⊆ (PolyZonotope.nominal pZ).point '' X.construct := by -- --- PROOF ---
  induction depth generalizing X₀ with
  | zero => intro Y hY; cases hY
  | succ depth ih =>
    intro Y hY
    simp only [PolyZonotope.innerApproxImage] at hY
    split_ifs at hY
    -- a box `Inner` accepted, a box of one of the halves, or nothing
    all_goals first
      | exact absurd hY List.not_mem_nil
      | exact (‹False›).elim
      | (rw [List.mem_singleton] at hY
         subst hY
         first
           | exact PolyZonotope.innerSpecial_subset_image pZ X X₀ _ inv iter ‹_› ‹_›
           | exact PolyZonotope.innerGeneral_subset_image pZ X X₀ _ inv iter ‹_›)
      | (split at hY
         · cases hY
         · rcases List.mem_append.mp hY with h | h <;> exact ih _ Y h)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
