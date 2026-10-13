import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErr
import CORALean.ContDynamics.NonlinearSys.Theorems.LagrangeRemainderMono
import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsMono

/-!
# `[2, Lemma 3]`: the abstraction error grows with what it is computed from

`[2]`'s property (7) for `[2, Alg. 2]`, an inclusion and not an equality, proved
the way `[2]` proves it: every step of Alg. 2 is monotone, so the composition is.

What `[2]` assumes and this discharges: the Cartesian products, `varInputs` and
the final `⊕` are exact, hence monotone, and `lagrangeRemainder` is monotone for
a reason of its own. What it keeps as a hypothesis is `[2]`'s own standing
assumption — its Sec. 2.3, that *every* operation it uses satisfies (6) or (7) —
at the two steps whose implementations do not have it: `hpost` for
`[1, Sec. 4.1]`'s `postΔ`, whose `linComb` and interval-matrix product both read
the representation rather than the set, and `hZ` for `zono`, which
`zonotope_not_mono` refutes outright.

`Ψ` reaches the result through `postΔ` alone, so `[2]`'s hypothesis
`Ψ⁽¹⁾ ⊆ Ψ⁽²⁾` is spent exactly there and appears as `hpost` rather than on its
own. `hE` is not an added hypothesis: `E` bounds a third derivative entrywise.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
* [2] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix Scalar

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[2, Lemma 3]`: a larger reachable set and a larger applied error give a
larger abstraction error, over a larger region. -/
theorem abstrErr_mono (sys : LinearSys 𝕋 n) (r : ℝ) (η : ℕ) (B : Mat ℝ n m)
    (D : Fin n → Mat ℝ (n + m) (n + m)) {E : Fin n → Fin (n + m) → Mat ℝ (n + m) (n + m)}
    (hE : ∀ i j k l, 0 ≤ E i j k l) (U UΔ : PolyZonotope (Vec ℝ m))
    {Z₁ Z₂ : Zonotope (Vec ℝ (n + m))} (zs : Vec ℝ (n + m))
    {R₁ R₂ Ψ₁ Ψ₂ : PolyZonotope (Vec ℝ n)} (hR : R₁.construct ⊆ R₂.construct)
    (hpost : (sys.postDelta (S := 𝒫𝒵) r η R₁ Ψ₁).construct
      ⊆ (sys.postDelta (S := 𝒫𝒵) r η R₂ Ψ₂).construct)
    (hZ : Z₁.construct ⊆ Z₂.construct) :
    (abstrErr sys r η B D E U UΔ Z₁ zs R₁ Ψ₁).construct
      ⊆ (abstrErr sys r η B D E U UΔ Z₂ zs R₂ Ψ₂).construct :=
  PolyZonotope.plus_mono
    (varInputs_mono B D
      (PolyZonotope.plus_mono (PolyZonotope.map_mono _ hR) subset_rfl)
      (PolyZonotope.plus_mono (PolyZonotope.map_mono _ hpost) subset_rfl))
    (lagrangeRemainder_mono hE hZ zs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
