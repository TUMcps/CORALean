module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErr
public import CORALean.ContDynamics.NonlinearSys.Theorems.LagrangeRemainderMono
public import CORALean.ContDynamics.NonlinearSys.Theorems.VarInputsMono

@[expose] public section

/-!
# `[2, Lemma 3]`: the abstraction error grows with what it is computed from

`[2]`'s property (7) for `[2, Alg. 2]`, an inclusion and not an equality: every step of Alg. 2
is monotone, so the composition is. The Cartesian products, `varInputs` and the final `⊕` are
exact, hence monotone, and `lagrangeRemainder` is monotone for a reason of its own. Kept as
hypotheses are `[2]`'s own standing assumption (its Sec. 2.3) at the two steps whose
implementations do not have it: `hpost` for `[1, Sec. 4.1]`'s `postΔ`, and `hZ` for `zono`,
which `zonotope_not_mono` refutes outright. `hE` is not added: `E` bounds a third derivative.

## Inputs
* `sys` – linear system
* `r` – time step
* `η` – Taylor terms
* `B` – input matrix
* `D` – Hessian family
* `E` – third-derivative bounds
* `U` – input range
* `UΔ` – varying input range
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `zs` – expansion point
* `R₁` – first reachable set
* `R₂` – second reachable set
* `Ψ₁` – first applied error
* `Ψ₂` – second applied error

## Hypotheses
* `hE` – bounds nonnegative
* `hR` – reachable sets nested
* `hpost` – error propagation monotone
* `hZ` – zonotopes nested

## Conclusion
* larger sets give a larger abstraction error

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
