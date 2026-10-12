import CORALean.ContSet.PolyZonotope.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Operations.BoxDiffBounds

/-!
# The factor bounds of a non-convex inner approximation

[1, Alg. 1]: shrink the factor box `[α̲, ᾱ]` of an outer approximation `⟨G, E⟩_PZ` until the
restriction `C(α̲, ᾱ)` misses each piece `PZₖ` of the boundary enclosure `B`, [1, Eq. 8]: the
constraint of [1, Prop. 2] (line 3), a contraction of the box with each piece's factors
appended in `[-1, 1]` (line 4), its projection (line 5) and the box difference of [1, Prop. 3],
stored as bounds (line 6, `boxDiffBounds`). The contractor is an argument, as [1] leaves it:
any that [1, Def. 3] admits, `IsBoundsContractor`. `C(α̲, ᾱ)` is `pZ.subsetAt (Icc α̲ ᾱ)`.

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the bounds `(α̲, ᾱ)` after one pass over the pieces `PZₖ` of `B`. -/
noncomputable def PolyZonotope.innerScaling (pZ : PolyZonotope α) (B : List (PolyZonotope α))
    (contract : ∀ m : ℕ, ((Fin m → ℝ) → α) → (Fin m → ℝ) × (Fin m → ℝ) →
      (Fin m → ℝ) × (Fin m → ℝ)) : (Fin pZ.p → ℝ) × (Fin pZ.p → ℝ) :=
  let init : (Fin pZ.p → ℝ) × (Fin pZ.p → ℝ) := (-1, 1)
  let step := fun (bounds : (Fin pZ.p → ℝ) × (Fin pZ.p → ℝ)) (PZk : PolyZonotope α) =>
    let c := fun x : Fin (pZ.p + PZk.p) → ℝ =>
      pZ.point (fun i => x (Fin.castAdd PZk.p i)) - PZk.point (fun j => x (Fin.natAdd pZ.p j))
    let I := contract (pZ.p + PZk.p) c (Fin.append bounds.1 (-1), Fin.append bounds.2 1)
    let Iproj := (fun i => I.1 (Fin.castAdd PZk.p i), fun i => I.2 (Fin.castAdd PZk.p i))
    boxDiffBounds bounds.1 bounds.2 Iproj.1 Iproj.2
  B.foldl step init

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
