import CORALean.ContSet.Zonotope.Float.Operations.EncloseMany
import CORALean.ContSet.Zonotope.Float.Theorems.EncloseManyBasisInvMem
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Float.Theorems.ReduceGirardOuter
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

/-!
# `encloseMany` encloses every cell

Outer, not exact: each cell is first reduced to a parallelotope containing it
(`reduceGirard_outer`), mapped to the rotated frame by a member of the box that holds `R⁻¹`
(`mtimesIntervalMat_outer`, `encloseManyBasisInv_mem`), boxed (`interval_contains`), and the box,
a zonotope (`Interval.zonotope_contains`), is mapped back by `R` (`mtimes_outer`). The member of
the box inverts `R`, so a point returns to itself. The result is a statement about the float sets
(`construct`, error boxes included) of the cells and of the result, as for every float outer
theorem; the rotation is the one the stored floats read as, so it is invertible without any
hypothesis on `direction` beyond the test `encloseMany` makes.

Source: [1].

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.encloseMany_outer (p : ℕ) (Zs : Fin (q + 1) → Zonotope 𝕋 (m + 1))
    (direction : Vec 𝕋 (m + 1)) (E : Zonotope 𝕋 (m + 1))
    (hE : Zonotope.encloseMany p Zs direction = some E) (i : Fin (q + 1)) :
    (Zs i).construct ⊆ E.construct := by -- --- PROOF ---
  unfold Zonotope.encloseMany at hE
  dsimp only at hE
  split_ifs at hE with hg
  rw [Option.some.injEq] at hE
  subst hE
  -- the nonzero test, as the hypothesis the inverse needs
  have hg' := Bool.or_eq_true_iff.mp hg
  obtain ⟨A, hA, hRA⟩ := Zonotope.encloseManyBasisInv_mem
    (fun i => divDown (direction i) (normUp p direction)) hg'
  set IM := Zonotope.encloseManyBasisInv (fun i => divDown (direction i) (normUp p direction))
  intro x hx
  -- the cell, its parallelotope, and the image of that under a member of the box
  have h1 := Zonotope.reduceGirard_outer (Zs i) 1 hx
  have h2 := Zonotope.mtimesIntervalMat_outer IM ((Zs i).reduceGirard 1)
    (Set.mem_iUnion₂.mpr ⟨A, hA, Set.mem_image_of_mem _ h1⟩)
  -- its interval hull, then the hull over all cells
  have h3 := Zonotope.interval_contains _ h2
  have h4 : A *ᵥ x ∈ Interval.construct (⟨fun k => minimumOver fun i =>
        ((Zonotope.mtimesIntervalMat IM ((Zs i).reduceGirard 1)).interval).inf k,
      fun k => maximumOver fun i =>
        ((Zonotope.mtimesIntervalMat IM ((Zs i).reduceGirard 1)).interval).sup k⟩ :
      Interval (Vec 𝕋 (m + 1))) := fun k =>
    ⟨le_trans (minimumOver_le (fun i =>
        ((Zonotope.mtimesIntervalMat IM ((Zs i).reduceGirard 1)).interval).inf k) i) (h3 k).1,
      le_trans (h3 k).2 (le_maximumOver (fun i =>
        ((Zonotope.mtimesIntervalMat IM ((Zs i).reduceGirard 1)).interval).sup k) i)⟩
  -- rotated back, the point returns to itself
  have h5 := Zonotope.mtimes_outer
    (Zonotope.encloseManyBasis (fun i => divDown (direction i) (normUp p direction))) _
    (Set.mem_image_of_mem _ (Interval.zonotope_contains _ h4))
  rwa [hRA x] at h5

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
