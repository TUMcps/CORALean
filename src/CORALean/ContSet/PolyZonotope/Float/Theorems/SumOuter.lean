import CORALean.ContSet.PolyZonotope.Float.Operations.Sum
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.Interval.Float.Theorems.OriginExact
import CORALean.ContSet.PolyZonotope.Float.Theorems.SumErrMem

/-!
# `PolyZonotope.sum` encloses the exact sum at the nominal sets

A point of the exact layer's `sum` of what the stored floats denote, plus a point of every
summand's error box, lies in the float `sum`. The generator blocks and exponent columns are
appended exactly as at the real layer, so the two points differ by the rounding of the centre
alone, which the `Interval.residual` of the directed sums holds; the error boxes are
added (`sumErr`, `sumErr_mem`), a box having no factors to share.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outer: the exact sum's points, with a point from each summand's box, lie in the float sum. -/
theorem PolyZonotope.sum_outer {m : ℕ} (pZ : PolyZonotope 𝕋 n)
    (L : Fin m → PolyZonotope 𝕋 n)
    (hp : ∀ i, (L i).p = pZ.p) {x : Vec ℝ n}
    (hx : x ∈ (Real.PolyZonotope.sum (nominal pZ) (fun i => nominal (L i)) hp).construct)
    {e : Vec ℝ n} (he : e ∈ pZ.err.construct) (eL : Fin m → Vec ℝ n)
    (heL : ∀ i, eL i ∈ (L i).err.construct) :
    x + e + ∑ i, eL i ∈ (pZ.sum L hp).construct := by -- --- PROOF ---
  obtain ⟨a, β, ha, hβ, hx⟩ := Real.PolyZonotope.mem_construct_iff.mp hx
  -- the stored centre is off from the exact sum by what the residual holds
  have hr := Interval.sub_mem_residual
    (lo := fun i => addDown (pZ.c i) (sumDown fun l => (L l).c i))
    (hi := fun i => addUp (pZ.c i) (sumUp fun l => (L l).c i))
    (stored := fun i => addDown (pZ.c i) (sumDown fun l => (L l).c i))
    (x := fun i => toReal (pZ.c i) + ∑ l, toReal ((L l).c i)) fun i =>
      ⟨le_trans (addDown_le_add _ _) (add_le_add (le_refl _) (sumDown_le_sum _)),
       le_trans (add_le_add (le_refl _) (sum_le_sumUp _)) (add_le_addUp _ _)⟩
  have hbox := Interval.plus_outer _ _
    ⟨e + ∑ i, eL i, Interval.plus_outer _ _ ⟨e, he, ∑ i, eL i,
      PolyZonotope.sumErr_mem _ eL heL, rfl⟩, _, hr, rfl⟩
  -- the float point at the same factors and coefficients, off by the centre's rounding
  refine ⟨fun i => toReal ((pZ.sum L hp).c i)
        + (∑ l, toReal ((pZ.sum L hp).G l i) * Real.PolyZonotope.monomial (pZ.sum L hp).E a l)
        + ∑ j, toReal ((pZ.sum L hp).GI j i) * β j,
    PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun _ => rfl⟩, _, hbox, ?_⟩
  funext i
  -- the stored blocks read back as the exact layer's appended ones, entry by entry
  let σh : Fin (∑ i, (L i).h) → Σ i, Fin (L i).h := fun j => finSigmaFinEquiv.symm j
  let σq : Fin (∑ i, (L i).q) → Σ i, Fin (L i).q := fun j => finSigmaFinEquiv.symm j
  have hG : ∀ l : Fin (pZ.h + ∑ i, (L i).h),
      toReal ((pZ.sum L hp).G l i)
      = (Real.PolyZonotope.sum (nominal pZ) (fun i => nominal (L i)) hp).G l i :=
    Fin.addCases
      (fun l => by
        show toReal ((Fin.append pZ.G (fun j =>
            (L (σh j).1).G (σh j).2)) (Fin.castAdd _ l) i)
          = (Fin.append (nominal pZ).G (fun j =>
            (nominal (L (σh j).1)).G (σh j).2) (Fin.castAdd _ l)) i
        rw [Fin.append_left, Fin.append_left]
        rfl)
      fun l => by
        show toReal ((Fin.append pZ.G (fun j =>
            (L (σh j).1).G (σh j).2)) (Fin.natAdd _ l) i)
          = (Fin.append (nominal pZ).G (fun j =>
            (nominal (L (σh j).1)).G (σh j).2) (Fin.natAdd _ l)) i
        rw [Fin.append_right, Fin.append_right]
        rfl
  -- and the independent block
  have hGI : ∀ l : Fin (pZ.q + ∑ i, (L i).q),
      toReal ((pZ.sum L hp).GI l i)
      = (Real.PolyZonotope.sum (nominal pZ) (fun i => nominal (L i)) hp).GI l i :=
    Fin.addCases
      (fun l => by
        show toReal ((Fin.append pZ.GI (fun j =>
            (L (σq j).1).GI (σq j).2)) (Fin.castAdd _ l) i)
          = (Fin.append (nominal pZ).GI (fun j =>
            (nominal (L (σq j).1)).GI (σq j).2) (Fin.castAdd _ l)) i
        rw [Fin.append_left, Fin.append_left]
        rfl)
      fun l => by
        show toReal ((Fin.append pZ.GI (fun j =>
            (L (σq j).1).GI (σq j).2)) (Fin.natAdd _ l) i)
          = (Fin.append (nominal pZ).GI (fun j =>
            (nominal (L (σq j).1)).GI (σq j).2) (Fin.natAdd _ l)) i
        rw [Fin.append_right, Fin.append_right]
        rfl
  -- the centre and the box agree up to the residual
  have hx' := hx i
  have hc : (Real.PolyZonotope.sum (nominal pZ) (fun i => nominal (L i)) hp).c i
      = toReal (pZ.c i) + ∑ l, toReal ((L l).c i) := by
    show (nominal pZ).c i + (∑ l, (nominal (L l)).c) i = _
    rw [Finset.sum_apply]
    rfl
  have hE : (pZ.sum L hp).E
      = (Real.PolyZonotope.sum (nominal pZ) (fun i => nominal (L i)) hp).E := rfl
  have hcs : toReal ((pZ.sum L hp).c i)
      = toReal (addDown (pZ.c i) (sumDown fun l => (L l).c i)) := rfl
  simp only [Pi.add_apply, Finset.sum_apply, hG, hGI, hE, hcs]
  rw [hx', hc]
  have key : ∀ d A B e s c t : ℝ,
      d + A + B + (e + s + (c + t - d)) = c + t + A + B + e + s := by
    intros; ring
  exact key _ _ _ _ _ _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
