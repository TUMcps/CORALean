import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPoly
import CORALean.ContSet.PolyZonotope.Float.Operations.EvalPolyFactorCount
import CORALean.ContSet.PolyZonotope.Float.Theorems.AbsLeErrorBound
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemGeneratorErrorMonomial
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MulGClose
import CORALean.ContSet.PolyZonotope.Real.Theorems.EvalPolyExact

/-!
# `PolyZonotope.evalPoly` encloses the exact evaluation, rounding outward

The gap `evalPoly_p`'s exactness argument never has to close: at the exact
layer, `R`'s point is `S`'s multiplied in without residue. Here `R` is already
only an enclosure, so the same product costs the extra term `evalPolyStep`'s
box already carries, `errorBound R.err * evalPolyBoundS S`. `mulG_close`
prices what `mul` itself rounds, `Interval.sub_mem_residual` what the centre
shift rounds, and the two combine with that extra term through `Interval.plus`.

The induction carries a single admissible factor vector `b` through every
level, exactly as `evalPolyP_point` does over ℝ: the point-level statement is
what makes chaining sound, where a set-level one would let the two layers
re-witness independently and identify unrelated slack.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|nominal S|` is at most its centre plus every generator's magnitude, since
every monomial is at most `1`. -/
theorem PolyZonotope.aux_point_le_boundS (S : PolyZonotope 𝕋 n) (b : Fin S.p → ℝ)
    (hb : ∀ k, |b k| ≤ 1) (i : Fin n) :
    |Real.PolyZonotope.point (nominal S) b i|
      ≤ toReal (PolyZonotope.evalPolyBoundS S i) := by -- --- PROOF ---
  -- unfold the point at `i`, `nominal S`'s fields read back as `S`'s own
  have h1 : Real.PolyZonotope.point (nominal S) b i
      = toReal (S.c i) + ∑ l, toReal (S.G i l) * Real.PolyZonotope.monomial S.E b l := by
    show ((nominal S).c + ∑ l, Real.PolyZonotope.monomial (nominal S).E b l • (nominal S).G l) i
      = toReal (S.c i) + ∑ l, toReal (S.G i l) * Real.PolyZonotope.monomial S.E b l
    rw [Pi.add_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    have hG : (nominal S).G l i = toReal (S.G i l) := rfl
    have hE : (nominal S).E = S.E := rfl
    rw [hG, hE, mul_comm]
  have h2 := abs_sum_le_radius (d := S.G) (Δ := fun i l => toReal (S.G i l))
    (β := fun l => Real.PolyZonotope.monomial S.E b l) (fun i l => le_refl _)
    (fun l => Real.PolyZonotope.abs_monomial_le_one S.E hb l) i
  rw [h1]
  calc |toReal (S.c i) + ∑ l, toReal (S.G i l) * Real.PolyZonotope.monomial S.E b l|
      ≤ |toReal (S.c i)| + |∑ l, toReal (S.G i l) * Real.PolyZonotope.monomial S.E b l| :=
        abs_add_le _ _
    _ ≤ toReal (absolute (S.c i)) + toReal (radius S.G i) := by
        rw [toReal_absolute]; linarith
    _ ≤ toReal (PolyZonotope.evalPolyBoundS S i) := add_le_addUp _ _

/-- The Horner recursion's invariant: the gap between the exact value (from `S`'s
stored floats, with no further rounding) and the float accumulator's own stored
value lies in that accumulator's error box, at every admissible `b`. -/
theorem PolyZonotope.aux_evalPoly_close (S : PolyZonotope 𝕋 n) (coeffs : List (Vec 𝕋 n))
    (b : Fin S.p → ℝ) (hb : ∀ k, |b k| ≤ 1) :
    (fun i => (Real.PolyZonotope.evalPolyP (nominal S) (coeffs.map toRealVec)).1.point
          (fun k => b (Fin.cast ((Real.PolyZonotope.evalPolyP (nominal S)
              (coeffs.map toRealVec)).2.trans (PolyZonotope.nominal_p S)) k)) i
        - Real.PolyZonotope.point (nominal (PolyZonotope.evalPolyP S coeffs).1)
            (fun k => b (Fin.cast (PolyZonotope.evalPolyP S coeffs).2 k)) i)
      ∈ ((PolyZonotope.evalPolyP S coeffs).1.err).construct := by -- --- PROOF ---
  -- both sides are the zero vector at the empty list, matched termwise below
  induction coeffs with
  | nil =>
    simp only [List.map_nil]
    have hzero : (fun i => (Real.PolyZonotope.evalPolyP (nominal S)
              ([] : List (Vec ℝ n))).1.point
            (fun k => b (Fin.cast ((Real.PolyZonotope.evalPolyP (nominal S)
              ([] : List (Vec ℝ n))).2.trans (PolyZonotope.nominal_p S)) k)) i
          - Real.PolyZonotope.point (nominal (PolyZonotope.evalPolyP S ([] : List (Vec 𝕋 n))).1)
              (fun k => b (Fin.cast (PolyZonotope.evalPolyP S ([] : List (Vec 𝕋 n))).2 k)) i)
        = (0 : Vec ℝ n) := by
      funext j
      simp only [Real.PolyZonotope.evalPolyP, PolyZonotope.evalPolyP]
      have hsumR : ∀ {α : Type} [AddCommMonoid α] (f : Fin (0 : ℕ) → α), ∑ x, f x = 0 :=
        fun f => Finset.sum_eq_zero fun x _ => x.elim0
      simp only [Real.PolyZonotope.point, hsumR, Pi.zero_apply, zero_add]
      -- the float side's own sum is empty too, by the same vacuous argument
      rw [Pi.add_apply, Finset.sum_apply,
        Finset.sum_eq_zero (fun x (_ : x ∈ Finset.univ) => x.elim0)]
      show (0:ℝ) - (toReal (zero : 𝕋) + 0) = 0
      rw [toReal_zero]
      ring
    rw [hzero]
    exact fun i => ⟨le_of_eq (by rw [PolyZonotope.evalPolyP]; exact toReal_zero),
      le_of_eq (by rw [PolyZonotope.evalPolyP]; exact toReal_zero.symm)⟩
  | cons a0 rest ih =>
    simp only [List.map_cons]
    set X := (Real.PolyZonotope.evalPolyP (nominal S) (rest.map toRealVec)).1 with hXdef
    set hX := (Real.PolyZonotope.evalPolyP (nominal S) (rest.map toRealVec)).2 with hXdef2
    set R := (PolyZonotope.evalPolyP S rest).1 with hRdef
    set hR := (PolyZonotope.evalPolyP S rest).2 with hRdef2
    set hXS := hX.trans (PolyZonotope.nominal_p S) with hXSdef
    -- the two casts to `S`'s factors compose to the direct one, `(nominal S).p ≡ S.p`
    have hcastX : (fun k : Fin (nominal S).p =>
          (fun k' => b (Fin.cast hXS k')) (Fin.cast hX.symm k))
        = fun k => b (Fin.cast (PolyZonotope.nominal_p S) k) := by
      funext k; congr 1
    show (Real.PolyZonotope.evalPolyStep X (nominal S) hX (toRealVec a0)).point
          (fun k => b (Fin.cast hXS k))
        - Real.PolyZonotope.point (nominal (PolyZonotope.evalPolyStep R S hR a0))
            (fun k => b (Fin.cast hR k))
      ∈ (PolyZonotope.evalPolyStep R S hR a0).err.construct
    -- the exact Horner step: `a₀ + X ⊙ (nominal S)`, `evalPolyStep_point` unfolded
    have hXstep : (Real.PolyZonotope.evalPolyStep X (nominal S) hX (toRealVec a0)).point
          (fun k => b (Fin.cast hXS k))
        = fun i => toReal (a0 i) + X.point (fun k => b (Fin.cast hXS k)) i
            * Real.PolyZonotope.point (nominal S) b i := by
      have key := Real.PolyZonotope.evalPolyStep_point X (nominal S) hX (toRealVec a0)
        (fun k => b (Fin.cast hXS k))
      simp only [hcastX] at key
      exact key
    -- the float step's nominal, `mul`'s nominal shifted by the rounded coefficient
    have hRmulC : (PolyZonotope.mul R S hR).c = fun _ => (zero : 𝕋) := rfl
    have hnomC : (nominal (PolyZonotope.mul R S hR)).c
        = fun i => toReal ((PolyZonotope.mul R S hR).c i) := rfl
    have hnomE : (nominal (PolyZonotope.evalPolyStep R S hR a0)).E
        = (nominal (PolyZonotope.mul R S hR)).E := rfl
    have hnomG : (nominal (PolyZonotope.evalPolyStep R S hR a0)).G
        = (nominal (PolyZonotope.mul R S hR)).G := rfl
    have hnomC' : (nominal (PolyZonotope.evalPolyStep R S hR a0)).c
        = fun i => toReal (FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i)) := rfl
    -- `.point` unfolded once, reused below at each specific structure
    have hpointdef : ∀ (PZ : Real.PolyZonotope (Vec ℝ n)) (c : Fin PZ.p → ℝ),
        PZ.point c = PZ.c + ∑ l, Real.PolyZonotope.monomial PZ.E c l • PZ.G l := fun _ _ => rfl
    have hnomstep : Real.PolyZonotope.point (nominal (PolyZonotope.evalPolyStep R S hR a0))
          (fun k => b (Fin.cast hR k))
        = fun i => toReal (FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i))
            + Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
                (fun k => b (Fin.cast hR k)) i := by
      rw [hpointdef, hpointdef, hnomE, hnomG, hnomC', hnomC]
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRmulC,
        toReal_zero, zero_add]
      rfl
    -- the exact product of nominals, as one sum: `mul_point`, `mul`'s centre being `0`
    have hmulPointE : (nominal (PolyZonotope.mul R S hR)).E = PolyZonotope.mulE R S hR := rfl
    have hmulPointG : (nominal (PolyZonotope.mul R S hR)).G
        = fun l i => toReal (PolyZonotope.mulGDown R S i l) := rfl
    have hmulPoint : Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
          (fun k => b (Fin.cast hR k))
        = fun i => ∑ l, toReal (PolyZonotope.mulGDown R S i l)
            * Real.PolyZonotope.monomial (PolyZonotope.mulE R S hR)
                (fun k => b (Fin.cast hR k)) l := by
      rw [hpointdef, hnomC, hRmulC, hmulPointE, hmulPointG]
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, toReal_zero,
        zero_add, smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have hmulE_eq : (Real.PolyZonotope.mul (nominal R) (nominal S) hR).E
        = PolyZonotope.mulE R S hR := rfl
    have hmulG_eq : (Real.PolyZonotope.mul (nominal R) (nominal S) hR).G
        = Real.PolyZonotope.mulG (nominal R) (nominal S) := rfl
    have hmulc0' : (Real.PolyZonotope.mul (nominal R) (nominal S) hR).c = 0 := rfl
    -- `mul_point`, `nominal R` and `nominal S`'s exact (unrounded) product
    have hRSexact : Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k))
          * Real.PolyZonotope.point (nominal S) b
        = fun i => ∑ l, Real.PolyZonotope.mulG (nominal R) (nominal S) l i
            * Real.PolyZonotope.monomial (PolyZonotope.mulE R S hR)
                (fun k => b (Fin.cast hR k)) l := by
      have key : Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k))
            * Real.PolyZonotope.point (nominal S)
                (fun k => b (Fin.cast hR (Fin.cast hR.symm k)))
          = (Real.PolyZonotope.mul (nominal R) (nominal S) hR).c
              + ∑ l, Real.PolyZonotope.monomial (Real.PolyZonotope.mul (nominal R) (nominal S) hR).E
                  (fun k => b (Fin.cast hR k)) l
                  • (Real.PolyZonotope.mul (nominal R) (nominal S) hR).G l :=
        (Real.PolyZonotope.mul_point (nominal R) (nominal S) hR
          (fun k => b (Fin.cast hR k))).symm
      rw [hmulc0', hmulE_eq, hmulG_eq] at key
      -- the double cast back to `S.p` cancels, `hR` composed with its own symm
      have hSeq : Real.PolyZonotope.point (nominal S)
            (fun k : Fin S.p => b (Fin.cast hR (Fin.cast hR.symm k)))
          = Real.PolyZonotope.point (nominal S) b := by
        congr 1
      rw [← hSeq]
      funext i
      have hkey : (Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k))
            * Real.PolyZonotope.point (nominal S)
                (fun k : Fin S.p => b (Fin.cast hR (Fin.cast hR.symm k)))) i
          = ((0 : Vec ℝ n) + ∑ l, Real.PolyZonotope.monomial (PolyZonotope.mulE R S hR)
              (fun k => b (Fin.cast hR k)) l
              • Real.PolyZonotope.mulG (nominal R) (nominal S) l) i :=
        congrFun key i
      rw [hkey]
      simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    -- term B, priced by `mulG_close`
    have hmulErr : (fun i => Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i
            * Real.PolyZonotope.point (nominal S) b i
          - Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
              (fun k => b (Fin.cast hR k)) i)
        ∈ (PolyZonotope.generatorError (PolyZonotope.mulGDiff R S)).construct := by
      have key := PolyZonotope.mem_generatorError_monomial (E := PolyZonotope.mulE R S hR)
        (a := fun k => b (Fin.cast hR k)) (PolyZonotope.mulG_close R S)
        (fun k => hb (Fin.cast hR k))
      -- the gap is the generator-level bound, aggregated by the shared monomials
      have heq : (fun i => Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i
            * Real.PolyZonotope.point (nominal S) b i
          - Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
              (fun k => b (Fin.cast hR k)) i)
          = fun i => ∑ l, (Real.PolyZonotope.mulG (nominal R) (nominal S) l i
              - toReal (PolyZonotope.mulGDown R S i l))
            * Real.PolyZonotope.monomial (PolyZonotope.mulE R S hR)
                (fun k => b (Fin.cast hR k)) l := by
        funext i
        rw [show (Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i
              * Real.PolyZonotope.point (nominal S) b i) = _ from congrFun hRSexact i,
          show Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
              (fun k => b (Fin.cast hR k)) i = _ from congrFun hmulPoint i]
        simp only [sub_mul]
        rw [Finset.sum_sub_distrib]
        rfl
      rwa [heq]
    -- term A: `R`'s own gap, times a bound on `nominal S`
    have hRerrBound : ∀ i, |X.point (fun k => b (Fin.cast hXS k)) i
          - Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i|
        ≤ toReal (PolyZonotope.errorBound R.err i) :=
      fun i => PolyZonotope.abs_le_errorBound ih i
    have hSbound : ∀ i, |Real.PolyZonotope.point (nominal S) b i|
        ≤ toReal (PolyZonotope.evalPolyBoundS S i) :=
      PolyZonotope.aux_point_le_boundS S b hb
    have htermAbound : ∀ i, |(X.point (fun k => b (Fin.cast hXS k)) i
          - Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i)
          * Real.PolyZonotope.point (nominal S) b i|
        ≤ toReal (mulUp (PolyZonotope.errorBound R.err i) (PolyZonotope.evalPolyBoundS S i)) := by
      intro i
      rw [abs_mul]
      exact le_trans (mul_le_mul (hRerrBound i) (hSbound i) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hRerrBound i))) (mul_le_mulUp _ _)
    -- the same bound, packaged as membership in the symmetric box
    have htermAmem : (fun i => (X.point (fun k => b (Fin.cast hXS k)) i
          - Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i)
          * Real.PolyZonotope.point (nominal S) b i)
        ∈ (Interval.symmetric (fun i => mulUp (PolyZonotope.errorBound R.err i)
            (PolyZonotope.evalPolyBoundS S i))).construct := by
      intro i
      have habs := htermAbound i
      rw [abs_le] at habs
      exact ⟨by
          show toReal (neg (mulUp (PolyZonotope.errorBound R.err i)
              (PolyZonotope.evalPolyBoundS S i))) ≤ _
          rw [toReal_neg]; exact habs.1,
        habs.2⟩
    -- term residual: `a₀`'s centre shift, priced by `Interval.sub_mem_residual`
    have hresidualMem : (fun i => toReal (a0 i)
          - toReal (FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i)))
        ∈ (PolyZonotope.centerResidual (PolyZonotope.mul R S hR).c a0).construct := by
      have := Interval.sub_mem_residual
        (lo := fun i => FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i))
        (hi := fun i => FloatOps.addUp ((PolyZonotope.mul R S hR).c i) (a0 i))
        (stored := fun i => FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i))
        (x := fun i => toReal ((PolyZonotope.mul R S hR).c i) + toReal (a0 i))
        (fun i => ⟨addDown_le_add _ _, add_le_addUp _ _⟩)
      simpa [PolyZonotope.centerResidual, congrFun hRmulC, toReal_zero, zero_add] using this
    -- the three pieces combine through `Interval.plus`
    rw [hXstep, hnomstep]
    show (fun i => toReal (a0 i) + X.point (fun k => b (Fin.cast hXS k)) i
          * Real.PolyZonotope.point (nominal S) b i
        - (toReal (FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i))
            + Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
                (fun k => b (Fin.cast hR k)) i))
      ∈ (PolyZonotope.evalPolyStep R S hR a0).err.construct
    -- regroup as (mul's rounding) + (centre residual) + (`R`'s own propagated gap)
    have hsplit : (fun i => toReal (a0 i) + X.point (fun k => b (Fin.cast hXS k)) i
          * Real.PolyZonotope.point (nominal S) b i
        - (toReal (FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i))
            + Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
                (fun k => b (Fin.cast hR k)) i))
        = ((fun i => Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i
              * Real.PolyZonotope.point (nominal S) b i
            - Real.PolyZonotope.point (nominal (PolyZonotope.mul R S hR))
                (fun k => b (Fin.cast hR k)) i)
          + (fun i => toReal (a0 i)
              - toReal (FloatOps.addDown ((PolyZonotope.mul R S hR).c i) (a0 i)))
          + (fun i => (X.point (fun k => b (Fin.cast hXS k)) i
              - Real.PolyZonotope.point (nominal R) (fun k => b (Fin.cast hR k)) i)
              * Real.PolyZonotope.point (nominal S) b i) : Vec ℝ n) := by
      funext i; simp only [Pi.add_apply]; ring
    rw [hsplit]
    exact Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, hmulErr, _, hresidualMem, rfl⟩,
      _, htermAmem, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

-- the exact statement, read through the refinement: the same image, rounded outward
theorem PolyZonotope.evalPoly_outer (S : PolyZonotope 𝕋 n) (coeffs : List (Vec 𝕋 n)) :
    (fun a : Fin S.p → ℝ => fun i => Real.PolyZonotope.evalPolyReal
        (coeffs.map fun v => toReal (v i))
        (Real.PolyZonotope.point (nominal S) a i)) '' {a | ∀ k, |a k| ≤ 1}
      ⊆ (PolyZonotope.evalPoly S coeffs).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  have hexact := Real.PolyZonotope.evalPoly_exact (nominal S) (coeffs.map toRealVec) a
  -- one coordinate of a list of coefficient vectors is that coordinate's own scalar list
  have hmap : ∀ i : Fin n, ((coeffs.map toRealVec).map fun v => v i)
      = coeffs.map fun v => toReal (v i) := fun _ => List.map_map
  simp only [hmap] at hexact
  have hgap : (fun i => Real.PolyZonotope.evalPolyReal (coeffs.map fun v => toReal (v i))
        (Real.PolyZonotope.point (nominal S) a i)
      - Real.PolyZonotope.point (nominal (PolyZonotope.evalPoly S coeffs))
          (fun k => a (Fin.cast (PolyZonotope.evalPoly_p S coeffs) k)) i)
      ∈ (PolyZonotope.evalPoly S coeffs).err.construct := by
    -- `hexact` rewrites the invariant's exact side into the target's own shape
    intro i
    have hi := congrFun hexact i
    have hmem := PolyZonotope.aux_evalPoly_close S coeffs a ha i
    have h1 : toReal ((PolyZonotope.evalPoly S coeffs).err.inf i)
          ≤ Real.PolyZonotope.evalPolyReal (coeffs.map fun v => toReal (v i))
              (Real.PolyZonotope.point (nominal S) a i)
            - Real.PolyZonotope.point (nominal (PolyZonotope.evalPoly S coeffs))
                (fun k => a (Fin.cast (PolyZonotope.evalPoly_p S coeffs) k)) i := hi ▸ hmem.1
    have h2 : Real.PolyZonotope.evalPolyReal (coeffs.map fun v => toReal (v i))
            (Real.PolyZonotope.point (nominal S) a i)
          - Real.PolyZonotope.point (nominal (PolyZonotope.evalPoly S coeffs))
              (fun k => a (Fin.cast (PolyZonotope.evalPoly_p S coeffs) k)) i
        ≤ toReal ((PolyZonotope.evalPoly S coeffs).err.sup i) := hi ▸ hmem.2
    exact ⟨h1, h2⟩
  -- the witness splits `x` as `nominal(evalPoly).point (cast a)` plus the gap
  refine ⟨Real.PolyZonotope.point (nominal (PolyZonotope.evalPoly S coeffs))
        (fun k => a (Fin.cast (PolyZonotope.evalPoly_p S coeffs) k)),
      PolyZonotope.mem_nominalSet_iff.mpr
        ⟨fun k => a (Fin.cast (PolyZonotope.evalPoly_p S coeffs) k),
        fun _ => (0 : ℝ), fun k => ha _, fun j => by norm_num, fun i => by
        -- `nominal`'s fields read back `evalPoly`'s own, entrywise
        have hYc : (nominal (PolyZonotope.evalPoly S coeffs)).c
            = fun i => toReal ((PolyZonotope.evalPoly S coeffs).c i) := rfl
        have hYG : (nominal (PolyZonotope.evalPoly S coeffs)).G
            = fun l i => toReal ((PolyZonotope.evalPoly S coeffs).G i l) := rfl
        have hYE : (nominal (PolyZonotope.evalPoly S coeffs)).E
            = (PolyZonotope.evalPoly S coeffs).E := rfl
        simp only [Real.PolyZonotope.point, hYc, hYG, hYE, Pi.add_apply, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
        congr 1
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _⟩,
      fun i => Real.PolyZonotope.evalPolyReal (coeffs.map fun v => toReal (v i))
          (Real.PolyZonotope.point (nominal S) a i)
        - Real.PolyZonotope.point (nominal (PolyZonotope.evalPoly S coeffs))
            (fun k => a (Fin.cast (PolyZonotope.evalPoly_p S coeffs) k)) i,
      hgap, by funext i; simp only [Pi.add_apply]; ring⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
