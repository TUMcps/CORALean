module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTail
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The exact tail orders lie in the float ones

`inputTaylorSumTail` taken at plain sets — images and Minkowski sums, exactly — at `U`'s
`construct`: each order's matrix `Aⁱ r^{i+1}/(i+1)!` is in its float box
(`smul_pow_mem_intervalInputTerm`), so its image is in the float product, and `⊞` holds the
sum; the zero matrix below order `1` is in the point `0`. [1, Alg. 2] line 16's set.

## Inputs
* `sys` – linear system
* `r` – float step length
* `U` – input float zonotope

## Hypotheses
* `hr` – step length nonnegative

## Conclusion
* the exact tail lies in the float tail

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix ContSet Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_setPlusTail (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩

/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_setMtimesTail : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

attribute [local instance] aux_setPlusTail aux_setMtimesTail


-- =======================================  MAIN THEOREM  ======================================= --

/-- At `r ≥ 0`, every order count `i`: the exact tail at plain sets is in the float tail. -/
theorem LinearSys.inputTaylorSumTail_subset_float (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) (U : Zonotope (Vec 𝕋 n)) : ∀ i,
    construct (sys.inputTaylorSumTail (S := 𝒮) (toReal r) U.construct i)
      ⊆ (sys.inputTaylorSumTailFloat r U i).construct := by -- --- PROOF ---
  -- a matrix in a float box maps `U` into the float product
  have hprod : ∀ {B : Interval (Mat 𝕋 n n)} {M : Mat ℝ n n}, M ∈ B.construct →
      (M *ᵥ ·) '' U.construct
        ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) B U) :=
    fun {B} {_} hM => (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' U.construct) hM).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) B U)
  have hterm : ∀ i, (sys.inputTerm (toReal r) i *ᵥ ·) '' U.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) U) :=
    fun i => hprod (MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i)
  -- the tail, term by term, by strong induction on the order
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ =>
      exact hprod (Interval.mem_mat_iff.mpr fun _ _ => by simp [Interval.point, toReal_zero])
    | 1, _ => exact hterm 1
    | i + 2, ih =>
      exact (Set.add_subset_add (ih (i + 1) (by omega)) (hterm (i + 2))).trans
        (Plus.plus_outer (sys.inputTaylorSumTailFloat r U (i + 1)) _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
