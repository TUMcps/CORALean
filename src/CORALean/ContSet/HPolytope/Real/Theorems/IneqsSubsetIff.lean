module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert
public import CORALean.Global.LinProg.Farkas

@[expose] public section

/-!
# H-polytope in H-polytope, as a linear program

`[1, Lemma 1]`: `{Hx x ≤ hx} ⊆ {Hy x ≤ hy}` iff some `Λ ≥ 0` has `Λ Hx = Hy` and
`Λ hx ≤ hy`. "If" is weak duality (`mem_ineqs_of_cert` at `Γ = I`, `β = 0`); "only if" is
Farkas' lemma, one row of `Hy` at a time, and needs the inbody nonempty, which the printed
statement omits: `∅` lies in every set, and is not always cut out by rows that assemble
`Hy` (`ineqs_subset_iff_counterexample`).

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {qx qy n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.ineqs_subset_iff {Hx : Mat ℝ qx n} {hx : Vec ℝ qx} {Hy : Mat ℝ qy n}
    {hy : Vec ℝ qy} (hne : (HPolytope.ineqs Hx hx).construct.Nonempty) :
    (HPolytope.ineqs Hx hx).construct ⊆ (HPolytope.ineqs Hy hy).construct ↔
      ∃ Λ : Mat ℝ qy qx, (∀ i j, 0 ≤ Λ i j) ∧ Λ * Hx = Hy ∧ Λ *ᵥ hx ≤ hy := by -- --- PROOF ---
  have hrl : ∀ {q : ℕ} (M : Mat ℝ q n) i x, HPolytope.rowLin M i x = (M *ᵥ x) i :=
    fun _ _ _ => rfl
  constructor
  -- Farkas, row by row of `Hy`
  · intro hsub
    obtain ⟨x0, hx0⟩ := hne
    have hrow : ∀ i, ∃ y : Fin qx → ℝ, (∀ j, 0 ≤ y j) ∧
        HPolytope.rowLin Hy i = ∑ j, y j • HPolytope.rowLin Hx j ∧ ∑ j, y j * hx j ≤ hy i :=
      fun i => exists_dual_of_forall_le (HPolytope.rowLin Hx) hx (HPolytope.rowLin Hy i) (hy i)
        ⟨x0, HPolytope.mem_ineqs_iff.mp hx0⟩
        (fun x hx' => HPolytope.mem_ineqs_iff.mp (hsub (HPolytope.mem_ineqs_iff.mpr hx')) i)
    choose y hy0 hyc hyb using hrow
    refine ⟨Matrix.of y, fun i j => hy0 i j, ?_, fun i => ?_⟩
    · ext i k
      have h := congrArg (fun f : Vec ℝ n →ₗ[ℝ] ℝ => f (Pi.single k 1)) (hyc i)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hrl,
        mulVec_single_one] at h
      rw [Matrix.mul_apply]
      simpa [Matrix.col_apply, Matrix.of_apply] using h.symm
    · simpa [mulVec, dotProduct] using hyb i
  -- weak duality: the certificate at `Γ = I`, `β = 0`
  · rintro ⟨Λ, hΛ, h1, h2⟩ x hx'
    have h := HPolytope.mem_ineqs_of_cert (Γ := 1) (β := 0) hΛ (by rw [h1, Matrix.mul_one])
      (by simpa using h2) hx'
    simpa using h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
