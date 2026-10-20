module

public import CORALean.ContSet.Ellipsoid.Float.Operations.CartProdVec
public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Ellipsoid.Real.Theorems.CartProdVecExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic

@[expose] public section

/-!
# `Ellipsoid.cartProdVec` is the product with a point, exactly

The nominal ellipsoid is the exact layer's `cartProdVec` of the nominal one: `blkdiag(Q, 0)` is
positive semi-definite exactly when `Q` is, being `P Q Pᵀ` for the embedding `P` and having `Q`
as a principal block, so both refuse the same `Q`, and `Real.Ellipsoid.cartProdVec_exact` appends
the point. The error box is the original's with a zero-width box on the appended coordinates, so
a point of it is a point of the original's with nothing added there.

## Inputs
* `E` – ellipsoid
* `v` – point

## Hypotheses
* none

## Conclusion
* the result is exactly the product of `E` with `v`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.cartProdVec_exact (E : Ellipsoid 𝕋 n) (v : Vec 𝕋 m) : -- --- CONCL ---
    (E.cartProdVec v).construct =
      (fun x : Vec ℝ n => (Fin.append x (toRealVec v) : Vec ℝ (n + m))) ''
        E.construct := by -- --- PROOF ---
  -- the nominal ellipsoid is the exact layer's product
  set B : Mat ℝ (n + m) (n + m) := toRealMat (E.cartProdVec v).Q with hB
  set P : Mat ℝ (n + m) n := Matrix.of fun i j => Fin.addCases (fun i => if i = j then 1 else 0)
    (fun _ => 0) i with hP
  -- `P A Pᵀ` is `A` padded with zeros
  have hPAP : ∀ A : Mat ℝ n n, P * A * Pᵀ = Matrix.of fun i j =>
      Fin.addCases (fun i => Fin.addCases (fun j => A i j) (fun _ => 0) j) (fun _ => 0) i := by
    intro A
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [hP, Matrix.mul_apply]
  -- the stored product's shape is `P Q Pᵀ`
  have hBeq : B = P * toRealMat E.Q * Pᵀ := by
    rw [hPAP]
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [hB, toRealMat, Ellipsoid.cartProdVec, toReal_zero]
  -- positive semi-definite exactly when `Q` is
  have hiff : B.PosSemidef ↔ (toRealMat E.Q).PosSemidef := by
    constructor
    · intro h
      have := h.submatrix (Fin.castAdd m)
      convert this using 1
      ext i j
      simp [hB, toRealMat, Ellipsoid.cartProdVec]
    · intro h
      rw [hBeq]
      simpa [conjTranspose_eq_transpose_of_trivial] using h.mul_mul_conjTranspose_same P
  -- so the nominal ellipsoids agree, in both cases of `ofShape`
  have hN : (nominal (E.cartProdVec v)).ellipsoid
      = (nominal E).ellipsoid.cartProdVec (toRealVec v) := by
    refine Real.Ellipsoid.ext ?_ ?_
    · show (nominal (E.cartProdVec v)).ellipsoid.Q = P * (nominal E).ellipsoid.Q * Pᵀ
      rw [Ellipsoid.nominal_Q_eq, Ellipsoid.nominal_Q_eq]
      by_cases h : (toRealMat E.Q).PosSemidef
      · rw [if_pos (hiff.2 h), if_pos h, ← hBeq]
      · rw [if_neg (mt hiff.1 h), if_neg h, Matrix.mul_zero, Matrix.zero_mul]
    · show (nominal (E.cartProdVec v)).ellipsoid.q
        = Fin.append (nominal E).ellipsoid.q (toRealVec v)
      rw [Ellipsoid.nominal_q, Ellipsoid.nominal_q]
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [toRealVec, Ellipsoid.cartProdVec]
  have hNs : nominalSet (E.cartProdVec v)
      = (fun x : Vec ℝ n => (Fin.append x (toRealVec v) : Vec ℝ (n + m))) '' nominalSet E := by
    show (nominal (E.cartProdVec v)).ellipsoid.construct = _ '' (nominal E).ellipsoid.construct
    rw [hN]
    exact Real.Ellipsoid.cartProdVec_exact _ _
  -- the error box: the original's on the first coordinates, zero on the rest
  have hI : ∀ e : Vec ℝ (n + m), e ∈ (E.cartProdVec v).I_error.construct ↔
      (fun i => e (Fin.castAdd m i)) ∈ E.I_error.construct ∧ ∀ i, e (Fin.natAdd n i) = 0 := by
    intro e
    rw [Interval.mem_vec_iff, Interval.mem_vec_iff]
    constructor
    · intro he
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have h := he (Fin.castAdd m i)
        simpa [Ellipsoid.cartProdVec] using h
      · have h := he (Fin.natAdd n i)
        simp only [Ellipsoid.cartProdVec, Fin.append_right, toReal_zero] at h
        exact le_antisymm h.2 h.1
    · rintro ⟨h₁, h₂⟩ i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [Ellipsoid.cartProdVec] using h₁ i
      · simp only [Ellipsoid.cartProdVec, Fin.append_right, toReal_zero, h₂ i]
        exact ⟨le_rfl, le_rfl⟩
  -- the two sums, the padding moved between the summands
  show nominalSet (E.cartProdVec v) + (E.cartProdVec v).I_error.construct = _
  rw [hNs]
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, e, he, rfl⟩
    obtain ⟨he₁, he₂⟩ := (hI e).1 he
    refine ⟨y + fun i => e (Fin.castAdd m i), ⟨y, hy, _, he₁, rfl⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp
    · simp [he₂ i]
  · rintro ⟨_, ⟨y, hy, e, he, rfl⟩, rfl⟩
    refine ⟨Fin.append y (toRealVec v), ⟨y, hy, rfl⟩, Fin.append e 0,
      (hI _).2 ⟨?_, fun i => ?_⟩, ?_⟩
    · simp only [Fin.append_left]
      exact he
    · simp
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
