module

public import CORALean.HybridDynamics.Operations.HitHessianMatZono
public import CORALean.HybridDynamics.Operations.HitHessianMatZonoFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# The float matrix zonotope holds `Q⁽ⁱ⁾` at the center's factors

For `|κ| ≤ 1`, the point `C̃⁽ⁱ⁾ + κG̃^(i,1)` of the exact layer's matrix zonotope
(`GuardMap.hitHessianMatZono`, at the floats read as reals, `ψ_c = −n − τ_cΥᵀ` and
`ψ_g = −τ_gΥᵀ`) is the float one's point at the same factors, `(κ, 0, 0)`, plus a point `E` of
its error box: the factors `(κ, 0, 0)` are those of the center `c_x` of `R(0)`
(`GuardMap.hitHessianNum_eq_hitHessianMatZono`), the only point the guard mapping needs.

Each printed formula is a product and sum of row and column matrices, so `C̃⁽ⁱ⁾` and
`G̃^(i,1)` lie in the float interval matrices (`matMul_outer`, `matPlus_outer`, `smul_outer`,
`mem_point`) once read as those products, an identity checked entry by entry; then
`E = (C̃ − C̲) + κ(G̃ − G̲)` lies in `[−(Ḡ − G̲), (C̄ − C̲) + (Ḡ − G̲)]`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `C + κG = C̲ + E + κG̲` with `E` in `[−(Ḡ − G̲), (C̄ − C̲) + (Ḡ − G̲)]`, for `C`, `G` in their
interval matrices and `|κ| ≤ 1`. -/
theorem aux_hessF_box (C G : Interval (Mat 𝕋 n n)) {Cr Gr : Mat ℝ n n} (hC : Cr ∈ C.construct)
    (hG : Gr ∈ G.construct) {κ : ℝ} (hκ : |κ| ≤ 1) :
    ∃ E ∈ (⟨fun l m => neg (subUp (G.sup l m) (G.inf l m)),
        fun l m => addUp (subUp (C.sup l m) (C.inf l m)) (subUp (G.sup l m) (G.inf l m))⟩ :
          Interval (Mat 𝕋 n n)).construct,
      Cr + κ • Gr = (toRealMat C.inf + E) + κ • toRealMat G.inf := by -- --- PROOF ---
  refine ⟨Cr - toRealMat C.inf + κ • (Gr - toRealMat G.inf), Interval.mem_mat_iff.mpr
    fun l m => ?_, by module⟩
  have hc := Interval.mem_mat_iff.mp hC l m
  have hg := Interval.mem_mat_iff.mp hG l m
  have h1 := sub_le_subUp (C.sup l m) (C.inf l m)
  have h2 := sub_le_subUp (G.sup l m) (G.inf l m)
  have h3 := add_le_addUp (subUp (C.sup l m) (C.inf l m)) (subUp (G.sup l m) (G.inf l m))
  -- `|κ(G − G̲)| ≤ Ḡ − G̲`
  have hk : |κ * (Gr l m - toReal (G.inf l m))| ≤ toReal (subUp (G.sup l m) (G.inf l m)) := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hg.1)]
    exact (mul_le_of_le_one_left (sub_nonneg.mpr hg.1) hκ).trans (by linarith [hg.2])
  have hk' := abs_le.mp hk
  show toReal (neg _) ≤ _ ∧ _ ≤ toReal _
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, toReal_neg,
    toRealMat]
  constructor <;> linarith [hc.1, hc.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3] at floats: the exact matrix zonotope's point at `(κ, 0, 0)` is the float one's
plus a point of its error box. -/
theorem GuardMap.hitHessianMatZonoFloat_mem (A : Mat 𝕋 n n) (b nv : Vec 𝕋 n) (d : 𝕋)
    (R₀ : Zonotope (Vec 𝕋 n)) (τc τg : 𝕋) (i : Fin n) {κ : ℝ} (hκ : |κ| ≤ 1) :
    ∃ E ∈ (GuardMap.hitHessianMatZonoFloat A b nv d R₀ τc τg i).I_error.construct,
      (GuardMap.hitHessianMatZono (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d)
          (⟨R₀.h, toRealVec R₀.c, fun j => toRealVec (R₀.G j)⟩ : Real.Zonotope (Vec ℝ n))
          (-toRealVec nv - toReal τc • (toRealVec nv ᵥ* toRealMat A))
          (-(toReal τg • (toRealVec nv ᵥ* toRealMat A))) i).c
        + ∑ j : Fin (1 + R₀.h + R₀.h),
          (Fin.append (Fin.append ![κ] (0 : Fin R₀.h → ℝ)) fun α => κ * (0 : Fin R₀.h → ℝ) α) j
          • (GuardMap.hitHessianMatZono (toRealMat A) (toRealVec b) (toRealVec nv) (toReal d)
          (⟨R₀.h, toRealVec R₀.c, fun j => toRealVec (R₀.G j)⟩ : Real.Zonotope (Vec ℝ n))
          (-toRealVec nv - toReal τc • (toRealVec nv ᵥ* toRealMat A))
          (-(toReal τg • (toRealVec nv ᵥ* toRealMat A))) i).G j
      = (toRealMat (GuardMap.hitHessianMatZonoFloat A b nv d R₀ τc τg i).c + E)
        + ∑ j : Fin (1 + R₀.h + R₀.h),
          (Fin.append (Fin.append ![κ] (0 : Fin R₀.h → ℝ)) fun α => κ * (0 : Fin R₀.h → ℝ) α) j
          • toRealMat ((GuardMap.hitHessianMatZonoFloat A b nv d R₀ τc τg i).G
            j) := by -- --- PROOF ---
  set Ar := toRealMat A with hAr
  set nr := toRealVec nv with hnr
  set cr := toRealVec R₀.c with hcr
  set br := toRealVec b with hbr
  -- the real rows and columns the float points read as
  set rowR : Vec ℝ n → Mat ℝ 1 n := fun v => Matrix.of fun _ m => v m with hrowR
  set colR : Vec ℝ n → Mat ℝ n 1 := fun v => Matrix.of fun l _ => v l with hcolR
  -- the scalars `−1` and `−2` in their brackets
  have hn1 : toReal (neg (one : 𝕋)) = -1 := by rw [toReal_neg, toReal_one]
  have h2lo : toReal (neg (addUp (one : 𝕋) one)) ≤ -2 := by
    have := add_le_addUp (one : 𝕋) one
    rw [toReal_one] at this
    rw [toReal_neg]
    linarith
  have h2hi : -2 ≤ toReal (neg (addDown (one : 𝕋) one)) := by
    have := addDown_le_add (one : 𝕋) one
    rw [toReal_one] at this
    rw [toReal_neg]
    linarith
  -- each formula's real matrix lies in its float interval matrix
  have pt : ∀ {p q : ℕ} (M : Mat 𝕋 p q), toRealMat M ∈ (Interval.point M).construct :=
    fun M => Interval.mem_point M
  have ptr : ∀ v : Vec 𝕋 n, rowR (toRealVec v) ∈
      (Interval.point (show Mat 𝕋 1 n from fun _ m => v m)).construct := fun v => pt _
  have ptc : ∀ v : Vec 𝕋 n, colR (toRealVec v) ∈
      (Interval.point (show Mat 𝕋 n 1 from fun l _ => v l)).construct := fun v => pt _
  have hΥ := Interval.matMul_outer _ _ (ptr nv) (pt A)
  have hΥT := Interval.matMul_outer _ _ (pt (show Mat 𝕋 n n from fun l j => A j l)) (ptc nv)
  have hy := Interval.matPlus_outer _ _ (Interval.matMul_outer _ _ (pt A) (ptc R₀.c))
    (ptc b)
  have hΛ := Interval.matMul_outer _ _ (ptr nv) hy
  have hnum := Interval.matPlus_outer _ _ (pt (show Mat 𝕋 1 1 from fun _ _ => d))
    (Interval.smul_outer hn1.le hn1.ge _ (Interval.matMul_outer _ _ (ptr nv) (ptc R₀.c)))
  have hΘc := Interval.matPlus_outer _ _
    (Interval.smul_outer hn1.le hn1.ge _ (Interval.matMul_outer _ _ hΛ (ptr nv)))
    (Interval.smul_outer hn1.le hn1.ge _ (Interval.matMul_outer _ _ hnum hΥ))
  have hΘcT := Interval.matPlus_outer _ _
    (Interval.smul_outer hn1.le hn1.ge _ (Interval.matMul_outer _ _ (ptc nv) hΛ))
    (Interval.smul_outer hn1.le hn1.ge _ (Interval.matMul_outer _ _ hΥT hnum))
  -- `ψ`, `Ω`, `S`, then `C̃⁽ⁱ⁾` and `G̃^(i,1)`
  have hψc := Interval.matPlus_outer _ _ (Interval.smul_outer hn1.le hn1.ge _ (ptc nv))
    (Interval.smul_outer (toReal_neg τc).le (toReal_neg τc).ge _ hΥT)
  have hψg := Interval.smul_outer (toReal_neg τg).le (toReal_neg τg).ge _ hΥT
  have hΩ := Interval.matPlus_outer _ _
    (Interval.smul_outer hn1.le hn1.ge _ (Interval.matMul_outer _ _ (ptc nv) hΥ))
    (Interval.matMul_outer _ _ hΥT (ptr nv))
  have hS := Interval.matPlus_outer _ _ hΩ
    (Interval.smul_outer h2lo h2hi _ (Interval.matMul_outer _ _ hψc hΥ))
  have hyi := Interval.mem_mat_iff.mp hy i 0
  have hC := Interval.matPlus_outer _ _ (Interval.matPlus_outer _ _
      (Interval.matMul_outer _ _ (ptc (A i)) hΘc)
      (Interval.matMul_outer _ _ hΘcT (ptr (A i))))
    (Interval.smul_outer hyi.1 hyi.2 _ hS)
  have hG1 := Interval.smul_outer hyi.1 hyi.2 _
    (Interval.smul_outer h2lo h2hi _ (Interval.matMul_outer _ _ hψg hΥ))
  -- the sums keep only the first generator, at `κ`
  have hsum : ∀ X : Fin (1 + R₀.h + R₀.h) → Mat ℝ n n, ∑ j : Fin (1 + R₀.h + R₀.h),
      (Fin.append (Fin.append ![κ] (0 : Fin R₀.h → ℝ)) fun α => κ * (0 : Fin R₀.h → ℝ) α) j
        • X j = κ • X (Fin.castAdd R₀.h (Fin.castAdd R₀.h 0)) := fun X => by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  obtain ⟨E, hE, heq⟩ := aux_hessF_box _ _ hC hG1 hκ
  refine ⟨E, hE, ?_⟩
  rw [hsum, hsum]
  refine Eq.trans ?_ (heq.trans ?_)
  -- `Υᵀ = Aᵀn` is `Υ = nᵀA` read down a column
  have hT : ∀ l, ∑ x, toRealMat (show Mat 𝕋 n n from fun l j => A j l) l x * toRealVec nv x
      = ∑ x, toRealVec nv x * toRealMat A x l := fun l =>
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hAi : ∀ l, toRealVec (A i) l = toRealMat A i l := fun _ => rfl
  have hd : toRealMat (show Mat 𝕋 1 1 from fun _ _ => d) 0 0 = toReal d := rfl
  · -- the exact `C̃⁽ⁱ⁾` and `G̃^(i,1)`, read as the products, entry by entry
    congr 1
    · ext l m
      simp [GuardMap.hitHessianMatZono, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul,
        dotProduct, rowR, colR, Ar, nr, cr, br, Matrix.vecMulVec_apply, hT, hAi, hd]
      ring
    · congr 1
      simp only [GuardMap.hitHessianMatZono, Fin.append_left, Matrix.cons_val_zero]
      ext l m
      simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, rowR, colR, Ar, nr, cr,
        br, hT]
      ring
  · -- the float center and first generator are the lower ends
    dsimp only [GuardMap.hitHessianMatZonoFloat]
    rw [Fin.append_left, Fin.append_left, Matrix.cons_val_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
