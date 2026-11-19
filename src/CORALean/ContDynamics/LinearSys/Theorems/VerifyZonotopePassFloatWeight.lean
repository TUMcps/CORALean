module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonotopePassFloat
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.CarryMinFloatSound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.LyapunovCertificateFloatSound
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.QuadExpLeWeighted

@[expose] public section

/-!
# The weighted carry of `LinearSys.verifyZonotopePassFloat` is sound

With an accepted Lyapunov weight `P` of `A` (`Krylov.lyapunovCertificateFloat_sound`: `a x'x ≤
x'Px ≤ b x'x`, `x'PAx ≤ μ x'Px`), the gauge `ν(x) = √(x'Px)` grows by at most `e^{μΔt}` under
`e^{AΔt}` (`Krylov.quad_exp_le_weighted`) and is subadditive. A carried error `e^{AΔt} ε + δ`, with
`ν(ε) ≤ β x` and `|δᵢ| ≤ ℓ x sᵢ`, then has `ν ≤ (e^{μΔt} β + √b √n max s ℓ) x = β' x`, and every
entry is at most `ν/√a ≤ β' x (1/(√a min s)) sᵢ`. So the smaller of this and the Gershgorin bound
holds, for the carried zonotope (`x = 1`) and for `Φ` (`x = a` of the scaled input).

## Inputs
* `A` – float system matrix
* `P` – float weight
* `L` – float factor of `P - aI`
* `a₀` – float shift
* `s` – positive float scales
* `Δt` – float step length
* `loc` – the step's local errors in the scales
* `st` – float state at `t`
* `st₁` – float state at `t + Δt` with the Gershgorin carry

## Hypotheses
* `hok` – the weight is accepted
* `hs` – the scales are positive
* `hΔt` – the step is nonnegative
* `hcap` – `μΔt` is in the range of the exponential
* `hβ0`, `hψ0` – the weighted bounds at `t` are nonnegative
* `hl1`, `hl2` – the local errors are nonnegative
* `hh1`, `hφ1` – the Gershgorin bounds are nonnegative

## Conclusion
* the weighted state keeps the other fields, its bounds are nonnegative, and for the zonotope and
  for `Φ` the carried error is within both its weighted bound and its smaller scaled bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Cauchy–Schwarz for a symmetric positive semidefinite weight. -/
private theorem LinearSys.aux_cs_weighted (P : Mat ℝ n n) (hS : Pᵀ = P)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (P *ᵥ x)) (u v : Vec ℝ n) : -- --- CONCL ---
    (u ⬝ᵥ (P *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (P *ᵥ u)) * (v ⬝ᵥ (P *ᵥ v)) := by -- --- PROOF ---
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := fun u v => by
    rw [dotProduct_comm, ← vecMul_transpose, hS, ← dotProduct_mulVec]
  have h := discrim_le_zero (a := v ⬝ᵥ (P *ᵥ v)) (b := 2 * (u ⬝ᵥ (P *ᵥ v))) (c := u ⬝ᵥ (P *ᵥ u))
    fun s => by
      have := hpsd (u + s • v)
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
      rw [hsym v u] at this
      nlinarith [this]
  unfold discrim at h
  nlinarith [h]

/-- The weighted gauge is subadditive. -/
private theorem LinearSys.aux_gauge_add_le (P : Mat ℝ n n) (hS : Pᵀ = P)
    (hpsd : ∀ x, 0 ≤ x ⬝ᵥ (P *ᵥ x)) (x y : Vec ℝ n) : -- --- CONCL ---
    Real.sqrt ((x + y) ⬝ᵥ (P *ᵥ (x + y))) ≤
      Real.sqrt (x ⬝ᵥ (P *ᵥ x)) + Real.sqrt (y ⬝ᵥ (P *ᵥ y)) := by -- --- PROOF ---
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := fun u v => by
    rw [dotProduct_comm, ← vecMul_transpose, hS, ← dotProduct_mulVec]
  have hcs := LinearSys.aux_cs_weighted P hS hpsd x y
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have hx := Real.sq_sqrt (hpsd x)
  have hy := Real.sq_sqrt (hpsd y)
  have hxy : x ⬝ᵥ (P *ᵥ y) ≤ Real.sqrt (x ⬝ᵥ (P *ᵥ x)) * Real.sqrt (y ⬝ᵥ (P *ᵥ y)) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, hx, hy]; exact hcs
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [hsym y x]
  nlinarith [hxy, hx, hy]

/-- `σ` doublings from one stay below `2^σ`. -/
private theorem LinearSys.aux_doublings_le (σ : ℕ) : -- --- CONCL ---
    toReal ((fun x : 𝕋 => addDown x x)^[σ] FloatOps.one) ≤ 2 ^ σ := by -- --- PROOF ---
  induction σ with
  | zero => simp [toReal_one]
  | succ σ ih =>
    rw [Function.iterate_succ_apply']
    refine le_trans (addDown_le_add _ _) ?_
    rw [pow_succ]
    linarith

/-- The real step: with `ν(e^{AΔt} x) ≤ g ν(x)`, `ν(x) ≤ K d` for `|xᵢ| ≤ d sᵢ` and `|xᵢ| ≤ ν(x) B
sᵢ`, the carried error `e^{AΔt} ε + δ` is within `β' x` in the gauge and `β' B x` in the scales. -/
private theorem LinearSys.aux_core (ν : Vec ℝ n → ℝ) (E : Mat ℝ n n) (s : Vec ℝ n)
    (hs : ∀ i, 0 < s i) (hadd : ∀ x y, ν (x + y) ≤ ν x + ν y) (g : ℝ)
    (hE : ∀ x, ν (E *ᵥ x) ≤ g * ν x) (K : ℝ)
    (hK : ∀ (d : ℝ) (x : Vec ℝ n), 0 ≤ d → (∀ i, |x i| ≤ d * s i) → ν x ≤ K * d)
    (B : ℝ) (hB : ∀ x i, |x i| ≤ ν x * B * s i) (hg : 0 ≤ g) (hB0 : 0 ≤ B)
    (β ℓ β' x : ℝ) (hℓ : 0 ≤ ℓ) (hx : 0 ≤ x) (hβ' : g * β + K * ℓ ≤ β') (ε δ : Vec ℝ n)
    (hε : ν ε ≤ β * x) (hδ : ∀ i, |δ i| ≤ ℓ * x * s i) : -- --- CONCL ---
    ν (E *ᵥ ε + δ) ≤ β' * x ∧ ∀ i, |(E *ᵥ ε + δ) i| ≤ β' * B * x * s i := by -- --- PROOF ---
  -- the gauge of the sum, then each entry through it
  have hδK := hK (ℓ * x) δ (mul_nonneg hℓ hx) hδ
  have h1 : ν (E *ᵥ ε + δ) ≤ β' * x := by
    refine (hadd _ _).trans ((add_le_add ((hE ε).trans (mul_le_mul_of_nonneg_left hε hg))
      hδK).trans ?_)
    have := mul_le_mul_of_nonneg_right hβ' hx
    nlinarith
  refine ⟨h1, fun i => (hB _ i).trans ?_⟩
  have hBs : 0 ≤ B * s i := mul_nonneg hB0 (hs i).le
  have := mul_le_mul_of_nonneg_right h1 hBs
  nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

set_option maxHeartbeats 1000000 in -- the weighted state is unfolded with its `let`s
/-- With an accepted weight of `A`: the weighted state keeps all but `h`, `φ`, `β`, `ψ`; its bounds
are nonnegative; a carried error `e^{AΔt} ε + δ` of the zonotope (`ν(ε) ≤ β x`, `|δᵢ| ≤ loc₁ x
sᵢ`) within the Gershgorin `h₁ x sᵢ` is within `β' x` and `h' x sᵢ`, and the same for `Φ`. -/
theorem LinearSys.verifyZonotopePassFloat_weight (A P L : Mat 𝕋 n n) (a₀ : 𝕋)
    {c : Krylov.LyapunovCertificateFloat 𝕋} (hc : c = Krylov.lyapunovCertificateFloat A P L a₀)
    (hok : c.ok = true) {s : Vec 𝕋 n} (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 ≤ toReal Δt)
    (hcap : le (mulUp c.rate Δt) ((fun x => addDown x x)^[29] FloatOps.one) = true)
    (loc : 𝕋 × 𝕋) (st st₁ : LinearSys.VerifyZonoState 𝕋 n m)
    (hβ0 : 0 ≤ toReal st.β) (hψ0 : 0 ≤ toReal st.ψ) (hl1 : 0 ≤ toReal loc.1)
    (hl2 : 0 ≤ toReal loc.2) (hh1 : 0 ≤ toReal st₁.h) (hφ1 : 0 ≤ toReal st₁.φ) : -- --- CONCL ---
    let st' := LinearSys.step_verifyZonoWeightFloat c s Δt loc st st₁
    let ν := fun x : Vec ℝ n => Real.sqrt (x ⬝ᵥ (toRealMat P *ᵥ x))
    let E := exp (toReal Δt • toRealMat A)
    st'.c = st₁.c ∧ st'.G = st₁.G ∧ st'.Φ = st₁.Φ ∧ st'.P = st₁.P ∧ st'.b = st₁.b ∧
    st'.ρ = st₁.ρ ∧ 0 ≤ toReal st'.h ∧ 0 ≤ toReal st'.φ ∧ 0 ≤ toReal st'.β ∧
    0 ≤ toReal st'.ψ ∧
    (∀ (x : ℝ) (ε δ : Vec ℝ n), 0 ≤ x → ν ε ≤ toReal st.β * x →
      (∀ i, |δ i| ≤ toReal loc.1 * x * toReal (s i)) →
      (∀ i, |(E *ᵥ ε + δ) i| ≤ toReal st₁.h * x * toReal (s i)) →
      ν (E *ᵥ ε + δ) ≤ toReal st'.β * x ∧ ∀ i, |(E *ᵥ ε + δ) i| ≤ toReal st'.h * x * toReal (s i)) ∧
    (∀ (x : ℝ) (ε δ : Vec ℝ n), 0 ≤ x → ν ε ≤ toReal st.ψ * x →
      (∀ i, |δ i| ≤ toReal loc.2 * x * toReal (s i)) →
      (∀ i, |(E *ᵥ ε + δ) i| ≤ toReal st₁.φ * x * toReal (s i)) →
      ν (E *ᵥ ε + δ) ≤ toReal st'.ψ * x ∧
        ∀ i, |(E *ᵥ ε + δ) i| ≤ toReal st'.φ * x * toReal (s i)) := by -- --- PROOF ---
  intro st' ν E
  obtain ⟨hS, ha0, hb0, ha, hb, hPA⟩ := Krylov.lyapunovCertificateFloat_sound A P L a₀ (hc ▸ hok)
  rw [← hc] at ha0 hb0 ha hb hPA
  set Pr := toRealMat P with hPr
  set a := toReal c.lower with hadef
  set b := toReal c.upper with hbdef
  have hpsd : ∀ x, 0 ≤ x ⬝ᵥ (Pr *ᵥ x) := fun x => by
    have := ha x
    rw [dotProduct_self] at this
    exact le_trans (by positivity) this
  -- the factors: `g ≥ e^{μΔt}`, `kn ≥ √b √n max s`, `back ≥ 1/(√a min s)`
  set g := expUp 30 (mulUp c.rate Δt) with hg
  set kn₀ := mulUp (sqrtUp 30 c.upper) (sqrtUp 30 (nsmulUp n (FloatOps.one : 𝕋))) with hkn₀
  set kn := mulUp kn₀ (maximumOver s) with hkn
  have hk₀le : toReal (sqrtUp 30 c.upper) * toReal (sqrtUp 30 (nsmulUp n (FloatOps.one : 𝕋)))
      ≤ toReal kn₀ := mul_le_mulUp _ _
  have hkle : toReal kn₀ * toReal (maximumOver s) ≤ toReal kn := mul_le_mulUp _ _
  set back := mulUp (sqrtUp 30 (divUp FloatOps.one c.lower))
    (maximumOver fun i => divUp FloatOps.one (s i)) with hback
  have hexp : Real.exp (toReal c.rate * toReal Δt) ≤ toReal g := by
    have h1 := toReal_le_of_le hcap
    have hcapR : toReal (mulUp c.rate Δt) ≤ 2 ^ 30 / 2 :=
      h1.trans ((LinearSys.aux_doublings_le 29).trans (by norm_num))
    exact (Real.exp_le_exp.2 (mul_le_mulUp c.rate Δt)).trans (le_expUp 30 _ hcapR)
  have hg0 : 0 ≤ toReal g := (Real.exp_pos _).le.trans hexp
  -- `kn ≥ √b √n max s`
  have hsmax : ∀ i, toReal (s i) ≤ toReal (maximumOver s) := fun i => le_maximumOver s i
  have hsqb : Real.sqrt b ≤ toReal (sqrtUp 30 c.upper) := le_sqrtUp 30 c.upper
  have hsqn : Real.sqrt n ≤ toReal (sqrtUp 30 (nsmulUp n (FloatOps.one : 𝕋))) := by
    have h := le_nsmulUp n (FloatOps.one : 𝕋)
    rw [toReal_one, mul_one] at h
    exact (Real.sqrt_le_sqrt h).trans (le_sqrtUp 30 _)
  have hK : ∀ (d : ℝ) (x : Vec ℝ n), 0 ≤ d → (∀ i, |x i| ≤ d * toReal (s i)) →
      ν x ≤ toReal kn * d := by
    intro d x hd hx
    -- no state: nothing to bound
    by_cases hn : n = 0
    · subst hn
      have : x = 0 := funext fun i => i.elim0
      subst this
      have hk0 : 0 ≤ toReal kn := by
        have h := hkle
        have hz : toReal (maximumOver s) = 0 := by simp [maximumOver, toReal_zero]
        rw [hz, mul_zero] at h
        exact h
      simp [ν, mul_nonneg hk0 hd]
    -- `x'x ≤ n (d max s)²`, then the upper quadratic bound
    have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    set M := toReal (maximumOver s) with hM
    have hM0 : 0 ≤ M := (hs ⟨0, hn0⟩).le.trans (hsmax _)
    have hxx : x ⬝ᵥ x ≤ n * (d * M) ^ 2 := by
      rw [dotProduct]
      calc ∑ i, x i * x i ≤ ∑ _i : Fin n, (d * M) ^ 2 := Finset.sum_le_sum fun i _ => by
            have h1 := hx i
            have h2 := mul_le_mul_of_nonneg_left (hsmax i) hd
            have h3 : |x i| ≤ d * M := h1.trans h2
            nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
        _ = n * (d * M) ^ 2 := by simp
    have hq : x ⬝ᵥ (Pr *ᵥ x) ≤ b * (n * (d * M) ^ 2) :=
      (hb x).trans (mul_le_mul_of_nonneg_left hxx hb0.le)
    have hsq : ν x ≤ Real.sqrt b * Real.sqrt n * (d * M) := by
      calc ν x ≤ Real.sqrt (b * (n * (d * M) ^ 2)) := Real.sqrt_le_sqrt hq
        _ = Real.sqrt b * Real.sqrt n * (d * M) := by
          rw [Real.sqrt_mul hb0.le, Real.sqrt_mul (Nat.cast_nonneg _),
            Real.sqrt_sq (mul_nonneg hd hM0)]; ring
    -- the product of the rounded factors, rounded up
    have e1 : Real.sqrt b * Real.sqrt n ≤ toReal kn₀ :=
      (mul_le_mul hsqb hsqn (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hsqb)).trans hk₀le
    have e2 : Real.sqrt b * Real.sqrt n * M ≤ toReal kn :=
      (mul_le_mul_of_nonneg_right e1 hM0).trans hkle
    calc ν x ≤ Real.sqrt b * Real.sqrt n * (d * M) := hsq
      _ = Real.sqrt b * Real.sqrt n * M * d := by ring
      _ ≤ toReal kn * d := mul_le_mul_of_nonneg_right e2 hd
  -- `back ≥ 1/(√a sᵢ)` for every `i`, so an entry is within `ν B sᵢ`
  have hinva : (Real.sqrt a)⁻¹ ≤ toReal (sqrtUp 30 (divUp (FloatOps.one : 𝕋) c.lower)) := by
    have h1 := div_le_divUp (FloatOps.one : 𝕋) c.lower ha0
    rw [toReal_one] at h1
    calc (Real.sqrt a)⁻¹ = Real.sqrt a⁻¹ := (Real.sqrt_inv _).symm
      _ ≤ Real.sqrt (toReal (divUp (FloatOps.one : 𝕋) c.lower)) :=
        Real.sqrt_le_sqrt (by rw [← one_div]; exact h1)
      _ ≤ _ := le_sqrtUp 30 _
  -- `1/sᵢ ≤ max 1/s`
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  have hinvs : ∀ i,
      (toReal (s i))⁻¹ ≤ toReal (maximumOver fun i => divUp (FloatOps.one : 𝕋) (s i)) := fun i => by
      have h1 := div_le_divUp (FloatOps.one : 𝕋) (s i) (hs i)
      rw [toReal_one] at h1
      exact (by rw [← one_div]; exact h1 : (toReal (s i))⁻¹ ≤ _).trans
        (le_maximumOver (fun i => divUp (FloatOps.one : 𝕋) (s i)) i)
  have hB : ∀ (x : Vec ℝ n) i, |x i| ≤ ν x * toReal back * toReal (s i) := by
    intro x i
    have hν0 : 0 ≤ ν x := Real.sqrt_nonneg _
    -- `a xᵢ² ≤ a x'x ≤ x'Px`
    have hxi : |x i| * Real.sqrt a ≤ ν x := by
      have h2 : x i * x i ≤ x ⬝ᵥ x := by
        rw [dotProduct]
        exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)
      have h3 : a * (x i * x i) ≤ x ⬝ᵥ (Pr *ᵥ x) :=
        (mul_le_mul_of_nonneg_left h2 ha0.le).trans (ha x)
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, Real.sq_sqrt ha0.le, sq_abs]
      have e : x i ^ 2 * a = a * (x i * x i) := by ring
      linarith
    -- `1/√a` and `1/sᵢ`, each within its rounded factor
    have hsi := hs i
    have hq : 0 ≤ toReal (sqrtUp 30 (divUp (FloatOps.one : 𝕋) c.lower)) :=
      (inv_nonneg.2 hsa.le).trans hinva
    have hb1 := mul_le_mulUp (sqrtUp 30 (divUp (FloatOps.one : 𝕋) c.lower))
      (maximumOver fun i => divUp (FloatOps.one : 𝕋) (s i))
    have hprod : (Real.sqrt a)⁻¹ * (toReal (s i))⁻¹ ≤ toReal back :=
      (mul_le_mul hinva (hinvs i) (inv_nonneg.2 hsi.le) hq).trans hb1
    have key :
        |x i| = |x i| * Real.sqrt a * (Real.sqrt a)⁻¹ * (toReal (s i))⁻¹ * toReal (s i) := by
      field_simp
    rw [key]
    have := mul_le_mul_of_nonneg_right hxi (inv_nonneg.2 hsa.le)
    have h4 : |x i| * Real.sqrt a * (Real.sqrt a)⁻¹ * (toReal (s i))⁻¹ ≤ ν x * toReal back := by
      calc |x i| * Real.sqrt a * (Real.sqrt a)⁻¹ * (toReal (s i))⁻¹
          ≤ ν x * (Real.sqrt a)⁻¹ * (toReal (s i))⁻¹ :=
            mul_le_mul_of_nonneg_right this (inv_nonneg.2 hsi.le)
        _ = ν x * ((Real.sqrt a)⁻¹ * (toReal (s i))⁻¹) := by ring
        _ ≤ ν x * toReal back := mul_le_mul_of_nonneg_left hprod hν0
    exact mul_le_mul_of_nonneg_right h4 hsi.le
  -- `ν(e^{AΔt} x) ≤ g ν(x)` and the gauge is subadditive
  have hE : ∀ x : Vec ℝ n, ν (E *ᵥ x) ≤ toReal g * ν x := by
    intro x
    have h := Krylov.quad_exp_le_weighted (toRealMat A) Pr (toReal c.rate) hS hPA x hΔt
    calc ν (E *ᵥ x) ≤ Real.sqrt (Real.exp (2 * toReal c.rate * toReal Δt) * (x ⬝ᵥ (Pr *ᵥ x))) :=
          Real.sqrt_le_sqrt h
      _ = Real.exp (toReal c.rate * toReal Δt) * ν x := by
          rw [Real.sqrt_mul (Real.exp_pos _).le, show 2 * toReal c.rate * toReal Δt
            = (toReal c.rate * toReal Δt) + (toReal c.rate * toReal Δt) by ring, Real.exp_add,
            Real.sqrt_mul_self (Real.exp_pos _).le]
      _ ≤ toReal g * ν x := mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _)
  have hadd : ∀ x y, ν (x + y) ≤ ν x + ν y := LinearSys.aux_gauge_add_le Pr hS hpsd
  -- the factors are nonnegative
  have hq0 : 0 ≤ toReal (sqrtUp 30 (divUp (FloatOps.one : 𝕋) c.lower)) :=
    (inv_nonneg.2 hsa.le).trans hinva
  have hmi0 : 0 ≤ toReal (maximumOver fun i => divUp (FloatOps.one : 𝕋) (s i)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [maximumOver, toReal_zero]
    · exact (inv_nonneg.2 (hs ⟨0, hn⟩).le).trans (hinvs ⟨0, hn⟩)
  have hback0 : 0 ≤ toReal back := (mul_nonneg hq0 hmi0).trans (mul_le_mulUp _ _)
  have hM0 : 0 ≤ toReal (maximumOver s) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [maximumOver, toReal_zero]
    · exact (hs ⟨0, hn⟩).le.trans (hsmax _)
  have hk0 : 0 ≤ toReal kn := by
    have s1 := (Real.sqrt_nonneg b).trans hsqb
    have s2 := (Real.sqrt_nonneg (n : ℝ)).trans hsqn
    exact (mul_nonneg ((mul_nonneg s1 s2).trans hk₀le) hM0).trans hkle
  -- the new bounds in the weight
  set β' := addUp (mulUp g st.β) (mulUp kn loc.1) with hβ'
  set ψ' := addUp (mulUp g st.ψ) (mulUp kn loc.2) with hψ'
  have hβ'le : toReal g * toReal st.β + toReal kn * toReal loc.1 ≤ toReal β' := by
    have := add_le_addUp (mulUp g st.β) (mulUp kn loc.1)
    have := mul_le_mulUp g st.β
    have := mul_le_mulUp kn loc.1
    linarith
  have hψ'le : toReal g * toReal st.ψ + toReal kn * toReal loc.2 ≤ toReal ψ' := by
    have := add_le_addUp (mulUp g st.ψ) (mulUp kn loc.2)
    have := mul_le_mulUp g st.ψ
    have := mul_le_mulUp kn loc.2
    linarith
  have hβ'0 : 0 ≤ toReal β' := by linarith [mul_nonneg hg0 hβ0, mul_nonneg hk0 hl1, hβ'le]
  have hψ'0 : 0 ≤ toReal ψ' := by linarith [mul_nonneg hg0 hψ0, mul_nonneg hk0 hl2, hψ'le]
  -- the weighted bounds back in the scales, and the smaller carries
  have hwβ : toReal β' * toReal back ≤ toReal (mulUp β' back) := mul_le_mulUp _ _
  have hwψ : toReal ψ' * toReal back ≤ toReal (mulUp ψ' back) := mul_le_mulUp _ _
  have hwβ0 : 0 ≤ toReal (mulUp β' back) := (mul_nonneg hβ'0 hback0).trans hwβ
  have hwψ0 : 0 ≤ toReal (mulUp ψ' back) := (mul_nonneg hψ'0 hback0).trans hwψ
  have hst'h : toReal st'.h = min (toReal st₁.h) (toReal (mulUp β' back)) := by
    show toReal (Krylov.carryMinFloat st₁.h (mulUp β' back)) = _
    rw [Krylov.carryMinFloat, toReal_minimum]
  have hst'φ : toReal st'.φ = min (toReal st₁.φ) (toReal (mulUp ψ' back)) := by
    show toReal (Krylov.carryMinFloat st₁.φ (mulUp ψ' back)) = _
    rw [Krylov.carryMinFloat, toReal_minimum]
  have hst'β : st'.β = β' := rfl
  have hst'ψ : st'.ψ = ψ' := rfl
  -- a carried error within the Gershgorin bound and the weighted one
  have hfin : ∀ (hG w β₁ ℓ : ℝ), toReal g * β₁ + toReal kn * ℓ ≤ w → 0 ≤ ℓ →
      ∀ (x : ℝ) (ε δ : Vec ℝ n), 0 ≤ x → ν ε ≤ β₁ * x →
      (∀ i, |δ i| ≤ ℓ * x * toReal (s i)) →
      (∀ i, |(E *ᵥ ε + δ) i| ≤ hG * x * toReal (s i)) →
      ν (E *ᵥ ε + δ) ≤ w * x ∧
        ∀ i, |(E *ᵥ ε + δ) i| ≤ min hG (w * toReal back) * x * toReal (s i) := by
    intro hG w β₁ ℓ hw hℓ x ε δ hx hε hδ hGb
    obtain ⟨h1, h2⟩ := LinearSys.aux_core ν E (fun i => toReal (s i)) hs hadd (toReal g) hE
      (toReal kn) hK (toReal back) hB hg0 hback0 β₁ ℓ w x hℓ hx hw ε δ hε hδ
    -- the entry within both bounds
    refine ⟨h1, fun i => ?_⟩
    have hxs : 0 ≤ x * toReal (s i) := mul_nonneg hx (hs i).le
    rw [mul_assoc, min_mul_of_nonneg _ _ hxs]
    refine le_min (by rw [← mul_assoc]; exact hGb i) ?_
    have := h2 i
    have e : w * toReal back * x * toReal (s i) = w * toReal back * (x * toReal (s i)) := by ring
    linarith
  -- the other fields are kept; the zonotope, then `Φ`
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by rw [hst'h]; exact le_min hh1 hwβ0,
    by rw [hst'φ]; exact le_min hφ1 hwψ0, hβ'0, hψ'0, fun x ε δ hx hε hδ hG => ?_,
    fun x ε δ hx hε hδ hG => ?_⟩
  · obtain ⟨h1, h2⟩ := hfin _ _ _ _ hβ'le hl1 x ε δ hx hε hδ hG
    refine ⟨h1, fun i => (h2 i).trans ?_⟩
    rw [hst'h]
    have hxs : 0 ≤ x * toReal (s i) := mul_nonneg hx (hs i).le
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_min le_rfl hwβ) hxs
  · obtain ⟨h1, h2⟩ := hfin _ _ _ _ hψ'le hl2 x ε δ hx hε hδ hG
    refine ⟨h1, fun i => (h2 i).trans ?_⟩
    rw [hst'φ]
    have hxs : 0 ≤ x * toReal (s i) := mul_nonneg hx (hs i).le
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_min le_rfl hwψ) hxs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
