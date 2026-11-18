module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyKrylovPassFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyKrylovBoundsFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyKrylovWindowsFloat

@[expose] public section

/-!
# A pass of `LinearSys.verifyKrylovPassFloat` that holds verifies its specifications

If the pass holds, then on every step `j` of `Δt = Δt₀ / 2^h` and for every group, some direction
of the group holds `w' x(t) ≤ d` (`< d` if strict) for every `t` of the step, every
`x₀ ∈ c + G [-1, 1]^m` and everything `y` an input `u(s) ∈ u_c + G_U [-1, 1]^p` contributes by
`t`: its windows hold `w' e^{tA}` on the grid `Δt₀ = 2^h Δt`
(`LinearSys.verifyKrylovWindowsFloat_sound`), so its bounds hold the steps
(`LinearSys.verifyKrylovBoundsFloat_sound`). A safe set has a group per row; an unsafe set one for
all its rows `-a' y < -b`. Verified-only: a pass that does not hold decides nothing.

## Inputs
* `sys` – linear system, its `A` the system matrix
* `p` – Newton steps per norm
* `q` – squarings of the exponential
* `εb` – breakdown threshold of Arnoldi
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `dirs` – the directions
* `cert` – Lyapunov certificate `(P, L, a)` of `A'`, if any
* `groups` – the number of groups
* `Δt₀` – float step size of the windows
* `h` – halvings of the step size
* `N` – number of steps

## Hypotheses
* `hq` – at least one squaring
* `hP` – the pass holds

## Conclusion
* on every step every group has a direction whose halfspace holds the reachable states
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p' : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An `Option` `mapM` that succeeds maps every element to its partner. -/
private theorem LinearSys.aux_mapM {α β : Type} (f : α → Option β) : -- --- CONCL ---
    ∀ (l : List α) (bs : List β), l.mapM f = some bs →
      ∀ pr ∈ l.zip bs, f pr.1 = some pr.2 := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro bs _ pr hpr; simp at hpr
  | cons a l ih =>
    intro bs h pr hpr
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    rcases ha : f a with _ | b
    · rw [ha] at h; simp at h
    rw [ha] at h
    rcases hl : l.mapM f with _ | bs'
    · rw [hl] at h; simp at h
    rw [hl] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.mp hpr with rfl | hmem
    · exact ha
    · exact ih bs' hl pr hmem

/-- `h` halvings divide by `2^h`, exactly. -/
private theorem LinearSys.aux_half_iterate (x : 𝕋) (h : ℕ) :
    toReal (half^[h] x) = toReal x / 2 ^ h := by
  induction h with
  | zero => simp
  | succ h ih => rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ, div_div]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyKrylovPassFloat_sound (sys : LinearSys 𝕋 n) (p q : ℕ) (hq : 1 ≤ q)
    (εb : 𝕋) {c : Vec 𝕋 n} {G : Mat 𝕋 n m} {uc : Vec 𝕋 n} {GU : Mat 𝕋 n p'}
    {dirs : List (LinearSys.VerifyKrylovDirection 𝕋 n)} {cert : Option (Mat 𝕋 n n × Mat 𝕋 n n × 𝕋)}
    {groups : ℕ} {Δt₀ : 𝕋} {h N : ℕ}
    (hP : LinearSys.verifyKrylovPassFloat p q εb sys.A c G uc GU dirs cert groups Δt₀ h N =
      true) : -- --- CONCL ---
    ∀ g < groups, ∀ j < N, ∀ t : ℝ, (j : ℝ) * (toReal Δt₀ / 2 ^ h) ≤ t →
      t ≤ ((j : ℝ) + 1) * (toReal Δt₀ / 2 ^ h) → ∀ β : Fin m → ℝ, (∀ i, |β i| ≤ 1) →
      ∀ y ∈ sys.inputReach (S := ExactSet)
        ((fun γ => toRealVec uc + toRealMat GU *ᵥ γ) '' Set.Icc (-1) 1) t,
      ∃ d ∈ dirs, d.group = g ∧
        (if d.strict then toRealVec d.w ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ
            (toRealVec c + toRealMat G *ᵥ β) + y) < toReal d.limit
          else toRealVec d.w ⬝ᵥ (exp (t • toRealMat sys.A) *ᵥ
            (toRealVec c + toRealMat G *ᵥ β) + y) ≤ toReal d.limit) := by -- --- PROOF ---
  intro g hg j hj t h1 h2 β hβ y hy
  unfold LinearSys.verifyKrylovPassFloat at hP
  dsimp only at hP
  split at hP
  · cases hP
  rename_i Bs hBs
  have hpair := LinearSys.aux_mapM _ dirs Bs hBs
  -- the group's direction that holds the step
  have hall := List.all_eq_true.mp hP j (List.mem_range.mpr hj)
  have hgr := List.all_eq_true.mp hall g (List.mem_range.mpr hg)
  obtain ⟨pr, hpr, hok⟩ := List.any_eq_true.mp hgr
  rw [Bool.and_eq_true] at hok
  obtain ⟨hgrp, hb⟩ := hok
  refine ⟨pr.1, (List.of_mem_zip hpr).1, beq_iff_eq.mp hgrp, ?_⟩
  -- its windows and bounds
  have hf := hpair pr hpr
  rcases hw : LinearSys.verifyKrylovWindowsFloat p q εb sys.A pr.1.w Δt₀ pr.1.plan cert with
    _ | wins
  · rw [hw] at hf; cases hf
  rw [hw, Option.bind_some] at hf
  have hwin := LinearSys.verifyKrylovWindowsFloat_sound p q hq εb sys.A pr.1.w Δt₀ pr.1.plan cert
    wins (Option.mem_def.mpr hw)
  have hΔ : ((2 ^ h : ℕ) : ℝ) * toReal (half^[h] Δt₀) = toReal Δt₀ := by
    rw [LinearSys.aux_half_iterate]; push_cast; field_simp
  rw [← hΔ] at hwin
  -- the bounds of the windows on the halved grid
  obtain ⟨hlen, hclaim⟩ :=
    LinearSys.verifyKrylovBoundsFloat_sound sys hwin _ (Option.mem_def.mpr hf)
  have hjB : j < pr.2.length := by rw [hlen]; exact hj
  rw [List.getElem?_eq_getElem hjB] at hb
  dsimp only at hb
  have hx := hclaim j hjB t (by rw [LinearSys.aux_half_iterate]; exact h1)
    (by rw [LinearSys.aux_half_iterate]; exact h2) β hβ y hy
  split_ifs at hb ⊢ with hs
  · exact lt_of_le_of_lt hx (toReal_lt_of_ltStrict hb)
  · exact le_trans hx (toReal_le_of_le hb)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
