module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpMulVecSubInterpolateLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.GirardReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetAddEq
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
public import CORALean.ContDynamics.LinearSys.Theorems.NormLeOfMemInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Real.Theorems.NormLeAbsMax
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `girardReachFloat` holds every run: [1, Thm. 1] in floats

[1, Lemma 2] for `Q₀` and [1, Lemma 1] for each `Qᵢ`, as `girardReach_outer` has them, with
each exact quantity under its float enclosure: a run over the first step is the point of
the segment from `z` to `e^{rA} z` at `t/r`, which `conv(I, [e^{rA}] I)` holds, plus at most
`α_r + β_r` in norm; a later step is `e^{rA}` of the previous one plus at most `β_r`. The
float `α_r` and `β_r` bound the real ones because `e^x - 1 - x` grows with `x ≥ 0` and
`(e^{ra} - 1)/a` with `a > 0`, the latter by the convexity of `exp`.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `(e^{ra} - 1)/a` grows with `a > 0`: `e^{ra}` lies under the chord from `e^0` to `e^{rb}`. -/
theorem aux_exp_sub_one_div_mono {r a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (Real.exp (r * a) - 1) / a ≤ (Real.exp (r * b) - 1) / b := by -- --- PROOF ---
  have hb : 0 < b := ha.trans_le hab
  have hl0 : 0 ≤ a / b := (div_pos ha hb).le
  have hl1 : 0 ≤ 1 - a / b := by rw [sub_nonneg, div_le_one hb]; exact hab
  have hconv := convexOn_exp.2 (Set.mem_univ (r * b)) (Set.mem_univ 0) hl0 hl1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  rw [show a / b * (r * b) = r * a by field_simp] at hconv
  rw [div_le_div_iff₀ ha hb]
  have hkey : (Real.exp (r * a) - 1) * b ≤ a / b * (Real.exp (r * b) - 1) * b :=
    mul_le_mul_of_nonneg_right (by linarith) hb.le
  calc (Real.exp (r * a) - 1) * b ≤ a / b * (Real.exp (r * b) - 1) * b := hkey
    _ = (Real.exp (r * b) - 1) * a := by field_simp

/-- `e^x - 1 - x` grows with `x ≥ 0`. -/
theorem aux_exp_sub_one_sub_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp x - 1 - x ≤ Real.exp y - 1 - y := by
  have h1 := Real.add_one_le_exp (y - x)
  have h2 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have h3 : Real.exp y = Real.exp x * Real.exp (y - x) := by rw [← Real.exp_add]; ring_nf
  nlinarith

/-- A time in `[0, T]` lies in the window `[i r, (i+1) r]` of some `i < N`, `T ≤ N r`. -/
theorem aux_exists_window_float {r T t : ℝ} {N : ℕ} (hr : 0 < r) (hN : T / r ≤ N)
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ i < N - 1 + 1, (i : ℝ) * r ≤ t ∧ t ≤ ((i : ℝ) + 1) * r := by -- --- PROOF ---
  have hfl := Nat.floor_le (div_nonneg ht0 hr.le)
  have hlt := Nat.lt_floor_add_one (t / r)
  rcases le_or_gt ⌊t / r⌋₊ (N - 1) with h | h
  · refine ⟨⌊t / r⌋₊, by omega, ?_, ?_⟩
    · rwa [le_div_iff₀ hr] at hfl
    · exact ((div_le_iff₀ hr).mp hlt.le)
  · refine ⟨N - 1, by omega, ?_, ?_⟩
    · have : ((N - 1 : ℕ) : ℝ) ≤ ⌊t / r⌋₊ := by exact_mod_cast h.le
      calc ((N - 1 : ℕ) : ℝ) * r ≤ ⌊t / r⌋₊ * r := by gcongr
        _ ≤ t := (le_div_iff₀ hr).mp hfl
    · have hN' : (N : ℝ) ≤ ((N - 1 : ℕ) : ℝ) + 1 := by
        have : N ≤ N - 1 + 1 := by omega
        exact_mod_cast this
      calc t ≤ T := htT
        _ ≤ N * r := (div_le_iff₀ hr).mp hN
        _ ≤ (((N - 1 : ℕ) : ℝ) + 1) * r := by gcongr

/-- `k` passes of a loop that maps its state and appends the result. -/
theorem aux_foldl_iterate_float {α : Type} (f : α → α) (a : α) (k : ℕ) :
    (List.range k).foldl (fun (QR : α × List α) (_ : ℕ) => (f QR.1, QR.2 ++ [f QR.1])) (a, [a])
      = (f^[k] a, (List.range (k + 1)).map fun i => f^[i] a) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.range_succ, Function.iterate_succ_apply']


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] in floats: every state a run under inputs of norm at most `μ` reaches from `I`
over `[0, T]` is in some `Qᵢ`. -/
theorem LinearSys.girardReachFloat_outer (sys : LinearSys 𝕋 n) {I U : Zonotope (Vec 𝕋 n)}
    {μ r : 𝕋} {T : ℚ} {Qs : List (Zonotope (Vec 𝕋 n))} (h : sys.girardReachFloat I μ r T = some Qs)
    (hA : 0 < ‖Scalar.toRealMat sys.A‖) (hr : 0 < toReal r) (hμ : 0 ≤ toReal μ)
    (hU : ∀ u ∈ U.construct, ‖u‖ ≤ toReal μ) : -- --- STMT ---
    ⋃ t ∈ Set.Icc (0:ℝ) T, sys.reachSet (S := 𝒵[𝕋]) (Set.Icc 0 t) I U t
      ⊆ ⋃ Q ∈ Qs, Q.construct := by -- --- PROOF ---
  simp only [LinearSys.girardReachFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨η, hη, rfl⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec hη).1
  -- the algorithm's own names for what it computed
  set A := Scalar.toRealMat sys.A with hAdef
  set a := ‖A‖ with hadef
  set rr := toReal r with hrr
  set eRA := sys.expIntervalFloat r r η with heRA
  set nA := MatExp.normUpperBound (Interval.point sys.A) with hnA
  set x := mulUp r nA with hxdef
  set E := expUp (Nat.log2 (⌈ToRat.toRat x⌉₊ + 1) + 5) x with hEdef
  set s := maximum (FloatOps.zero : 𝕋) (maximumOver fun j => I.absBoundError j) with hsdef
  -- `α_r`, `β_r` and the cube they size
  set αr := mulUp (subUp (subUp E one) x) s with hαdef
  set βr := mulUp (divUp (subUp E one) nA) μ with hβdef
  set cube := fun c : 𝕋 => (⟨fun _ => neg c, fun _ => c⟩ : Interval (Vec 𝕋 n)).zonotope
    with hcubedef
  -- the float bounds on `‖A‖`, `r‖A‖` and `e^{r‖A‖}`
  have hanA : a ≤ toReal nA := le_trans (Real.Interval.norm_le_absMax (Interval.mem_point sys.A))
    (MatExp.norm_absMax_le_normUpperBound _)
  have hnA0 : 0 < toReal nA := hA.trans_le hanA
  have hxn : rr * toReal nA ≤ toReal x := mul_le_mulUp _ _
  have hra : rr * a ≤ toReal x := (mul_le_mul_of_nonneg_left hanA hr.le).trans hxn
  have hra0 : 0 ≤ rr * a := mul_nonneg hr.le hA.le
  have hE : Real.exp (toReal x) ≤ toReal E := by
    refine le_expUp _ _ ?_
    set m := ⌈ToRat.toRat x⌉₊ + 1 with hm
    have h1 : toReal x ≤ (m : ℝ) := by
      rw [← ToRat.toReal_toRat x, hm]; push_cast
      have := Nat.le_ceil (ToRat.toRat x)
      have h' : ((ToRat.toRat x : ℚ) : ℝ) ≤ ((⌈ToRat.toRat x⌉₊ : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at h'; linarith
    -- `m < 2^{log₂ m + 1}`, an eighth of `2^p / 2`
    have h2 : (m : ℝ) < 2 ^ (Nat.log2 m + 1) := by exact_mod_cast Nat.lt_log2_self
    have h3 : (2 : ℝ) ^ (Nat.log2 m + 1) ≤ 2 ^ (Nat.log2 m + 5) / 2 := by
      have hp : (0 : ℝ) < 2 ^ (Nat.log2 m + 1) := by positivity
      have h16 : (2 : ℝ) ^ (Nat.log2 m + 5) = 2 ^ (Nat.log2 m + 1) * 16 := by ring
      rw [h16]
      linarith
    linarith
  -- `□(c)` holds every vector of norm at most `c`
  have hcube : ∀ {c : 𝕋} {v : Vec ℝ n}, ‖v‖ ≤ toReal c → v ∈ (cube c).construct := by
    intro c v hv
    refine Interval.zonotope_contains _ fun j => ?_
    show toReal (FloatOps.neg c) ≤ v j ∧ v j ≤ toReal c
    have hj : |v j| ≤ toReal c := by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm v j).trans hv
    exact ⟨by rw [toReal_neg]; linarith [neg_abs_le (v j)], by linarith [le_abs_self (v j)]⟩
  -- `s` bounds the norm of every point of `I`
  have hs0 : 0 ≤ toReal s := by rw [hsdef, toReal_maximum, toReal_zero]; exact le_max_left _ _
  have hIs : ∀ z ∈ I.construct, ‖z‖ ≤ toReal s := fun z hz => by
    refine (pi_norm_le_iff_of_nonneg hs0).mpr fun j => ?_
    rw [Real.norm_eq_abs, hsdef, toReal_maximum]
    exact le_max_of_le_right ((Zonotope.abs_le_absBoundError hz j).trans (le_maximumOver _ j))
  -- the real `α_r` and `β_r` under the float ones
  have hβ0 : 0 ≤ (Real.exp (rr * a) - 1) / a * toReal μ :=
    mul_nonneg (div_nonneg (by linarith [Real.add_one_le_exp (rr * a)]) hA.le) hμ
  have hβ : (Real.exp (rr * a) - 1) / a * toReal μ ≤ toReal βr := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hμ) (mul_le_mulUp _ _)
    refine le_trans (aux_exp_sub_one_div_mono hA hanA) (le_trans ?_ (div_le_divUp _ _ hnA0))
    refine div_le_div_of_nonneg_right ?_ hnA0.le
    refine le_trans ?_ (sub_le_subUp _ _)
    rw [toReal_one]
    linarith [Real.exp_le_exp.mpr hxn]
  have hα0 : 0 ≤ (Real.exp (rr * a) - 1 - rr * a) * toReal s :=
    mul_nonneg (by linarith [Real.add_one_le_exp (rr * a)]) hs0
  have hα : (Real.exp (rr * a) - 1 - rr * a) * toReal s ≤ toReal αr := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hs0) (mul_le_mulUp _ _)
    refine le_trans (aux_exp_sub_one_sub_mono hra0 hra) (le_trans ?_ (sub_le_subUp _ _))
    have := sub_le_subUp E one
    rw [toReal_one] at this
    linarith
  -- `[e^{rA}] Z` holds `e^{rA} z`
  have hexp : exp (rr • A) ∈ eRA.construct := sys.exp_mem_expIntervalFloat hadm le_rfl le_rfl
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (rr • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eRA Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eRA Z
      (Set.mem_biUnion hexp (Set.mem_image_of_mem _ hz))
  have hUb : Bornology.IsBounded (ContSet.construct U) := CompactSet.isBounded_construct U
  set f : Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 n) := fun Q =>
    Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eRA Q ⊞
      cube βr with hf
  set Q₀ := LinComb.linComb I
    (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eRA I)
    ⊞ cube (addUp αr βr) with hQ₀
  -- every window lands in its own iterate
  have hwin : ∀ i : ℕ, ∀ t ∈ Set.Icc ((i : ℝ) * rr) (((i : ℝ) + 1) * rr),
      sys.reachSet (S := 𝒵[𝕋]) (Set.Icc 0 t) I U t ⊆
        (f^[i] Q₀).construct := by
    intro i
    induction i with
    | zero =>
      intro t ht y hy
      simp only [Nat.cast_zero, zero_mul, zero_add, one_mul] at ht
      obtain ⟨ht0, htr⟩ := ht
      rw [sys.reachSet_eq (S := 𝒵[𝕋]) I U ht0 hUb] at hy
      obtain ⟨_, ⟨z, hz, rfl⟩, v, hv, rfl⟩ := hy
      -- the point of the segment from `z` to `e^{rA} z`, at the fraction `t / r`
      have hlam : t / rr ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg ht0 hr.le, (div_le_one hr).mpr htr⟩
      set p : Vec ℝ n := (1 - t / rr) • z + (t / rr) • (exp (rr • A) *ᵥ z) with hp
      have hpP : p ∈ (LinComb.linComb I
          (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
            eRA I)).construct :=
        LinComb.linComb_outer _ _ ⟨z, hz, exp (rr • A) *ᵥ z, hmt hz, 1 - t / rr,
          ⟨by linarith [hlam.2], by linarith [hlam.1]⟩, by rw [hp, sub_sub_cancel]⟩
      -- what is left over: the interpolation error and the input's reach
      have hint := Real.MatExp.norm_exp_mulVec_sub_interpolate_le A ht0 htr z
      have hinput : ‖v‖ ≤ (Real.exp (rr * a) - 1) / a * toReal μ := by
        refine (sys.norm_le_of_mem_inputReach hA ht0 hU hv).trans ?_
        have : Real.exp (t * a) ≤ Real.exp (rr * a) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right htr hA.le)
        gcongr
      have hrest : ‖(exp (t • A)).mulVecLin z + v - p‖ ≤ toReal (addUp αr βr) := by
        have heq : (exp (t • A)).mulVecLin z + v - p
            = (exp (t • A) *ᵥ z - z - (t / rr) • (exp (rr • A) *ᵥ z - z)) + v := by
          rw [hp, Matrix.mulVecLin_apply]; module
        rw [heq]
        refine (norm_add_le _ _).trans (le_trans (add_le_add (hint.trans ?_) hinput)
          (le_trans (add_le_add hα hβ) (add_le_addUp _ _)))
        exact mul_le_mul_of_nonneg_left (hIs z hz) (by linarith [Real.add_one_le_exp (rr * a)])
      show (exp (t • A)).mulVecLin z + v ∈ _
      rw [show (exp (t • A)).mulVecLin z + v = p + ((exp (t • A)).mulVecLin z + v - p) by abel]
      exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hpP (hcube hrest))
    | succ i ih =>
      intro t ht y hy
      -- the next window is `e^{rA}` of this one plus the input over `r`
      have ht' : t - rr ∈ Set.Icc ((i : ℝ) * rr) (((i : ℝ) + 1) * rr) := by
        push_cast at ht; constructor <;> linarith [ht.1, ht.2]
      have hti : 0 ≤ t - rr := (mul_nonneg (Nat.cast_nonneg i) hr.le).trans ht'.1
      rw [show t = (t - rr) + rr by ring, sys.reachSet_add_eq (S := 𝒵[𝕋]) I U
        hti hr.le hUb] at hy
      obtain ⟨_, ⟨q, hq, rfl⟩, v, hv, rfl⟩ := hy
      rw [Function.iterate_succ_apply']
      have hvβ : ‖v‖ ≤ toReal βr := (sys.norm_le_of_mem_inputReach hA hr.le hU hv).trans hβ
      exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add (hmt (ih _ ht' hq)) (hcube hvβ))
  -- and every time in `[0, T]` lies in one of the `N` windows
  intro y hy
  obtain ⟨t, ⟨ht0, htT⟩, hyt⟩ := Set.mem_iUnion₂.mp hy
  have hN : (T : ℝ) / rr ≤ (⌈T / ToRat.toRat r⌉₊ : ℝ) := by
    have h1 := Nat.le_ceil (T / ToRat.toRat r)
    have h2 : (((T / ToRat.toRat r : ℚ)) : ℝ) ≤ ((⌈T / ToRat.toRat r⌉₊ : ℚ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    rwa [ToRat.toReal_toRat] at h2
  obtain ⟨i, hi, hti⟩ := aux_exists_window_float hr hN ht0 htT
  have hlist := congrArg Prod.snd (aux_foldl_iterate_float f Q₀ (⌈T / ToRat.toRat r⌉₊ - 1))
  refine Set.mem_iUnion₂.mpr ⟨f^[i] Q₀, ?_, hwin i t hti hyt⟩
  rw [hlist]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
