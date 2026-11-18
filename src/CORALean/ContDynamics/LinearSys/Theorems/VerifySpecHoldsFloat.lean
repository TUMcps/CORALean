module

public import CORALean.ContDynamics.LinearSys.Operations.VerifySpecHoldsFloat
public import CORALean.ContDynamics.LinearSys.Theorems.VerifyZonoSupportUpFloat

@[expose] public section

/-!
# `LinearSys.verifySpecHoldsFloat` answering `true` is sound

A safe set: every point of the zonotope is strictly inside every halfspace, its support being
below the offset. An unsafe set: some multipliers `λ ≥ 0` pass the Farkas test, and then every
point `x` of the zonotope violates some row. Were `a'x ≤ b` for all rows, then
`(H'λ)'x ≤ λ'b ≤ lb < inf_Z (H'λ)' y ≤ (H'λ)'x`. `false` claims nothing: an undecided unsafe set
leaves the step unverified.

## Inputs
* `Z` – float zonotope with a box
* `S` – float safe or unsafe set

## Hypotheses
* `h` – the test answers `true`

## Conclusion
* a safe set holds strictly on every point of `Z`, an unsafe set misses every point of `Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A left fold of upward additions is at least its seed plus the sum of the terms. -/
private theorem LinearSys.aux_le_foldl_addUp' {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal a + (L.map fun x => toReal (f x)).sum
        ≤ toReal (L.foldl (fun acc x => addUp acc (f x)) a) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have := ih (addUp a (f x))
    linarith [add_le_addUp a (f x)]

/-- A left fold of downward additions is at most its seed plus the sum of the terms. -/
private theorem LinearSys.aux_foldl_addDown_le {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal (L.foldl (fun acc x => addDown acc (f x)) a)
        ≤ toReal a + (L.map fun x => toReal (f x)).sum := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have := ih (addDown a (f x))
    linarith [addDown_le_add a (f x)]

/-- The dot product with a sum of a list. -/
private theorem LinearSys.aux_list_sum_dot {α : Type} (f : α → Vec ℝ q) (x : Vec ℝ q) :
    ∀ L : List α, (L.map f).sum ⬝ᵥ x = (L.map fun p => f p ⬝ᵥ x).sum := by
  intro L
  induction L with
  | nil => simp
  | cons p L ih => simp [add_dotProduct, ih]

/-- An entry of a sum of a list. -/
private theorem LinearSys.aux_list_sum_apply {α : Type} (f : α → Vec ℝ q) (i : Fin q) :
    ∀ L : List α, (L.map f).sum i = (L.map fun p => f p i).sum := by
  intro L
  induction L with
  | nil => simp
  | cons p L ih => simp [ih]

/-- A passed Farkas test leaves every point of `Z` outside some row. -/
private theorem LinearSys.aux_farkas {Z : LinearSys.VerifyZono 𝕋 q} {rows : List (Vec 𝕋 q × 𝕋)}
    {lam : List 𝕋} (h : LinearSys.step_verifyFarkasFloat Z rows lam = true) {x : Vec ℝ q}
    (hx : x ∈ Z.toSet) : -- --- CONCL ---
    ∃ ab ∈ rows, toReal ab.2 < toRealVec ab.1 ⬝ᵥ x := by -- --- PROOF ---
  by_contra hcon
  push Not at hcon
  unfold LinearSys.step_verifyFarkasFloat at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨-, hlam⟩, hlt⟩ := h
  set pairs := rows.zip lam with hpairs
  have hp : ∀ p ∈ pairs, p.1 ∈ rows ∧ 0 ≤ toReal p.2 := by
    intro p hp
    have hz := toReal_le_of_le (hlam p.2 (List.of_mem_zip hp).2)
    rw [toReal_zero] at hz
    exact ⟨(List.of_mem_zip hp).1, hz⟩
  -- the exact direction `H'λ` and its bounds
  set ℓr : Vec ℝ q := (pairs.map fun p => toReal p.2 • toRealVec p.1.1).sum with hℓr
  have hdir : ∀ i, |-ℓr i - toReal ((-fun i => pairs.foldl (fun acc ab =>
      addUp acc (mulUp ab.2 (ab.1.1 i))) zero) i)| ≤ toReal (subUp (pairs.foldl (fun acc ab =>
      addUp acc (mulUp ab.2 (ab.1.1 i))) zero) (pairs.foldl (fun acc ab =>
      addDown acc (mulDown ab.2 (ab.1.1 i))) zero)) := by
    intro i
    -- the sum of the products between its folds rounded down and up
    have hi := LinearSys.aux_le_foldl_addUp' (fun ab : (Vec 𝕋 q × 𝕋) × 𝕋 =>
      mulUp ab.2 (ab.1.1 i)) pairs zero
    have lo := LinearSys.aux_foldl_addDown_le (fun ab : (Vec 𝕋 q × 𝕋) × 𝕋 =>
      mulDown ab.2 (ab.1.1 i)) pairs zero
    have hℓi : ℓr i = (pairs.map fun p => toReal p.2 * toReal (p.1.1 i)).sum := by
      rw [hℓr, LinearSys.aux_list_sum_apply]; rfl
    have h1 : (pairs.map fun p => toReal p.2 * toReal (p.1.1 i)).sum
        ≤ (pairs.map fun p => toReal (mulUp p.2 (p.1.1 i))).sum :=
      List.sum_le_sum fun p _ => mul_le_mulUp _ _
    have h2 : (pairs.map fun p => toReal (mulDown p.2 (p.1.1 i))).sum
        ≤ (pairs.map fun p => toReal p.2 * toReal (p.1.1 i)).sum :=
      List.sum_le_sum fun p _ => mulDown_le_mul _ _
    rw [toReal_zero, zero_add] at hi lo
    have hs := sub_le_subUp (pairs.foldl (fun acc ab => addUp acc (mulUp ab.2 (ab.1.1 i))) zero)
      (pairs.foldl (fun acc ab => addDown acc (mulDown ab.2 (ab.1.1 i))) zero)
    rw [Pi.neg_apply, toReal_neg', abs_le]
    constructor <;> linarith
  have hsup := LinearSys.dotProduct_le_verifyZonoSupportUpFloat hx _ _ hdir
  have hstrict := toReal_lt_of_ltStrict hlt
  rw [toReal_neg] at hstrict
  -- `(H'λ)'x ≤ λ'b ≤ lb`
  have hdot : ℓr ⬝ᵥ x
      ≤ toReal (pairs.foldl (fun acc ab => addUp acc (mulUp ab.2 ab.1.2)) zero) := by
    rw [hℓr, LinearSys.aux_list_sum_dot]
    have hb := LinearSys.aux_le_foldl_addUp' (fun ab : (Vec 𝕋 q × 𝕋) × 𝕋 =>
      mulUp ab.2 ab.1.2) pairs zero
    rw [toReal_zero, zero_add] at hb
    refine le_trans (List.sum_le_sum fun p hp' => ?_) hb
    obtain ⟨hrow, hl⟩ := hp p hp'
    rw [smul_dotProduct, smul_eq_mul]
    exact le_trans (mul_le_mul_of_nonneg_left (hcon p.1 hrow) hl) (mul_le_mulUp _ _)
  have hneg : (-ℓr) ⬝ᵥ x = -(ℓr ⬝ᵥ x) := neg_dotProduct _ _
  have : (fun i => -ℓr i) = -ℓr := rfl
  rw [this, hneg] at hsup
  linarith

omit [SoundFloatArithmetic 𝕋] in
/-- A passed test of an unsafe set comes from a passed Farkas test. -/
private theorem LinearSys.aux_apart {Z : LinearSys.VerifyZono 𝕋 q} {rows : List (Vec 𝕋 q × 𝕋)}
    (h : LinearSys.step_verifyApartFloat Z rows = true) : -- --- CONCL ---
    ∃ lam, LinearSys.step_verifyFarkasFloat Z rows lam = true := by -- --- PROOF ---
  unfold LinearSys.step_verifyApartFloat at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h
  rcases h with ⟨k, -, hk⟩ | ⟨-, g, -, d, -, ij, -, hij⟩
  · exact ⟨_, hk⟩
  · split at hij
    · exact ⟨_, hij⟩
    · exact absurd hij Bool.false_ne_true


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifySpecHoldsFloat_sound {Z : LinearSys.VerifyZono 𝕋 q}
    {S : LinearSys.VerifySpecSet 𝕋 q}
    (h : LinearSys.verifySpecHoldsFloat Z S = true) : -- --- CONCL ---
    (S.safe = true → ∀ x ∈ Z.toSet, ∀ ab ∈ S.rows, toRealVec ab.1 ⬝ᵥ x < toReal ab.2) ∧
    (S.safe = false → ∀ x ∈ Z.toSet,
      ∃ ab ∈ S.rows, toReal ab.2 < toRealVec ab.1 ⬝ᵥ x) := by -- --- PROOF ---
  unfold LinearSys.verifySpecHoldsFloat at h
  refine ⟨fun hs x hx ab hab => ?_, fun hs x hx => ?_⟩
  · -- the support along the row is below its offset
    rw [hs, if_pos rfl, List.all_eq_true] at h
    have hlt := toReal_lt_of_ltStrict (h ab hab)
    have hle := LinearSys.dotProduct_le_verifyZonoSupportUpFloat hx ab.1 (fun _ => zero)
      (ℓr := toRealVec ab.1) (fun i => by simp [toRealVec, toReal_zero])
    linarith
  · -- a Farkas certificate
    rw [hs] at h
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨lam, hlam⟩ := LinearSys.aux_apart h
    exact LinearSys.aux_farkas hlam hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
