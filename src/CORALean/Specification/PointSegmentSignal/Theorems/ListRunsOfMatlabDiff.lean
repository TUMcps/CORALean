module

public import CORALean.Specification.PointSegmentSignal.Operations.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.Basic
public import CORALean.Specification.PointSegmentSignal.Theorems.MemMatlabFind
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Set

@[expose] public section

/-!
# The runs of `true` in a Boolean array

`find(diff(x) == -1)` and `find(diff(x) == 1) + 1` of a logical array `x` are the ends and the
starts of its runs of `true`: with a start added at `1` when `x(1)` holds, the starts paired with
the ends, the last one open to the end of the array, are runs that are all `true`, begin after a
`false` and end before one, and cover every `true`.

## Inputs
* `tk` – Boolean array
* `F` – ends of runs
* `R` – starts of runs after the first
* `R'` – starts of runs

## Hypotheses
* `hne` – the array is nonempty
* `hF` – the ends are found by `find` and `diff`
* `hR` – the later starts are found by `find` and `diff`
* `hR'` – the starts add the first index if the array starts true

## Conclusion
* starts and ends bound the maximal runs of true
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An entry of `diff` is the difference of two neighbours. -/
theorem aux_diff_getElem (l : List Bool) (i : ℕ) (h : i + 1 < l.length) :
    (List.matlabDiff l)[i]? = some ((l[i+1].toNat : ℤ) - l[i].toNat) := by
  simp [List.matlabDiff, List.getElem?_zipWith, List.getElem?_tail, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem (show i < l.length by omega)]

/-- `diff` has one entry fewer than the array. -/
theorem aux_diff_length (l : List Bool) : (List.matlabDiff l).length = l.length - 1 := by
  simp [List.matlabDiff]


/-- An entry of `diff`, by index. -/
theorem aux_diff_getElem' (l : List Bool) (i : ℕ) (h : i < (List.matlabDiff l).length) :
    (List.matlabDiff l)[i] = ((l[i+1]'(by have := aux_diff_length l; omega)).toNat : ℤ) -
      (l[i]'(by have := aux_diff_length l; omega)).toNat := by
  have h1 := aux_diff_length l
  have h2 := aux_diff_getElem l i (by omega)
  rw [List.getElem?_eq_getElem h] at h2
  exact Option.some.inj h2

/-- The falling edges are the positions where `true` is followed by `false`. -/
theorem aux_mem_fall (tk : List Bool) (f : ℕ) :
    f ∈ List.matlabFind (· == (-1 : ℤ)) (List.matlabDiff tk) ↔
      1 ≤ f ∧ f < tk.length ∧ tk.getD (f - 1) false = true ∧
        tk.getD f true = false := by -- --- PROOF ---
  rw [List.mem_matlabFind]
  have hl := aux_diff_length tk
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [aux_diff_getElem' tk (f - 1) h2] at h3
    have h4 : f - 1 + 1 = f := by omega
    simp only [h4] at h3
    -- the two entries of the array are read as Booleans
    refine ⟨h1, by omega, ?_⟩
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show f - 1 < tk.length by omega),
      List.getElem?_eq_getElem (show f < tk.length by omega), Option.getD_some]
    generalize tk[f - 1]'(by omega) = a at h3 ⊢
    generalize tk[f]'(by omega) = b at h3 ⊢
    cases a <;> cases b <;> simp_all
  · rintro ⟨h1, h2, h3, h4⟩
    -- conversely, the flag is set
    refine ⟨h1, by omega, ?_⟩
    rw [aux_diff_getElem' tk (f - 1) (by omega)]
    have h5 : f - 1 + 1 = f := by omega
    simp only [h5]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show f - 1 < tk.length by omega),
      List.getElem?_eq_getElem (show f < tk.length by omega), Option.getD_some] at h3 h4
    generalize tk[f - 1]'(by omega) = a at h3 ⊢
    generalize tk[f]'(by omega) = b at h4 ⊢
    cases a <;> cases b <;> simp_all


/-- The rising edges are the positions where `false` is followed by `true`. -/
theorem aux_mem_rise (tk : List Bool) (r : ℕ) :
    r ∈ (List.matlabFind (· == (1 : ℤ)) (List.matlabDiff tk)).map (· + 1) ↔
      2 ≤ r ∧ r ≤ tk.length ∧ tk.getD (r - 2) true = false ∧
        tk.getD (r - 1) false = true := by -- --- PROOF ---
  rw [List.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.mem_matlabFind] at hj
    obtain ⟨h1, h2, h3⟩ := hj
    have hl := aux_diff_length tk
    rw [aux_diff_getElem' tk (j - 1) h2] at h3
    have h4 : j - 1 + 1 = j := by omega
    simp only [h4] at h3
    -- the two entries of the array are read as Booleans
    refine ⟨by omega, by omega, ?_⟩
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j - 1 < tk.length by omega),
      List.getElem?_eq_getElem (show j < tk.length by omega), Option.getD_some,
      show j + 1 - 2 = j - 1 by omega, show j + 1 - 1 = j by omega]
    generalize tk[j - 1]'(by omega) = a at h3 ⊢
    generalize tk[j]'(by omega) = b at h3 ⊢
    cases a <;> cases b <;> simp_all
  · rintro ⟨h1, h2, h3, h4⟩
    -- conversely, the position `r - 1` is found by `find`
    refine ⟨r - 1, ?_, by omega⟩
    rw [List.mem_matlabFind]
    have hl := aux_diff_length tk
    refine ⟨by omega, by omega, ?_⟩
    rw [aux_diff_getElem' tk (r - 1 - 1) (by omega)]
    have h5 : r - 1 - 1 + 1 = r - 1 := by omega
    simp only [h5]
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show r - 2 < tk.length by omega),
      List.getElem?_eq_getElem (show r - 1 < tk.length by omega), Option.getD_some] at h3 h4
    have h6 : r - 1 - 1 = r - 2 := by omega
    simp only [h6]
    generalize tk[r - 2]'(by omega) = a at h3 ⊢
    generalize tk[r - 1]'(by omega) = b at h4 ⊢
    cases a <;> cases b <;> simp_all

/-- Counting the entries `≤ m + 1` adds those equal to `m + 1`. -/
theorem aux_countP_succ (L : List ℕ) (m : ℕ) :
    L.countP (fun x => decide (x ≤ m + 1)) = L.countP (fun x => decide (x ≤ m)) +
      L.countP (fun x => decide (x = m + 1)) := by -- --- PROOF ---
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : a ≤ m
    · have : a ≠ m + 1 := by omega
      simp [h1, this, h1.trans (Nat.le_succ m)]; omega
    · by_cases h2 : a = m + 1
      · simp [h2]; omega
      · have : ¬ a ≤ m + 1 := by omega
        simp [h1, h2, this]

/-- In an increasing list an entry is counted at most once. -/
theorem aux_countP_eq (L : List ℕ) (hL : L.Pairwise (· < ·)) (x : ℕ) :
    L.countP (fun y => decide (y = x)) = if x ∈ L then 1 else 0 := by -- --- PROOF ---
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    simp only [List.countP_cons, ih hL.2]
    by_cases h : a = x
    · subst h
      have : a ∉ L := fun hm => lt_irrefl _ (hL.1 a hm)
      simp [this]
    · have h' : x ∈ a :: L ↔ x ∈ L := by simp [Ne.symm h]
      simp [h, h']

/-- In an increasing list the first entries are those `≤ m`. -/
theorem aux_getElem_le_iff (L : List ℕ) (hL : L.Pairwise (· < ·)) (m i : ℕ) (hi : i < L.length) :
    L[i] ≤ m ↔ i < L.countP (fun x => decide (x ≤ m)) := by -- --- PROOF ---
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases h : a ≤ m
    · simp only [List.countP_cons, h, decide_true, if_true]
      cases i with
      | zero => simp [h]
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [ih hL.2 j (by simpa using hi)]
        omega
    -- the first entry is `> m`, so no entry is `≤ m`
    · have hall : ∀ y ∈ L, ¬ y ≤ m := fun y hy => by have := hL.1 y hy; omega
      have hz : L.countP (fun x => decide (x ≤ m)) = 0 := by
        rw [List.countP_eq_zero]; intro y hy; simpa using hall y hy
      simp only [List.countP_cons, h, decide_false, hz]
      simp only [Bool.false_eq_true, if_false, Nat.zero_add, not_lt_zero, iff_false, not_le]
      cases i with
      | zero => simp; omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := hL.1 _ (List.getElem_mem (by simpa using hi))
        omega

/-- In an increasing list the first entries are those `< m`. -/
theorem aux_getElem_lt_iff (L : List ℕ) (hL : L.Pairwise (· < ·)) (m i : ℕ) (hi : i < L.length) :
    L[i] < m ↔ i < L.countP (fun x => decide (x < m)) := by -- --- PROOF ---
  have := aux_getElem_le_iff L hL (m - 1) i hi
  cases m with
  | zero =>
    simp
  | succ m =>
    simpa [Nat.lt_succ_iff] using this


/-- Counting the entries `< m + 1` adds those equal to `m`. -/
theorem aux_countP_succ' (L : List ℕ) (m : ℕ) (hm : 1 ≤ m) :
    L.countP (fun x => decide (x < m + 1)) = L.countP (fun x => decide (x < m)) +
      L.countP (fun x => decide (x = m)) := by -- --- PROOF ---
  have h := aux_countP_succ L (m - 1)
  rw [show m - 1 + 1 = m by omega] at h
  have e1 : L.countP (fun x => decide (x < m + 1)) = L.countP (fun x => decide (x ≤ m)) := by
    apply List.countP_congr; intro x _; simp [Nat.lt_succ_iff]
  have e2 : L.countP (fun x => decide (x < m)) = L.countP (fun x => decide (x ≤ m - 1)) := by
    apply List.countP_congr; intro x _; simp; omega
  rw [e1, e2]; exact h

/-- Inside the list the default of `getD` does not matter. -/
theorem aux_getD_eq (tk : List Bool) (i : ℕ) (hi : i < tk.length) (d d' : Bool) :
    tk.getD i d = tk.getD i d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The number of runs begun by `m` less the number ended before it is the entry at `m`. -/
theorem aux_D (tk : List Bool) (F R : List ℕ) (hF : F.Pairwise (· < ·))
    (hFm : ∀ f, f ∈ F ↔ 1 ≤ f ∧ f < tk.length ∧ tk.getD (f - 1) false = true ∧
      tk.getD f true = false)
    (hR : R.Pairwise (· < ·))
    (hRm : ∀ r, r ∈ R ↔ 1 ≤ r ∧ r ≤ tk.length ∧ tk.getD (r - 1) false = true ∧
      (r = 1 ∨ tk.getD (r - 2) true = false)) (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ tk.length) :
    R.countP (fun x => decide (x ≤ m)) =
      F.countP (fun x => decide (x < m)) +
        (if tk.getD (m - 1) false = true then 1 else 0) := by -- --- PROOF ---
  induction m, h1 using Nat.le_induction with
  -- at the first value only a start at one can be counted
  | base =>
    have hr : R.countP (fun x => decide (x ≤ 1)) = if 1 ∈ R then 1 else 0 := by
      have : R.countP (fun x => decide (x ≤ 1)) = R.countP (fun x => decide (x = 1)) := by
        apply List.countP_congr
        intro x hx
        have := ((hRm x).1 hx).1
        simp; omega
      rw [this, aux_countP_eq R hR]
    have hf : F.countP (fun x => decide (x < 1)) = 0 := by
      rw [List.countP_eq_zero]; intro x hx; have := ((hFm x).1 hx).1; simp; omega
    rw [hr, hf]
    by_cases h : tk.getD 0 false = true
    -- the first value is `true`: a run starts at one
    · have : 1 ∈ R := (hRm 1).2 ⟨le_rfl, by omega, by simpa using h, Or.inl rfl⟩
      simp only [this, if_true, Nat.sub_self, h, Nat.zero_add]
    · have : 1 ∉ R := fun hm => by
        have := ((hRm 1).1 hm).2.2.1; simp at this; exact h this
      have h' : tk.getD 0 false = false := by simpa using h
      simp only [this, if_false, Nat.sub_self, h', Nat.zero_add]; rfl
  -- from `m` to `m + 1` the count of starts and of ends change with the edges
  | succ m hm ih =>
    have ih := ih (by omega)
    rw [aux_countP_succ, aux_countP_eq R hR, ih, aux_countP_succ' F m hm, aux_countP_eq F hF]
    have e1 : m + 1 - 1 = m := by omega
    rw [e1]
    have hmF : m ∈ F ↔ tk.getD (m - 1) false = true ∧ tk.getD m false = false := by
      rw [hFm, aux_getD_eq tk m (by omega) true false]
      constructor
      · rintro ⟨-, -, a, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨hm, by omega, a, b⟩
    have hmR : m + 1 ∈ R ↔ tk.getD m false = true ∧ tk.getD (m - 1) false = false := by
      rw [hRm, show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega,
        aux_getD_eq tk (m - 1) (by omega) true false]
      constructor
      · rintro ⟨-, -, a, (h | b)⟩
        · omega
        · exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨by omega, h2, a, Or.inr b⟩
    rw [if_congr hmF rfl rfl, if_congr hmR rfl rfl]
    cases ha : tk.getD (m - 1) false <;> cases hb : tk.getD m false <;> simp

/-- The runs of `true`, as the rising edges paired with the falling edges. -/
theorem aux_runs (tk : List Bool) (F R : List ℕ) (hF : F.Pairwise (· < ·))
    (hFm : ∀ f, f ∈ F ↔ 1 ≤ f ∧ f < tk.length ∧ tk.getD (f - 1) false = true ∧
      tk.getD f true = false)
    (hR : R.Pairwise (· < ·))
    (hRm : ∀ r, r ∈ R ↔ 1 ≤ r ∧ r ≤ tk.length ∧ tk.getD (r - 1) false = true ∧
      (r = 1 ∨ tk.getD (r - 2) true = false)) (hne : tk ≠ []) : -- --- CONCL ---
    F.length ≤ R.length ∧ R.length ≤ F.length + 1 ∧
    (∀ p ∈ R.zip (F ++ [tk.length]), 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ tk.length ∧
      (∀ m, p.1 ≤ m → m ≤ p.2 → tk.getD (m - 1) false = true) ∧
      (2 ≤ p.1 → tk.getD (p.1 - 2) true = false) ∧
      (p.2 < tk.length → tk.getD p.2 true = false)) ∧
    (∀ m, 1 ≤ m → m ≤ tk.length → tk.getD (m - 1) false = true →
      ∃ p ∈ R.zip (F ++ [tk.length]), p.1 ≤ m ∧ m ≤ p.2) := by -- --- PROOF ---
  have hN : 1 ≤ tk.length := List.length_pos_iff.mpr hne
  have hD := aux_D tk F R hF hFm hR hRm
  have hcrN : R.countP (fun x => decide (x ≤ tk.length)) = R.length := by
    rw [List.countP_eq_length]; intro x hx; simpa using ((hRm x).1 hx).2.1
  have hcfN : F.countP (fun x => decide (x < tk.length)) = F.length := by
    rw [List.countP_eq_length]; intro x hx; simpa using ((hFm x).1 hx).2.1
  have hlen := hD tk.length hN le_rfl
  rw [hcrN, hcfN] at hlen
  have hlen1 : F.length ≤ R.length ∧ R.length ≤ F.length + 1 := by
    split_ifs at hlen <;> omega
  -- the pairs of starts and ends are runs, and they cover the `true` values
  refine ⟨hlen1.1, hlen1.2, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have hi' : i < (R.zip (F ++ [tk.length])).length := hi
    simp only [List.length_zip, List.length_append, List.length_singleton] at hi'
    simp only [List.getElem_zip]
    have hiR : i < R.length := lt_of_lt_of_le hi' (min_le_left _ _)
    set r := R[i] with hr
    set f := (F ++ [tk.length])[i]'(by simp; omega) with hf
    have hrm := (hRm r).1 (List.getElem_mem hiR)
    have hiF : (∃ h : i < F.length, f = F[i]) ∨ (i = F.length ∧ f = tk.length) := by
      rcases lt_or_ge i F.length with h | h
      · exact Or.inl ⟨h, by rw [hf, List.getElem_append_left h]⟩
      · right
        have : i = F.length := by simp at hi'; omega
        refine ⟨this, ?_⟩
        rw [hf]; simp [List.getElem_append_right, this]
    -- the end is within the array
    have hfN : f ≤ tk.length := by
      rcases hiF with ⟨h, e⟩ | ⟨_, e⟩
      · rw [e]; exact ((hFm _).1 (List.getElem_mem h)).2.1.le
      · rw [e]
    -- counts of the starts and of the ends before `m`
    have ha : ∀ m, r ≤ m → i < R.countP (fun x => decide (x ≤ m)) := fun m hm =>
      (aux_getElem_le_iff R hR m i hiR).1 hm
    have hb : ∀ m, m ≤ f → F.countP (fun x => decide (x < m)) ≤ i := by
      intro m hm
      rcases hiF with ⟨h, e⟩ | ⟨e, _⟩
      · by_contra hc
        have := (aux_getElem_lt_iff F hF m i h).2 (by omega)
        omega
      · rw [e]; exact List.countP_le_length
    -- the start is not after the end
    have hrf : r ≤ f := by
      by_contra hc
      have hlt : f < r := by omega
      have hcf : i < F.countP (fun x => decide (x < r)) := by
        rcases hiF with ⟨h, e⟩ | ⟨_, e⟩
        · exact (aux_getElem_lt_iff F hF r i h).1 (by omega)
        · omega
      have hcr : R.countP (fun x => decide (x ≤ r)) ≤ i + 1 := by
        by_contra hc2
        have h2' := List.countP_le_length (p := fun x => decide (x ≤ r)) (l := R)
        have h2 : i + 1 < R.length := by omega
        have := (aux_getElem_le_iff R hR r (i + 1) h2).2 (by omega)
        have h3 := List.pairwise_iff_getElem.1 hR i (i + 1) hiR h2 (by omega)
        omega
      have := hD r (by omega) hrm.2.1
      have h4 : tk.getD (r - 1) false = true := hrm.2.2.1
      simp only [h4, if_true] at this
      omega
    -- the run is all `true`, after a `false` and before a `false`
    refine ⟨hrm.1, hrf, hfN, ?_, ?_, ?_⟩
    · intro m hm1 hm2
      have hmN : m ≤ tk.length := hm2.trans hfN
      have := hD m (by omega) hmN
      have h1 := ha m hm1
      have h2 := hb m hm2
      by_contra hc
      have : tk.getD (m - 1) false = false := by simpa using hc
      simp only [this] at *
      simp at *
      omega
    · intro h2
      rcases hrm.2.2.2 with h | h
      · omega
      · exact h
    · intro hfl
      rcases hiF with ⟨h, e⟩ | ⟨_, e⟩
      · rw [e]; exact ((hFm _).1 (List.getElem_mem h)).2.2.2
      · omega
  -- every `true` value lies in a run: the one counted by `c`
  · intro m hm1 hm2 hmt
    have h1 := hD m hm1 hm2
    simp only [hmt, if_true] at h1
    set c := F.countP (fun x => decide (x < m)) with hc
    have hcF : c ≤ F.length := List.countP_le_length
    have hcR' := List.countP_le_length (p := fun x => decide (x ≤ m)) (l := R)
    have hcR : c < R.length := by omega
    have hcG : c < (F ++ [tk.length]).length := by simp; omega
    -- that run starts at or before `m` and ends at or after it
    refine ⟨(R[c], (F ++ [tk.length])[c]), ?_, ?_, ?_⟩
    · have : (R[c], (F ++ [tk.length])[c]) = (R.zip (F ++ [tk.length]))[c]'(by simp; omega) := by
        simp [List.getElem_zip]
      rw [this]; exact List.getElem_mem _
    · exact (aux_getElem_le_iff R hR m c hcR).2 (by omega)
    · rcases lt_or_ge c F.length with h | h
      · rw [List.getElem_append_left h]
        by_contra hlt
        have := (aux_getElem_lt_iff F hF m c h).1 (by omega)
        omega
      · have : c = F.length := by omega
        simp [List.getElem_append_right, this, hm2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The runs found by `find` and `diff` are the maximal runs of `true`. -/
theorem List.runs_of_matlabDiff (tk : List Bool) (hne : tk ≠ []) (F R R' : List ℕ)
    (hF : F = List.matlabFind (· == (-1 : ℤ)) (List.matlabDiff tk))
    (hR : R = (List.matlabFind (· == (1 : ℤ)) (List.matlabDiff tk)).map (· + 1))
    (hR' : R' = if tk.head? = some true then 1 :: R else R) : -- --- CONCL ---
    R'.length ≤ F.length + 1 ∧
    (∀ p ∈ R'.zip (F ++ [tk.length]), 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ tk.length ∧
      (∀ m, p.1 ≤ m → m ≤ p.2 → tk.getD (m - 1) false = true) ∧
      (2 ≤ p.1 → tk.getD (p.1 - 2) true = false) ∧
      (p.2 < tk.length → tk.getD p.2 true = false)) ∧
    (∀ m, 1 ≤ m → m ≤ tk.length → tk.getD (m - 1) false = true →
      ∃ p ∈ R'.zip (F ++ [tk.length]), p.1 ≤ m ∧ m ≤ p.2) := by -- --- PROOF ---
  -- the first value is `true` exactly when the first run starts at one
  have hhead : tk.head? = some true ↔ tk.getD 0 false = true := by
    cases tk with
    | nil => exact absurd rfl hne
    | cons a l => simp
  -- the edges, as positions of `tk`
  have hFm : ∀ f, f ∈ F ↔ 1 ≤ f ∧ f < tk.length ∧ tk.getD (f - 1) false = true ∧
      tk.getD f true = false := by rw [hF]; exact aux_mem_fall tk
  have hFs : F.Pairwise (· < ·) := by rw [hF]; exact List.pairwise_matlabFind _ _
  have hRm0 : ∀ r, r ∈ R ↔ 2 ≤ r ∧ r ≤ tk.length ∧ tk.getD (r - 2) true = false ∧
      tk.getD (r - 1) false = true := by rw [hR]; exact aux_mem_rise tk
  have hRs0 : R.Pairwise (· < ·) := by
    rw [hR]; exact (List.pairwise_matlabFind _ _).map _ (fun a b h => by omega)
  -- the starts of the runs: the rising edges, and one if the first value is `true`
  have hRm : ∀ r, r ∈ R' ↔ 1 ≤ r ∧ r ≤ tk.length ∧ tk.getD (r - 1) false = true ∧
      (r = 1 ∨ tk.getD (r - 2) true = false) := by
    intro r
    by_cases hh : tk.head? = some true
    · rw [hR', if_pos hh, List.mem_cons, hRm0]
      have h0 := hhead.1 hh
      constructor
      · rintro (rfl | ⟨a, b, c, d⟩)
        · exact ⟨le_rfl, by have := List.length_pos_iff.2 hne; omega, h0, Or.inl rfl⟩
        · exact ⟨by omega, b, d, Or.inr c⟩
      · rintro ⟨a, b, c, (rfl | d)⟩
        · exact Or.inl rfl
        · by_cases h1 : r = 1
          · exact Or.inl h1
          · exact Or.inr ⟨by omega, b, d, c⟩
    -- the first value is `false`: no run starts at one
    · rw [hR', if_neg hh, hRm0]
      have h0 : ¬ tk.getD 0 false = true := fun h => hh (hhead.2 h)
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨by omega, b, d, Or.inr c⟩
      · rintro ⟨a, b, c, (rfl | d)⟩
        · exact absurd c h0
        · by_cases h1 : r = 1
          · subst h1; exact absurd c h0
          · exact ⟨by omega, b, d, c⟩
  have hRs : R'.Pairwise (· < ·) := by
    rw [hR']
    by_cases hh : tk.head? = some true
    · rw [if_pos hh, List.pairwise_cons]
      exact ⟨fun a ha => by have := ((hRm0 a).1 ha).1; omega, hRs0⟩
    · rw [if_neg hh]; exact hRs0
  obtain ⟨-, hl2, hT1, hT2⟩ := aux_runs tk F R' hFs hFm hRs hRm hne
  exact ⟨hl2, hT1, hT2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
