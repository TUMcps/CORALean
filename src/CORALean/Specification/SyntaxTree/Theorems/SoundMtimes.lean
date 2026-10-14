module

public import CORALean.Specification.SyntaxTree.Definitions.Sound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.Mtimes
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.SoundSum
public import CORALean.Specification.SyntaxTree.Theorems.Basic

@[expose] public section

/-!
# `mtimes` of sound trees is sound

Every entry of `mtimes` over sound trees is sound.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of `mtimes` of sound trees is sound. -/
theorem SyntaxTree.sound_mtimes {m k p : ℕ} {A : Fin m → Fin (k + 1) → SyntaxTree n}
    {C : Fin (k + 1) → Fin p → SyntaxTree n} (hA : ∀ i l, Sound B (A i l))
    (hC : ∀ l j, Sound B (C l j)) (i : Fin m) (j : Fin p) : Sound B (mtimes A C i j) :=
  sound_sum (sound_times (hA i 0) (hC 0 j)) _ (fun u hu => by
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hu
    exact sound_times (hA i l.succ) (hC l.succ j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
