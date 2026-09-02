import CORALean.Global.Tensor

/-!
# Reading one block of a concatenated vector

`Fin.append` builds a vector out of two; these read the halves back, as linear
maps rather than as functions, so that a constraint on one half becomes a
constraint on the whole by `comap` and no sum has to be split.

That is what lets an operation which concatenates coefficient vectors — a
constrained zonotope's `plus`, or its multiplication by an interval matrix —
state its constraints by composing polytopes instead of assembling matrix rows.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

/-- The first `m` coordinates. -/
def blockLeft (m n : ℕ) : Vec ℝ (m + n) →ₗ[ℝ] Vec ℝ m where
  toFun v := fun j => v (Fin.castAdd n j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The last `n` coordinates. -/
def blockRight (m n : ℕ) : Vec ℝ (m + n) →ₗ[ℝ] Vec ℝ n where
  toFun v := fun j => v (Fin.natAdd m j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem blockLeft_append {m n : ℕ} (u : Vec ℝ m) (v : Vec ℝ n) :
    blockLeft m n (Fin.append u v) = u :=
  funext fun j => Fin.append_left u v j

@[simp] theorem blockRight_append {m n : ℕ} (u : Vec ℝ m) (v : Vec ℝ n) :
    blockRight m n (Fin.append u v) = v :=
  funext fun j => Fin.append_right u v j

end CORALean
