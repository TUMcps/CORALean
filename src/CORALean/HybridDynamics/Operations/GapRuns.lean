module

@[expose] public section

/-!
# `Location.gapRuns`

CORA's `aux_removeGaps` on the set indices of one guard: the list is cut after every index whose
successor in the list is not the next number, so that each run is one crossing of the guard (a
guard met at several points in time gives several runs). The indices keep their order.

## Inputs
* `is` – set indices of one guard, in the order of the hits

## Output
* the maximal runs of consecutive indices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The maximal runs of consecutive indices of `is`, in order. -/
def Location.gapRuns (is : List Nat) : List (List Nat) :=
  match is with
  | [] => []
  | i :: is' =>
    match Location.gapRuns is' with
    | [] => [[i]]
    | [] :: rest => [i] :: rest   -- (no run is empty)
    | (j :: js) :: rest => if j = i + 1 then (i :: j :: js) :: rest else [i] :: (j :: js) :: rest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
