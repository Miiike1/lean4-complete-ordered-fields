import Init
import Mathlib.Util.Notation3
import Mathlib.Data.Set.Operations
import Mathlib.Tactic


class SupSet (α : Type _) :=
  (sSup : Set α → α)

def f : ℕ → ℝ := fun n ↦ n ^ 2 + 3
#check f
#eval f 3
