import Mathlib.Data.Stream.Defs
import Std.Data.List.Lemmas
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Find
import Mathlib.Tactic.Ring

import ListPowersProblem.StreamLemmas

open Stream'

/-- The infinite sequence of all naturals: `1`, `2`, ... -/
def nat : Stream' Nat :=
  (· + 1)

/-- 
  The infinite sequence of each natural number to the `e`-th power: 
  `0ᵉ`, `1ᵉ`, `2ᵉ`, ...
-/
def powers (e : Nat) : Stream' Nat := 
  fun i => (i + 1)^e

/-!
  We observe that if we start with the stream of all positive naturals
    ` 1   2   3   4   5   ⋯`
  Then drop every second element    (`Stream'.dropEveryNth 2`)
    ` 1       3       5   ⋯`
  And sum this sequence             (`Stream'.sum`)
    ` 1       4       9   ⋯`
  That we obtain the sequence of squares
-/

/-- 
  Sanity check: we can compute both sequences up to a finite bound, and check that these 
  computations indeed agree.
  We use `native_decide` to get fast computation, allowing for a higher bound in less time
-/
example : 
    let bound := 5 -- 100
    (nat.dropEveryNth 2 |>.sum |>.take bound) = (powers 2 |>.take bound) := by 
  native_decide

/--
  Now the real deal:
  We prove that the sequence obtained by this procedure is indeed the sequence of squares
-/
theorem procedure_two_eq_squares :
    (nat.dropEveryNth 2 |>.sum) = powers 2 := by
  funext i
  simp [dropEveryNth_two_eq_mul_two, nat, powers]
  induction' i with i ih
  · rfl
  · simp only [sum_succ, ih, pow_two, (show Nat.succ i = i + 1 from rfl)]
    ring




def sumDrop : Nat → Stream' Nat → Stream' Nat 
  | 0, σ | 1, σ  => σ
  | n+1, σ => sumDrop n <| sum <| σ.dropEveryNth (n+1)

@[simp]
theorem sumDrop_one : sumDrop 1 σ = σ := rfl

@[simp]
theorem sumDrop_two : sumDrop 2 nat = powers 2 := by
  simp only [sumDrop]; rw [procedure_two_eq_squares]

/--
  This pattern also works for cubes!
-/
example : 
    let bound := 2 --  20
    (sumDrop 3 nat |>.take bound) = (powers 3 |>.take bound) := by 
  native_decide


theorem sumDrop_three : sumDrop 3 nat = powers 3 := by 
  funext i
  simp [sumDrop, nat]
  rw [dropEveryNth_two_eq_mul_two]
  sorry