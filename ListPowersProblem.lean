import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Lemmas
import Mathlib.Tactic.Ring
import Std.Data.List.Lemmas


/-- The infinite sequence of all naturals: `1`, `2`, ... -/
def nat : Stream' Nat :=
  (· + 1)

/-- 
  The infinite sequence of each natural number to the `e`-th power: 
  `0ᵉ`, `1ᵉ`, `2ᵉ`, ...
-/
def powers (e : Nat) : Stream' Nat := 
  fun i => (i + 1)^e

/-- 
  Given a sequence of naturals `σ : Stream' Nat`,
  `σ.sumPreceding` is the sequence whose `i`-th element is the sum of the elements at indices 
  `0`, `1`, ..., `i`
 -/
def Stream'.sumPreceding (σ : Stream' Nat) : Stream' Nat :=
  fun i => 
    List.range (i+1)
      |>.map (σ ·)
      |>.foldl (· + ·) 0

open Stream'

theorem Stream'.even_simp (σ : Stream' α) :
    σ.even = fun i => σ (i * 2) := by
  simp

example : nat.even.sumPreceding = powers 2 := by
  funext i
  simp[sumPreceding, nat, powers, pow_two, even]
  
  induction i
  · rfl
  · simp[sumPreceding]

#eval nat.take 100
#eval (powers 2).take 100
#eval nat.odd.sumPreceding.take 100
#eval nat.even.sumPreceding.take 100

def hello := "world"