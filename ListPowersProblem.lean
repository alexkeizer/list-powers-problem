import Mathlib.Data.Stream.Defs
import Std.Data.List.Lemmas
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Find
import Mathlib.Tactic.Ring


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

#check iterate
#check Nat.iterate

theorem Stream'.iterate_eq_Nat_iterate :
    iterate f a i = f^[i] a := by
  induction' i with i ih
  · rfl
  · unfold iterate Nat.iterate
    rw [ih, Function.Commute.iterate_self]

theorem Stream'.iterate_stream (σ : Stream' α) (f : Nat → Nat) :
    iterate (fun s i => s (f i)) σ i j = σ (f^[i] j) := by
  rw [iterate_eq_Nat_iterate]
  induction' i with i ih generalizing σ 
  · rfl
  · simp [ih]; congr; exact (Function.iterate_succ_apply' f i j).symm


-- #find (fun x => x + ?y)^[?i] 0 = ?y * ?i

-- #find Nat.succ ?n = ?n + 1

theorem Nat.iterate_add_eq_mul (x) :
    (· + x)^[y] z = (x * y) + z := by
  induction' y with y ih generalizing z
  · simp only [zero_eq, Function.iterate_zero, id_eq, mul_zero, zero_add]
  · simp only [Function.iterate_succ, Function.comp_apply, ih, ←Nat.add_one]; ring_nf

theorem Stream'.even_eq_mul_two (σ : Stream' α) :
    σ.even = fun i => σ (i * 2) := by
  funext i
  simp [even, corec, map, head, nth, tail, iterate_stream, Nat.iterate_add_eq_mul 2]
  rw [Nat.mul_comm]
  
  
#eval List.range 3

/-- Sanity check -/
example : (nat.even.sumPreceding).take 10 = (powers 2).take 10 := by rfl

example : nat.even.sumPreceding = powers 2 := by
  funext i
  simp[sumPreceding, nat, powers, pow_two, even_eq_mul_two, List.foldl_map]
  induction' i with i ih
  · rfl
  · simp []

#eval nat.take 100
#eval (powers 2).take 100
#eval nat.odd.sumPreceding.take 100
#eval nat.even.sumPreceding.take 100

def hello := "world"