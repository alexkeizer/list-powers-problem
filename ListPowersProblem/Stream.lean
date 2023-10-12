import Mathlib.Data.Stream.Defs
import Std.Data.List.Lemmas

namespace Stream'

/-- The infinite sequence of all positive naturals: `1`, `2`, ... -/
def pnats : Stream' Nat :=
  (· + 1)

/-- 
  Given a sequence of naturals `σ : Stream' Nat`,
  `σ.sum` is the sequence whose `i`-th element is the sum of the elements at indices 
  `0`, `1`, ..., `i`
 -/
def sum (σ : Stream' Nat) : Stream' Nat :=
  fun i => σ.take (i + 1) |> Nat.sum

/--
  Remove every `n`-th element from the stream
-/
def dropEveryNth (n : Nat) (σ : Stream' α ) : Stream' α := 
  corec (fun ⟨σ, _⟩ => head σ) (fun
    | ⟨σ, 0⟩    => ⟨tail (tail σ), n-2⟩
    | ⟨σ, m+1⟩  => ⟨tail σ, m⟩ 
  ) (σ, n-2)

/--
  Transform a sequence `x₀, x₁, x₂, x₃, x₄, x₅, ⋯` into a sequence where each 
  element whose index is *not* a multiple of `n` is replaced with `0`.
  For example, if `n = 3`, then the resulting sequence if
    `x₀, 0, 0, x₃, 0, 0, x₆, 0, 0, ⋯`
-/
def maskEveryNth (n : Nat) (σ : Stream' Nat) : Stream' Nat := fun i =>
  if i % n = 0 then
    σ i
  else
    0

def append : List α → Stream' α → Stream' α
  | [], σ           => σ 
  | .cons a as, σ   => a :: (append as σ)

instance : HAppend (List α) (Stream' α) (Stream' α) := ⟨append⟩
    

instance [Sub α] : Sub (Stream' α) where
  sub σ₁ σ₂ := fun i => σ₁ i - σ₂ i

/-!
  ## Arithmetic sequences
-/

class ArithmeticSequence {α} [Sub α] [Add α] [HMul Nat α α] [LE α] (σ : Stream' α) where
  (increasing : σ 0 ≤ σ 1 := by decide)
  is_arithmetic : ∀ i, σ i = σ 0 + i * (σ 1 - σ 0)

instance : ArithmeticSequence nats where
  is_arithmetic i := by simp [nats]

instance : ArithmeticSequence pnats where
  is_arithmetic i := by simp [pnats, Nat.add_comm]



end Stream'