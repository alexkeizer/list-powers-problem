import Mathlib.Data.Stream.Defs
import Std.Data.List.Lemmas

namespace Stream'

/-- 
  Given a sequence of naturals `σ : Stream' Nat`,
  `σ.sum` is the sequence whose `i`-th element is the sum of the elements at indices 
  `0`, `1`, ..., `i`
 -/
def sum (σ : Stream' Nat) : Stream' Nat :=
  fun i => σ.take (i + 1) |> Nat.sum

#check even

/--
  Remove every `n`-th element from the stream
-/
def dropEveryNth (n : Nat) (σ : Stream' α ) : Stream' α := 
  corec' (fun
    | ⟨σ, 0⟩    => ⟨head σ, tail (tail σ), n-2⟩
    | ⟨σ, m+1⟩  => ⟨head σ, tail σ, m⟩ 
  ) (σ, n-2)

#eval sum (·) |>.take 10

end Stream'