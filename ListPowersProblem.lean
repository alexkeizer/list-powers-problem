import Mathlib.Data.Stream.Defs
import Std.Data.List.Lemmas
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Find
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

import ListPowersProblem.StreamLemmas

open Stream'

/-- 
  The infinite sequence of each positive natural number to some constant `e`-th power: 
    `1ᵉ`, `2ᵉ`, ...
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
    (pnats.dropEveryNth 2 |>.sum |>.take bound) = (powers 2 |>.take bound) := by 
  native_decide

/--
  Now the real deal:
  We prove that the sequence obtained by this procedure is indeed the sequence of squares
-/
theorem procedure_two_eq_squares :
    (pnats.dropEveryNth 2 |>.sum) = powers 2 := by
  funext i
  simp [dropEveryNth_two_eq_mul_two, powers, pnats]
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
theorem sumDrop_two : sumDrop 2 pnats = powers 2 := by
  simp only [sumDrop]; rw [procedure_two_eq_squares]

/--
  This pattern also works for cubes!
-/
example : 
    let bound := 2 --  20
    (sumDrop 3 pnats |>.take bound) = (powers 3 |>.take bound) := by 
  native_decide


#eval sum (dropEveryNth 3 pnats) |>.take 12
#eval tail (sum (dropEveryNth 1 pnats)) - sum (dropEveryNth 1 pnats) |>.take 20
#eval tail (sum (dropEveryNth 2 pnats)) - sum (dropEveryNth 2 pnats) |>.take 20

#eval take 20       (dropEveryNth 3 nats)
#eval take 20 (fun i => nats (i + i / 2))

-- i = 0  => 1
-- i = 1  => 2
-- i = 2  => 4
-- i = 3  => 5
-- i = 4  => 7
-- i = 5  => 8

-- theorem dropEveryNth_of_i_lt_n (h : i < n + 2) :
--     dropEveryNth (n+2) σ i = σ i := by
--   simp [dropEveryNth]
--   suffices ∀ x,
--       corec (fun x => head x.fst)
--       (fun x =>
--         match x with
--         | (σ, 0) => (tail (tail σ), n)
--         | (σ, Nat.succ m) => (tail σ, m))
--       (σ, x) i 
--       = _
--   from this _
--   intro x
--   induction' i with i ih generalizing σ x
--   · rfl
--   · have h : i < n + 2 := Nat.lt_of_succ_lt h
--     rw [corec_succ]
--     cases' x with x
--     · simp [ih h]
--     · simp [ih h]; rfl

-- theorem dropEveryNth_eq_take_append_drop :
--     dropEveryNth (n+1) σ = σ.take n ++ dropEveryNth (n+1) (σ.drop n) := by
--   -- simp [dropEver]
--   induction' n with n ih
--   · rfl
--   · simp [take]

-- let n = 3
--
-- i = 0 => 1
-- i = 1 => 0
-- i = 2 => 1
-- i = 3 => 0

theorem Nat.not_dvd_of_mod_neq_zero : 
    a % b ≠ 0 → ¬b ∣ a := by
  rw [Nat.dvd_iff_mod_eq_zero]
  exact id

theorem dropEveryNth_three_eq_fun : 
    dropEveryNth 3 σ = fun i => σ (i + i/2) := by
  rw [dropEveryNth, fun_to_corec fun i => σ (i + i/2)]
  apply corec_bisim (fun ⟨σ', c⟩ i => σ' = (σ.drop <| i + i/2) 
    ∧ c = (i+1) % 2)
  · rintro ⟨_, _⟩ i ⟨⟨⟩, ⟨⟩⟩
    simp only [head, nth, drop, zero_add]
  · rintro ⟨_, _⟩ i ⟨⟨⟩, ⟨⟩⟩
    simp; 
    rw [Nat.add_mod (i+1) 1]
    cases h : (i+1)%2
    · have hdvd : 2 ∣ i+1 := Nat.dvd_of_mod_eq_zero h
      simp [tail, drop, nth, Nat.succ_div_of_dvd hdvd]
      funext j
      congr 1
      ring
    · simp [tail, drop, nth]
      constructor
      · funext j
        congr 1
        have hdvd : ¬2 ∣ i+1 := by
          apply Nat.not_dvd_of_mod_neq_zero 
          intro h'
          rw [h] at h'
          contradiction
        rw [Nat.succ_div_of_not_dvd hdvd]
        ring
      · cases' Nat.mod_two_eq_zero_or_one (i + 1) with h' h'
        <;> rw [h'] at h
        · contradiction
        · simp at h; rw[←h]; rfl
  · exact ⟨rfl, rfl⟩

theorem dropEveryNth_eq_fun : 
    dropEveryNth (n+1) σ = fun i => σ (i + i/n) := by
  rw [dropEveryNth, fun_to_corec fun i => σ (i + i/n)]
  stop -- STOP
  apply corec_bisim (fun ⟨σ', c⟩ i => σ' = (σ.drop <| i + i/n) 
    ∧ c = (i+1) % n)
  · rintro ⟨_, _⟩ i ⟨⟨⟩, ⟨⟩⟩
    simp only [head, nth, drop, zero_add]
  · rintro ⟨_, _⟩ i ⟨⟨⟩, ⟨⟩⟩
    simp; 
    rw [Nat.add_mod (i+1) 1]
    cases h : (i+1)%n
    · have hdvd : n ∣ i+1 := Nat.dvd_of_mod_eq_zero h
      simp [tail, drop, nth, Nat.succ_div_of_dvd hdvd]
      funext j
      congr 1
      ring
    · simp [tail, drop, nth]
      constructor
      · funext j
        congr 1
        have hdvd : ¬2 ∣ i+1 := by
          apply Nat.not_dvd_of_mod_neq_zero 
          intro h'
          rw [h] at h'
          contradiction
        rw [Nat.succ_div_of_not_dvd hdvd]
        ring
      · cases' Nat.mod_two_eq_zero_or_one (i + 1) with h' h'
        <;> rw [h'] at h
        · contradiction
        · simp at h; rw[←h]; rfl
  · exact ⟨rfl, rfl⟩

#eval take 20 (fun j => sum (fun i => i + i / 2 + i) (j+j))
#eval take 20       (fun i => i + i / 2 + 1)
#eval take 20 (sum (fun i => i + i / 2 + 1))


-- #eval take 20 (fun j => sum (fun i => i + i / 2 + 1) (j+j+1))
-- #eval take 20 (fun j => 3 * (j+1)^2)
-- lemma sum_eq_three_odd : 
--     sum (fun i => i + i/2 + 1) (j+j+1) = 3 * (j+1)^2 := by
--   simp [pow_two]
--   sorry

theorem Nat.mul_div {a b : Nat} (hb : 0 < b) : 
    a * b / b = a := by
  have hb' : b ≠ 0 := by 
    rintro ⟨⟩; contradiction
  induction a generalizing b
  <;> simp [Nat.succ_mul, Nat.add_div hb, hb', *]

#eval take 20 (fun j => sum (fun i => i + i / 2 + 1) (j+j))
#eval take 20 (fun j => 3 * (j^2 + j) + 1)
lemma sum_eq_three_even : 
    sum (fun i => i + i/2 + 1) (j+j) = 3 * (j^2 + j) + 1 := by
  simp [pow_two]
  induction' j with j ih
  · rfl
  · have hlt : 0 < 2 := by decide
    simp only [
      Nat.add_succ, add_zero, Nat.succ_add, sum_succ, ih, Nat.mul_succ, Nat.succ.injEq
    ]
    have h1 : Nat.succ j = j + 1 := rfl
    have h2 : Nat.succ (j + j) = j + j + 1 := rfl
    have h3 : Nat.succ (j + j + 1) = j + j + 2 := rfl
    rw [h1, h2, h3]
    ring_nf
    rw [Nat.add_div hlt, Nat.mul_div hlt]
    simp [
      show 1 / 2 = 0 from rfl,
      show ∀ x, Nat.succ x = x + 1 from fun _ => rfl
    ]
    ring

#eval take 20 <| sum nats
#eval take 20 <| fun i => (i^2) / 2

lemma sum_nats : sum nats = fun i => i * (i+1) / 2 := by
  simp [nats, pow_two]
  funext i
  induction' i with i ih
  · rfl
  · simp only [sum_succ, ih, Nat.add_succ, add_zero, Nat.succ_mul, Nat.mul_succ, Nat.succ_div, 
      Nat.isUnit_iff]
    show _ + 1 = _
    have not_two_le : ¬2 ≤ (i * i + i) % 2 := by
      cases Nat.mod_two_eq_zero_or_one (i * i + i) <;> simp [*]
    simp [
      Nat.add_assoc (i*i+i) i i, 
      Nat.add_div (a := i*i+i), 
      ←mul_two i,
      Nat.mul_div,
      not_two_le,
      Nat.add_assoc ((i * i + i) / 2 + i),
      Nat.dvd_iff_mod_eq_zero
    ]
    have : (Nat.succ (Nat.succ (i * i + i + i * 2))) % 2 
          = (Nat.succ ((Nat.succ (i * i + i + i * 2) % 2))) % 2 := by
      show (_ + 1) % 2 = _
      rw [Nat.add_mod]
      rfl
    rw [this]
    cases' Nat.mod_two_eq_zero_or_one (Nat.succ (i * i + i + i * 2)) with h h
      <;> simp [h]

      

#eval take 20 (sum fun i => i            )
#eval take 20 (fun i => (i / 3) * 4      )
#eval take 20     (fun i => i + i / 3 + 1)
#eval take 20 (sum fun i => i + i / 3 + 1)
#eval take 20 (fun j => sum (fun i => i + i / 3 + 1) (j+(j/2)))
#eval take 20 (fun j => j * ((4/3)*j + 1) + (j+j) )

-- lemma sum_eq_three : 
--     sum (fun i => i + i/2 + 1) 
--     = fun j => 
--       if j % 2 = 0 then
--          := by
--   sorry

lemma sum_n [NeZero n] : 
    sum (fun i => i + i/(n+1) + 1) (j+(j/n)) = 3 * (j^2 + j) + 1 := by
  sorry

theorem sumDrop_three : sumDrop 3 pnats = powers 3 := by 
  funext i
  simp only [sumDrop, powers, pow_three, 
    dropEveryNth_eq_fun, pnats, Nat.div_one,
    sum_eq_three_even
  ]
  induction' i with i ih
  · rfl
  · simp [ih, show Nat.succ i = i + 1 from rfl]; ring

theorem sumDrop_four : sumDrop 4 pnats = powers 4 := by 
  funext i
  simp only [sumDrop, powers, pow_succ, pow_zero, mul_one, 
    dropEveryNth_eq_fun, pnats, Nat.div_one
  ]
  induction' i with i ih
  · rfl
  · sorry

theorem sumDrop_five : sumDrop 5 pnats = powers 5 := by 
  funext i
  simp only [sumDrop, powers, pow_succ, pow_zero, mul_one, 
    dropEveryNth_eq_fun, pnats, Nat.div_one
  ]
  induction' i with i ih
  · rfl
  · sorry
    