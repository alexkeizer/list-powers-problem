import ListPowersProblem.Stream
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

namespace Stream' 

variable {σ : Stream' α}


/-!
  ## Iterate
-/

theorem iterate_eq_Nat_iterate :
  iterate f a i = f^[i] a := by
induction' i with i ih
· rfl
· unfold iterate Nat.iterate
  rw [ih, Function.Commute.iterate_self]

theorem iterate_stream_eq_index_iterate (σ : Stream' α) (f : Nat → Nat) :
    iterate (fun s i => s (f i)) σ i j = σ (f^[i] j) := by
  rw [iterate_eq_Nat_iterate]
  induction' i with i ih generalizing σ 
  · rfl
  · simp [ih]; congr; exact (Function.iterate_succ_apply' f i j).symm

/-! 
  ## sum
-/

theorem take_append_drop_take :
    σ.take i ++ (σ.drop i |>.take j) = σ.take (i + j) := by
  simp only [drop, nth]
  induction' i with i ih generalizing j σ
  · simp [take]
  · rw [Nat.add_assoc i 1 j, Nat.add_comm 1 j, ←Nat.add_assoc i j 1]
    simp [take, ←ih]
    congr
    
theorem take_succ_to_concat :
    take (i+1) σ = (take i σ).concat (σ i) := by
  rw [←take_append_drop_take]
  simp only [take, head, nth, drop, zero_add, List.concat_eq_append]
  
theorem sum_eq_head_plus_sum_tail (σ : Stream' Nat) (i : Nat) :
    σ.sum (i + 1) = (head σ) + (tail σ).sum i := by
  simp only [sum, take, head, nth, Nat.add_eq, add_zero, Nat.sum_cons]

@[simp]
theorem sum_succ (σ : Stream' Nat) (i : Nat) :
    σ.sum (i + 1) = σ.sum i + σ (i + 1) := by
  simp [sum, take_succ_to_concat, Nat.add_assoc]

theorem sum_eq_corec (σ : Stream' Nat) :
    σ.sum = corec Prod.fst (fun (acc, σ) => (
      acc + head σ,
      tail σ 
    )) (head σ, tail σ) := by
  funext i
  simp only [corec, map, nth]
  induction' i with i ih
  · rfl
  · simp only [sum_succ, iterate, ← ih, add_right_inj]
    simp only [iterate_eq_Nat_iterate, head, nth]
    clear ih
    have (g : ℕ × Stream' ℕ → ℕ) (y) : 
        Prod.snd ((fun x => (g x, tail x.snd))^[i] (y, tail σ))
        = ((fun x => tail x)^[i] (tail σ)) := by
      induction i generalizing y σ <;> simp [*]
    rw [this]; clear this
    simp [tail, nth]
    suffices ∀ k,
        σ (i + k) = (fun x i => x (i + 1))^[i] (fun i => σ (i + k)) 0
      from this 1
    intro k
    induction' i with i ih generalizing k
    · rfl 
    · simp [Nat.add_assoc, ←ih (1+k)]
      show σ (i + 1 + k) = _
      congr 1
      ring_nf


/-!
  ## Corec
-/

/-- Prove stream equality by providing a bisimulation relation `R` -/
theorem corec_bisim {f : α → β} {g : α → α} {f' : α' → β} {g' : α' → α'}
    (R : α → α' → Prop) 
    (hf : ∀ a a', R a a' → f a = f' a') 
    (hg : ∀ a a', R a a' → R (g a) (g' a')) :
    ∀ {a a'}, R a a' → corec f g a = corec f' g' a' := by
  intro a a' hR
  funext i
  simp [corec, map, nth]
  apply hf
  induction' i with i ih
  · exact hR
  · exact hg _ _ ih

/-!
  ## Even
-/

lemma iterate_add_eq_mul (x) :
    (· + x)^[y] z = (x * y) + z := by
  induction' y with y ih generalizing z
  · simp only [Nat.zero_eq, Function.iterate_zero, id_eq, mul_zero, zero_add]
  · simp only [Function.iterate_succ, Function.comp_apply, ih, ←Nat.add_one]; ring_nf

theorem even_eq_mul_two (σ : Stream' α) :
    σ.even = fun i => σ (i * 2) := by
  funext i
  simp [even, corec, map, head, nth, tail, iterate_stream_eq_index_iterate, iterate_add_eq_mul 2]
  rw [Nat.mul_comm]

/-!
  ## DropEveryNth
-/

theorem dropEveryNth_two_eq_even :
    σ.dropEveryNth 2 = σ.even := by
  simp [even, dropEveryNth, corec']
  apply corec_bisim (fun ⟨σ, n⟩ σ' => σ = σ' ∧ n = 0)
  · rintro ⟨σ, n⟩ σ' ⟨⟨⟩, ⟨⟩⟩
    simp [drop, head, nth]
  · rintro ⟨σ, n⟩ σ' ⟨⟨⟩, ⟨⟩⟩
    simp [tail, nth]
  · exact ⟨rfl, rfl⟩

theorem dropEveryNth_two_eq_mul_two (σ : Stream' α) :
    σ.dropEveryNth 2 = fun i => σ (i * 2) := by
  rw [dropEveryNth_two_eq_even, even_eq_mul_two]

end Stream'
