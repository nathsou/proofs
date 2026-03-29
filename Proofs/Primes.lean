
/-- A number n is prime if n ≥ 2 and n is only divisible by 1 and itself -/
def Prime (n : Nat) : Prop := n > 1 ∧ ∀k, k ∣ n → (k = 1 ∨ k = n)

def fact (n : Nat) : Nat :=
  match n with
    | 0 => 1
    | n' + 1 => (n' + 1) * (fact n')

/-- The factorial of n is divisible by all natural numbers in [1, n] -/
theorem fact_div {n m : Nat} : m ≥ 1 ∧ m <= n → m ∣ fact n := by
  intro ⟨hm, hmn⟩
  induction n with
    | zero =>
      have h₁ : 1 ≤ 0 := Nat.le_trans hm hmn
      contradiction
    | succ n' ih =>
      unfold fact
      rcases Nat.eq_or_lt_of_le hmn with hl | hr
      .
        subst hl
        exact Nat.dvd_mul_right (n' + 1) (fact n')
      .
        have h₁ : m ≤ n' := Nat.le_of_lt_succ hr
        have h₂ : m ∣ fact n' := ih h₁
        exact Nat.dvd_mul_left_of_dvd h₂ (n' + 1)

theorem prime_ge_two {p : Nat} (hp : Prime p) : p ≥ 2 := hp.1

theorem composite_mp {n : Nat} : ¬(Prime n) → n ≤ 1 ∨ ∃k, k ∣ n ∧ k ≠ 1 ∧ k ≠ n :=
  fun hnp =>
  have h₁ : ¬(n > 1) ∨ ¬(∀k, k ∣ n → (k = 1 ∨ k = n)) := Decidable.not_and_iff_not_or_not.mp hnp
  match h₁ with
    | Or.inl h => Or.inl (Nat.le_of_not_lt h)
    | Or.inr h =>
      have h₂ : ∃k, ¬(k ∣ n → k = 1 ∨ k = n) := Classical.not_forall.mp h
      have ⟨k, hk⟩ := h₂
      have h₃ : k ∣ n ∧ ¬(k = 1 ∨ k = n) := Decidable.not_imp_iff_and_not.mp hk
      have h₄ : ¬(k = 1 ∨ k = n) := h₃.right
      have h₅ : k ≠ 1 ∧ k ≠ n := not_or.mp h₄
      Or.inr ⟨k, ⟨h₃.left, h₅⟩⟩

theorem exists_prime_div (n : Nat) (hn1 : n ≥ 2) : ∃p, p ∣ n ∧ Prime p := by
  by_cases h : Prime n
  . have h₁ : n ∣ n := Nat.dvd_refl n
    exact ⟨n, ⟨h₁, h⟩⟩
  . rcases composite_mp h with hl | hr
    .
      have h₂ : 1 < 1 := Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hn1) hl
      contradiction
    .
      have ⟨k, hk_dvd, hk1, hkn⟩ := hr
      have h₂ : n > 0 := Nat.zero_lt_of_lt hn1
      have h₃ : k ≤ n := Nat.le_of_dvd h₂ hk_dvd
      have h₄ : k < n := Nat.lt_of_le_of_ne h₃ hkn
      have h₅ : k > 0 := Nat.pos_of_dvd_of_pos hk_dvd h₂
      have h₆ : k > 1 := Nat.lt_of_le_of_ne h₅ (id (Ne.symm hk1))
      have ⟨p, hp_dvd, hp'⟩ := exists_prime_div k h₆
      have hp_dvd_n : p ∣ n := Nat.dvd_trans hp_dvd hk_dvd
      exact ⟨p, ⟨hp_dvd_n, hp'⟩⟩

theorem fact_increasing (n : Nat) : fact n <= fact (n + 1) :=
  @Nat.le_mul_of_pos_left (n + 1) (fact n) (Nat.succ_pos n)

theorem fact_ge_one (n : Nat) : fact n ≥ 1 := by
  induction n with
    | zero => exact Nat.le_of_ble_eq_true rfl
    | succ n' ih =>
      have h : fact (n' + 1) ≥ fact n' := fact_increasing n'
      exact Nat.le_trans ih h

/-- Given a natural number, we can find a greater natural number that is prime.
In other words, there are infinitely many prime numbers. -/
theorem infinitude_of_primes : ∀n, ∃p, p > n ∧ Prime p := by
  intro n
  let N := (fact n) + 1
  have hd := exists_prime_div N
  have h₁ : fact n ≥ 1 := fact_ge_one n
  have h₂ : N ≥ 2 := Nat.le_add_of_sub_le h₁
  have ⟨p, ⟨hp_dvd, hp_prime⟩⟩ : ∃ p, p ∣ N ∧ Prime p := hd h₂
  by_cases h : p ≤ n
  .
    have h₃ : p ≥ 2 := prime_ge_two hp_prime
    have h₄ : p ≥ 1 := Nat.one_le_of_lt h₃
    have h₅ : p ∣ fact n := fact_div ⟨h₄, h⟩
    have h₆ : p ∣ N - fact n := Nat.dvd_sub hp_dvd h₅
    have h₇ : N - fact n = 1 := Nat.add_sub_self_left (fact n) 1
    have h₈ : p ∣ 1 := h₇ ▸ h₆
    have h₉ : p = 1 := Nat.eq_one_of_dvd_one h₈
    have hn1 : ¬(p = 1) := Nat.ne_of_lt' h₃
    exact absurd h₉ hn1
  .
    exact ⟨p, ⟨Nat.lt_of_not_le h, hp_prime⟩⟩
