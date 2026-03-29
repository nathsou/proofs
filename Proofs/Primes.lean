import Proofs.EvenOdd

/-- A number n is prime if n ≥ 2 and n is only divisible by 1 and itself -/
def Prime (n : Nat) : Prop := n > 1 ∧ ∀k, k ∣ n → (k = 1 ∨ k = n)

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

theorem composite_mpr {n : Nat} : (n ≤ 1 ∨ ∃k, k ∣ n ∧ k ≠ 1 ∧ k ≠ n) → ¬(Prime n) := by
  intro hp
  have h₁ : ¬(¬(n ≤ 1) ∧ ¬(∃k, k ∣ n ∧ k ≠ 1 ∧ k ≠ n)) := by grind
  have h₂ : ¬(n > 1 ∧ (∀k, k ∣ n → (k = 1 ∨ k = n))) := by grind
  exact h₂

theorem composite_iff {n : Nat} : ¬(Prime n) ↔ (n ≤ 1 ∨ ∃k, k ∣ n ∧ k ≠ 1 ∧ k ≠ n) :=
  ⟨composite_mp, composite_mpr⟩

theorem composite_mp' {n : Nat} : ¬(Prime n) → (n ≤ 1 ∨ ∃k, k ∣ n ∧ k > 1 ∧ k < n) := by
  intro hnp
  have h₁ : n ≤ 1 ∨ ∃k, k ∣ n ∧ k ≠ 1 ∧ k ≠ n := composite_mp hnp
  by_cases hpos : n > 0
  . rcases h₁ with hl | hr
    . exact Or.inl hl
    . have ⟨k, ⟨h_k_dvd_n, ⟨h_k_ne_1, h_k_ne_n⟩⟩⟩ := hr
      have h_k_nz : k ≠ 0 := by grind [Nat.zero_dvd]
      have h_k_gt_1 : k > 1 := by grind
      have h_k_lt_n : k < n := by
        have h_k_le_n : k ≤ n := Nat.le_of_dvd hpos h_k_dvd_n
        grind
      exact Or.inr ⟨k, ⟨h_k_dvd_n, ⟨h_k_gt_1, h_k_lt_n⟩⟩⟩
  . exact Or.inl (show n ≤ 1 by omega)

theorem prime_ge_two {p : Nat} (hp : Prime p) : p ≥ 2 := hp.1

theorem prime_gt_two_odd {p : Nat} (hgt2 : p > 2) (hp : Prime p) : Odd p := by
  by_cases h : Even p
  . have ⟨w, hw⟩ := h
    have h2dvd : 2 ∣ p := by omega
    have hne : ∃k, k ∣ p ∧ k ≠ 1 ∧ k ≠ p := ⟨2, ⟨h2dvd, ⟨by decide, by omega⟩⟩⟩
    have hnp : ¬(Prime p) := composite_mpr (Or.inr hne)
    exact absurd hp hnp
  . exact not_even_odd h

theorem prime_even_eq_two {p : Nat} {he : Even p} (hp : Prime p) : p = 2 := by
  by_cases h : p = 2
  . exact h
  . have hge2 : p ≥ 2 := prime_ge_two hp
    have hgt2 : p > 2 := by omega
    have hpodd : Odd p := prime_gt_two_odd hgt2 hp
    have heo : Even p ∧ Odd p := ⟨he, hpodd⟩
    exact False.elim (even_and_odd_false heo)

theorem exists_prime_dvd {n : Nat} (hn1 : n ≥ 2) : ∃p, p ∣ n ∧ Prime p := by
  by_cases h : Prime n
  . have h₁ : n ∣ n := Nat.dvd_refl n
    exact ⟨n, ⟨h₁, h⟩⟩
  . rcases composite_mp h with hl | hr
    . have h₂ : 1 < 1 := Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hn1) hl
      contradiction
    . have ⟨k, hk_dvd, hk1, hkn⟩ := hr
      have h₂ : n > 0 := Nat.zero_lt_of_lt hn1
      have h₃ : k ≤ n := Nat.le_of_dvd h₂ hk_dvd
      have h₄ : k < n := Nat.lt_of_le_of_ne h₃ hkn
      have h₅ : k > 0 := Nat.pos_of_dvd_of_pos hk_dvd h₂
      have h₆ : k > 1 := Nat.lt_of_le_of_ne h₅ (id (Ne.symm hk1))
      have ⟨p, hp_dvd, hp'⟩ := exists_prime_dvd h₆
      have hp_dvd_n : p ∣ n := Nat.dvd_trans hp_dvd hk_dvd
      exact ⟨p, ⟨hp_dvd_n, hp'⟩⟩

def fact (n : Nat) : Nat :=
  match n with
    | 0 => 1
    | n' + 1 => (n' + 1) * (fact n')

/-- The factorial of n is divisible by all natural numbers in [1, n] -/
theorem fact_dvd {n m : Nat} : m ≥ 1 ∧ m <= n → m ∣ fact n := by
  intro ⟨hm, hmn⟩
  induction n with
    | zero =>
      have h₁ : 1 ≤ 0 := Nat.le_trans hm hmn
      contradiction
    | succ n' ih =>
      unfold fact
      rcases Nat.eq_or_lt_of_le hmn with hl | hr
      . subst hl
        exact Nat.dvd_mul_right (n' + 1) (fact n')
      . have h₁ : m ≤ n' := Nat.le_of_lt_succ hr
        have h₂ : m ∣ fact n' := ih h₁
        exact Nat.dvd_mul_left_of_dvd h₂ (n' + 1)

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
  have h₁ : fact n ≥ 1 := fact_ge_one n
  have h₂ : N ≥ 2 := Nat.le_add_of_sub_le h₁
  have ⟨p, ⟨hp_dvd, hp_prime⟩⟩ : ∃p, p ∣ N ∧ Prime p := exists_prime_dvd h₂
  by_cases h : p ≤ n
  . have h₃ : p ≥ 2 := prime_ge_two hp_prime
    have h₄ : p ≥ 1 := Nat.one_le_of_lt h₃
    have h₅ : p ∣ fact n := fact_dvd ⟨h₄, h⟩
    have h₆ : p ∣ N - fact n := Nat.dvd_sub hp_dvd h₅
    have h₇ : N - fact n = 1 := Nat.add_sub_self_left (fact n) 1
    have h₈ : p ∣ 1 := h₇ ▸ h₆
    have h₉ : p = 1 := Nat.eq_one_of_dvd_one h₈
    have hn1 : ¬(p = 1) := Nat.ne_of_lt' h₃
    exact absurd h₉ hn1
  . exact ⟨p, ⟨Nat.lt_of_not_le h, hp_prime⟩⟩

def prod (lst : List Nat) : Nat := lst.foldl (fun n acc => n * acc) 1

theorem mul_gt_one_rel {a b n : Nat} (hnz : n ≠ 0) (h_a_gt_1 : a > 1) (h_n_eq_ab : n = a * b) : b < n := by
  have h_b_pos : b > 0 := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · simp [hb] at h_n_eq_ab
      exact absurd h_n_eq_ab hnz
    · exact hb
  subst h_n_eq_ab
  have h₁ : 2 * b ≤ a * b := Nat.mul_le_mul_right b (by omega)
  omega

private theorem foldl_mul_init (init : Nat) (l : List Nat) :
    l.foldl (fun n acc => n * acc) init = init * l.foldl (fun n acc => n * acc) 1 := by
  induction l generalizing init with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, Nat.one_mul]
    rw [ih (init * h), ih h, Nat.mul_assoc]

theorem prod_concat {l1 l2 : List Nat} {p1 p2 : Nat} (hp1 : p1 = prod l1) (hp2 : p2 = prod l2) : p1 * p2 = prod (l1 ++ l2) := by
  subst hp1; subst hp2
  unfold prod
  rw [List.foldl_append]
  exact (foldl_mul_init _ l2).symm

/-- Existence part of the fundamental theorem of arithmetic
All natural numbers greater than 1 can be factorised as a product of prime numbers
-/
theorem exists_prime_factorisation {n : Nat} (hngt1 : n > 1) : ∃(l : List Nat), (∀p ∈ l, Prime p) ∧ n = prod l := by
  by_cases h : Prime n
  . let l := [n]
    have h₁ : ∀p ∈ l, Prime p := by grind
    have h₂ : n = prod l := by unfold prod List.foldl; simp
    exact ⟨l, ⟨h₁, h₂⟩⟩
  . rcases composite_mp' h with hl | hr
    . omega
    . have ⟨a, ⟨h_a_dvd_n, ⟨h_a_gt_1, h_a_lt_n⟩⟩⟩ := hr
      have ⟨b, h_ab⟩ := h_a_dvd_n
      have h_b_gt_1 : b > 1 := by grind [Nat.mul_ne_zero_iff.mp]
      have h_b_dvd_n : b ∣ n := ⟨a, by grind⟩
      have h_n_pos : 0 < n := by omega
      have h_b_le_n : b ≤ n := Nat.le_of_dvd h_n_pos h_b_dvd_n
      have h_b_lt_n : b < n := mul_gt_one_rel (by omega) h_a_gt_1 h_ab
      have ih_a := exists_prime_factorisation h_a_gt_1
      have ih_b := exists_prime_factorisation h_b_gt_1
      have ⟨lst_a, ⟨lst_a_primes, h_lst_a_prod⟩⟩ := ih_a
      have ⟨lst_b, ⟨lst_b_primes, h_lst_b_prod⟩⟩ := ih_b
      let l := lst_a ++ lst_b
      have h_l_primes : ∀p ∈ l, Prime p := by grind
      have h_l_prod_eq_n : n = prod l := (prod_concat h_lst_a_prod h_lst_b_prod) ▸ h_ab
      exact ⟨l, ⟨h_l_primes, h_l_prod_eq_n⟩⟩
