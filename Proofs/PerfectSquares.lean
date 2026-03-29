
def PerfectSquare (n : Nat) : Prop := ∃k, n = k^2

example : PerfectSquare 49 := ⟨7, show 49 = 7^2 by decide⟩

theorem pow2_monotonic {a b : Nat} : (a^2 > b^2) → a > b :=
  have h₁ : b^2 ≤ a^2 → b ≤ a := (Nat.pow_le_pow_iff_left (show 2 ≠ 0 by decide)).mp
  by grind

theorem between_perfect_squares {n m : Nat} (h_bounds : m > n^2 ∧ m < (n + 1)^2) : ¬(PerfectSquare m) := by
  apply Classical.byContradiction
  intro h
  have ⟨hgt, hlt⟩ := h_bounds
  have ⟨k, hk⟩ : PerfectSquare m := Classical.not_not.mp h
  have h_k2_gt_m2 : k^2 > n^2 := Nat.lt_of_lt_of_eq hgt hk
  have h_k_gt_m : k > n := pow2_monotonic h_k2_gt_m2
  have h_k2_lt_succ_n2 : k^2 < (n + 1)^2 := lt_of_eq_of_lt (id (Eq.symm hk)) hlt
  have k_lt_succ_n : k < n + 1 := pow2_monotonic h_k2_lt_succ_n2
  grind

example : ¬(PerfectSquare 2) :=
  between_perfect_squares ⟨show 2 > 1^2 by decide, show 2 < 2^2 by decide⟩
