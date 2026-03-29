import Proofs.Primes

def Even (n : Nat) := ∃k, n = 2 * k
def Odd (n : Nat) := ∃k, n = 2 * k + 1

theorem even_or_odd (n : Nat) : Even n ∨ Odd n := by
  induction n with
    | zero => exact Or.inl ⟨0, Eq.symm (Nat.mul_zero 2)⟩
    | succ n' ih =>
        rcases ih with hl | hr
        .
          have ⟨w, hw⟩ := hl
          exact Or.inr ⟨w, Nat.add_left_inj.mpr hw⟩
        .
          have ⟨w, hw⟩ := hr
          have hsucc : n' + 1 = 2*(w + 1) := by omega
          exact Or.inl ⟨w + 1, hsucc⟩

theorem not_odd_even {n : Nat} (h : ¬(Odd n)) : Even n :=
  Or.resolve_right (even_or_odd n) h

theorem even_and_odd_false {n : Nat} : ¬(Even n ∧ Odd n) := by
  intro h
  have ⟨w₁, hw₁⟩ := h.left
  have ⟨w₂, hw₂⟩ := h.right
  have h₂ : 2*n = 2*(w₁ + w₂) + 1 := by omega
  have h₃ : 2*(n - (w₁ + w₂)) = 1 := by omega
  have h₃ : 2 ∣ 1 := by omega
  contradiction

/-- if n^2 is even, then n is even -/
theorem sq_of_even_even {n : Nat} (hn2_even : Even (n^2)) : Even n := by
  by_cases h : Odd n
  .
    have ⟨w, hw⟩ := h
    have h₁ : n^2 = 4*w^2 + 4*w + 1 := by grind
    have h₂ : n^2 = 2*(2*w^2 + 2*w) + 1 := by omega
    have hn2_odd : Odd (n^2) := ⟨2*w^2 + 2*w, h₂⟩
    exact False.elim (even_and_odd_false ⟨hn2_even, hn2_odd⟩)
  .
    exact not_odd_even h

theorem gcd_of_evens_ge_two {a b : Nat} (ha : Even a) (hb : Even b) (hanz : a > 0) : Nat.gcd a b ≥ 2 := by
  have ⟨wa, hwa⟩ := ha
  have ⟨wb, hwb⟩ := hb
  have h₁ : (2 * wa).gcd (2 * wb) = 2 * wa.gcd wb := Nat.gcd_mul_left 2 wa wb
  have h₂ : a.gcd b = 2 * wa.gcd wb := by grind
  have hwanz : wa > 0 := by omega
  have h₃ : wa.gcd wb ≥ 1 := Nat.gcd_pos_of_pos_left wb hwanz
  omega

-- no (irreducible) pair of natural numbers a and b exists such that a/b = sqrt(2)
theorem sqrt2_irrational (a b : Nat) (hcp : Nat.Coprime a b) : a^2 ≠ 2*b^2 := by
  by_cases h : a^2 = 2*b^2
  .
    have ha2_even : Even (a^2) := ⟨b^2, h⟩
    have ha_even : Even a := sq_of_even_even ha2_even
    have ⟨w, hw⟩ := ha_even
    have ha2 : a^2 = 4*w^2 := by grind
    have hb2 : b^2 = 2*w^2 := by omega
    have hb2_even : Even (b^2) := ⟨w^2, hb2⟩
    have hb_even : Even b := sq_of_even_even hb2_even
    have hagtz : a > 0 := by grind -- using hcp
    have hgcdge2 : a.gcd b ≥ 2 := gcd_of_evens_ge_two ha_even hb_even hagtz
    have hgcde1 : a.gcd b = 1 := hcp
    omega
  .
    exact h
