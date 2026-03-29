import Proofs.EvenOdd

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
