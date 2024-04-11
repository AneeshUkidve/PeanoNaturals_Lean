inductive NatNum where
  |zero : NatNum
  |succ (a : NatNum) : NatNum
  deriving Repr

namespace NatNum

theorem zero_ne_succ (a : NatNum) : zero ≠ succ a := by
  simp
theorem succ_inj (h : succ a = succ b) : a = b := by
  simp at h
  exact h

def inverse : Integer → Integer
  |nat_to_pos a => succ (nat_to_neg a)
  |nat_to_neg a => succ (nat_to_pos a)

theorem inv_zero : inverse zero = zero := by rfl

theorem pred_eq_add_inv_one (a : Integer) : pred a = a + inverse one := by
  cases a
  rename_i a
  apply Eq.symm
  calc
    _ = nat_to_pos a + inverse (nat_to_pos (Natural.succ Natural.zero)) := by rfl
    _ = nat_to_pos a + succ (nat_to_neg (Natural.succ Natural.zero)) := by rfl
    _ = nat_to_pos a + nat_to_neg Natural.zero := by rfl
    _ = pred (nat_to_pos a) := by rfl

  rename_i d
  apply Eq.symm
  calc
    _ = nat_to_neg d + inverse (nat_to_pos (Natural.succ Natural.zero)) := by rfl
    _ = nat_to_neg d + succ (nat_to_neg (Natural.succ Natural.zero)) := by rfl
    _ = nat_to_neg d + nat_to_neg Natural.zero := by rfl
    _ = pred (nat_to_neg (d + Natural.zero)) := by rfl
    _ = pred (nat_to_neg d) := by rfl

theorem add_inv (a : Integer) : a + inverse a = zero := by
  cases a
  rename_i a
  calc
    _ = nat_to_pos a + succ (nat_to_neg a) := by rfl
    _ = nat_to_pos a + nat_to_neg a + one := by rw [succ_eq_add_one]
    _ =

theorem inv_linear (a b : Integer) : inverse a + inverse b = inverse (a + b) := by
  cases b
  rename_i b
  induction b with
  |zero =>
    calc
      _ = inverse a + zero  := by rfl
      _ = inverse a         := by rw [add_zero]

--theorem inv_succ (a : Integer) : inverse (succ a) = pred (inverse a) := by


/-
theorem inv_inv (a : Integer) : inverse (inverse a) = a := by
  cases a
  rename_i d
  calc inverse (inverse (nat_to_pos d))
    _ = inverse (succ (nat_to_neg d)) := by rfl
    _ = inverse (nat_to_neg) := by sorry
  sorry
-/
