import FirstProject.Naturals

inductive Integer where
  |nat_to_pos : Natural → Integer
  |nat_to_neg : Natural → Integer
  deriving Repr

namespace Integer

def zero := nat_to_pos (Natural.zero)

def succ : Integer → Integer
  |nat_to_pos n => nat_to_pos (Natural.succ n)
  |nat_to_neg (Natural.succ n) => nat_to_neg n
  |nat_to_neg Natural.zero => zero

def pred : Integer → Integer
  |nat_to_pos (Natural.succ n) => nat_to_pos n
  |nat_to_pos (Natural.zero) => nat_to_neg (Natural.zero)
  |nat_to_neg n => nat_to_neg (Natural.succ n)

theorem pred_succ (a : Integer) : pred (succ a) = a := by
  cases a
  rfl
  rename_i d
  cases d
  rfl
  rfl

theorem succ_pred (a : Integer) : succ (pred a) = a := by
  cases a
  rename_i d
  cases d
  rfl
  rfl
  rfl

theorem succ_to_pred (a b : Integer) (h : a = succ b) : b = pred a := by
  calc b
    _ = pred (succ b) := by rw [pred_succ]
    _ = pred a        := by rw [h]

theorem pred_to_succ (a b : Integer) (h : a = pred b) : b = succ a := by
  calc b
    _ = succ (pred b) := by rw [succ_pred]
    _ = succ a        := by rw [h]

theorem succ_inj (a b : Integer) (h : succ a = succ b) : a = b := by
  calc a
  _ = pred (succ a) := by rw [pred_succ]
  _ = pred (succ b) := by rw [h]
  _ = b             := by rw [pred_succ]

theorem pred_inj (a b : Integer) (h : pred a = pred b) : a = b := by
  calc a
    _ = succ (pred a) := by rw [succ_pred]
    _ = succ (pred b) := by rw [h]
    _ = b             := by rw [succ_pred]


def add : Integer → Integer → Integer
  |nat_to_pos a, nat_to_pos b => nat_to_pos (a + b)
  |nat_to_neg a, nat_to_neg b => pred (nat_to_neg (a + b))
  |nat_to_pos a, nat_to_neg (Natural.succ b) => pred (add (nat_to_pos a) (nat_to_neg b))
  |nat_to_pos a, nat_to_neg (Natural.zero) => pred (nat_to_pos a)
  |nat_to_neg a, nat_to_pos (Natural.succ b) => succ (add (nat_to_neg a) (nat_to_pos b))
  |nat_to_neg a, nat_to_pos (Natural.zero) => nat_to_neg a

infixl:65 " + " => add
--notation " 0 " => zero

def one := succ zero
def two := succ one

theorem succ_eq_add_one (a : Integer) : succ a = a + one := by
  cases a
  rfl
  rfl

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
