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

theorem add_zero (a : Integer) : a + zero = a := by
  cases a
  rfl
  rfl

theorem succ_eq_add_one (a : Integer) : succ a = a + one := by
  cases a
  rfl
  rfl

theorem pred_eq_add_neg_one (a : Integer) : pred a = a + nat_to_neg Natural.zero := by
  cases a
  rfl
  rfl

theorem zero_add (a : Integer) : zero + a = a := by
  cases a
  rename_i a
  calc
   _ = nat_to_pos Natural.zero + nat_to_pos a := by rw [zero]
   _ = nat_to_pos (Natural.zero + a)          := by simp [add]
   _ = nat_to_pos a                           := by rw [Natural.zero_add]

  rename_i a
  induction a with
  |zero =>
    rfl
  |succ d hd =>
    rewrite [zero, add, ←zero, hd]
    simp [pred]

theorem add_succ (a b : Integer) : a + succ b = succ (a + b) := by
  cases a
  cases b

  rename_i a b
  calc
    _ = nat_to_pos a + nat_to_pos (Natural.succ b) := by simp [succ]
    _ = nat_to_pos (a + Natural.succ b) := by simp [add]
    _ = nat_to_pos (Natural.succ (a + b)) := by rw [Natural.add_succ]
    _ = succ (nat_to_pos (a + b)) := by simp [succ]
    _ = succ (nat_to_pos a + nat_to_pos b) := by simp [add]

  rename_i a b
  cases b
  calc
    _ = nat_to_pos a + zero := by simp [succ]
    _ = nat_to_pos a := by rw [add_zero]
    _ = succ (pred (nat_to_pos a)) := by rw [succ_pred]
    _ = succ (nat_to_pos a + nat_to_neg Natural.zero) := by rw [pred_eq_add_neg_one]
  rename_i d
  calc
    _ = nat_to_pos a + nat_to_neg d := by simp [succ]
    _ = succ (pred (nat_to_pos a + nat_to_neg d)) := by rw [succ_pred]
    _ = succ (nat_to_pos a + (nat_to_neg (Natural.succ d))) := by simp [add]

  rename_i a
  cases b
  rename_i b
  cases b
  calc
    _ = nat_to_neg a + nat_to_pos (Natural.succ Natural.zero) := by simp [succ]
    _ = succ (nat_to_neg a + nat_to_pos Natural.zero) := by  simp [add]
  rename_i d
  calc
    _ = nat_to_neg a + nat_to_pos (Natural.succ (Natural.succ d)) := by simp [succ]
    _ = succ (nat_to_neg a + nat_to_pos (Natural.succ d)) := by simp [add]

  rename_i b
  cases b
  calc
    _ = nat_to_neg a := by simp [succ, add_zero]
    _ = succ (pred (nat_to_neg a)) := by rw [succ_pred]
    _ = succ (nat_to_neg a + nat_to_neg Natural.zero) := by rw [pred_eq_add_neg_one]

  rename_i d
  calc
    _ = pred (nat_to_neg (a + d)) := by simp [succ, add]
    _ = nat_to_neg (Natural.succ (a + d)) := by simp [pred]
    _ = nat_to_neg (a + Natural.succ d) := by rw [Natural.add_succ]
    _ = succ (pred (nat_to_neg (a + Natural.succ d))) := by rw [succ_pred]
    _ = succ (nat_to_neg a + nat_to_neg (Natural.succ d)) := by simp [add]


theorem succ_add (a b : Integer) : succ a + b = succ (a + b) := by
  cases a
  cases b

  rename_i a b
  calc
    _ = nat_to_pos (Natural.succ a) + nat_to_pos b := by simp [succ]
    _ = nat_to_pos (Natural.succ (a + b)) := by simp [add, Natural.succ_add]
    _ = succ (nat_to_pos a + nat_to_pos b) := by simp [succ, add]

  rename_i a b
  induction b with
  |zero =>
    calc
      _ = pred (succ (nat_to_pos a)) := by rw [pred_eq_add_neg_one]
      _ = succ (pred (nat_to_pos a)) := by rw [pred_succ, succ_pred]
      _ = succ (nat_to_pos a + nat_to_neg Natural.zero) := by rw [pred_eq_add_neg_one]
  |succ d hd =>
    calc
      _ = pred (succ (nat_to_pos a) + nat_to_neg d) := by simp [succ, add]
      _ = pred (succ (nat_to_pos a + nat_to_neg d)) := by rw [hd]
      _ = succ (pred (nat_to_pos a + nat_to_neg d)) := by rw [pred_succ, succ_pred]
      _ = succ (nat_to_pos a + nat_to_neg (Natural.succ d)) := by simp [add]

  cases b
  rename_i a b
  induction b with
  |zero =>
    rewrite [←zero]
    simp [add_zero]
  |succ d hd =>
    calc
      _ = succ (nat_to_neg a) + succ (nat_to_pos d) := by simp [succ]
      _ = succ (succ (nat_to_neg a) + nat_to_pos d) := by rw [add_succ]
      _ = succ (succ (nat_to_neg a + nat_to_pos d)) := by rw [hd]
      _ = succ (nat_to_neg a + succ (nat_to_pos d)) := by rw [add_succ]
      _ = succ (nat_to_neg a + (nat_to_pos (Natural.succ d))) := by simp [succ]

  rename_i a b
  cases a
  calc
    _ = nat_to_neg b := by simp[succ, zero_add]
    _ = succ (pred (nat_to_neg (Natural.zero + b))) := by rw[succ_pred, Natural.zero_add]
    _ = succ (nat_to_neg Natural.zero + nat_to_neg b) := by simp [add]

  rename_i d
  calc
    _ = nat_to_neg d + nat_to_neg b := by simp [succ]
    _ = pred (nat_to_neg (d + b)) := by simp [add]
    _ = nat_to_neg (Natural.succ (d + b)) := by simp [pred]
    _ = succ (pred (nat_to_neg (Natural.succ d + b))) := by simp [Natural.succ_add, succ_pred]
    _ = succ (nat_to_neg (Natural.succ d) + nat_to_neg b) := by simp [add]

theorem add_comm (a b : Integer) : a + b = b + a := by
  cases a
  rename_i a

  cases b
  rename_i b
  simp [add, Natural.add_comm]

  rename_i b
  induction b with
  |zero =>
    apply succ_inj
    rw [←add_succ, ←succ_add]
    simp [succ, add_zero, zero_add]
  |succ d hd =>
    rewrite [add, hd]
    calc
      _ = pred (succ (nat_to_neg (Natural.succ d)) + nat_to_pos a) := by simp [succ]
      _ = pred (succ (nat_to_neg (Natural.succ d) + nat_to_pos a)) := by rw [succ_add]
      _ = nat_to_neg (Natural.succ d) + nat_to_pos a := by rw [pred_succ]

  rename_i a
  cases b

  rename_i b
  induction b with
  |zero =>
    rw [←zero, zero_add, add_zero]
  |succ d hd =>
    calc
      _ = nat_to_neg a + succ (nat_to_pos d) := by simp [succ]
      _ = succ (nat_to_neg a + nat_to_pos d) := by rw [add_succ]
      _ = succ (nat_to_pos d + nat_to_neg a) := by rw [hd]
      _ = succ (nat_to_pos d) + nat_to_neg a := by rw [succ_add]
      _ = nat_to_pos (Natural.succ d) + nat_to_neg a := by simp [succ]

  rename_i b
  simp [add, Natural.add_comm]

theorem add_pred (a b : Integer) : a + pred b = pred (a + b) := by
  let c := pred a
  have h : c = pred a := by rfl
  have hac : a = succ c := by exact pred_to_succ c a h
  rw [hac, succ_add, succ_add, pred_succ, ←add_succ, succ_pred]

theorem pred_add (a b : Integer) : pred a + b = pred (a + b) := by
  rw [add_comm, add_pred, add_comm]

theorem add_assoc (a b c : Integer) : a + b + c = a + (b + c) := by
  cases a
  rename_i a
  induction a with
  |zero =>
    rw [←zero, zero_add, zero_add]
  |succ d hd =>
    calc
      _ = succ (nat_to_pos d) + b + c := by simp [succ]
      _ = succ (nat_to_pos d + b + c) := by simp [succ_add]
      _ = succ (nat_to_pos d + (b + c)) := by rw [hd]
      _ = succ (nat_to_pos d) + (b + c) := by simp [succ_add]
      _ = nat_to_pos (Natural.succ d) + (b + c) := by simp [succ]

  rename_i a
  induction a with
  |zero =>
    rewrite [add_comm (nat_to_neg Natural.zero), add_comm (nat_to_neg Natural.zero)]
    rw [←pred_eq_add_neg_one, ←pred_eq_add_neg_one, pred_add]
  |succ d hd =>
    calc
      _ = pred (nat_to_neg d) + b + c := by simp [pred]
      _ = pred (nat_to_neg d) + (b + c) := by rw [pred_add, pred_add, hd, ←pred_add]
      _ = nat_to_neg (Natural.succ d) + (b + c) := by simp [pred]

def inverse : Integer → Integer
  |nat_to_pos a => succ (nat_to_neg a)
  |nat_to_neg a => succ (nat_to_pos a)

theorem inv_zero : inverse zero = zero := by rfl

theorem add_inverse_1 (a : Natural) : nat_to_pos a + inverse (nat_to_pos a) = zero := by
  induction a with
  |zero =>
    rfl
  |succ d hd =>
    calc
      _ = succ (nat_to_pos d) + succ (nat_to_neg (Natural.succ d)) := by simp [succ, inverse]
      _ = succ (nat_to_pos d) + succ (pred (nat_to_neg d)) := by simp [pred]
      _ = succ (nat_to_pos d + pred (succ (nat_to_neg d))) := by rw [succ_pred, pred_succ, succ_add]
      _ = succ (pred (nat_to_pos d + inverse (nat_to_pos d))) := by simp [inverse, add_pred]
      _ = zero := by rw [hd, succ_pred]

theorem add_inverse_2 (a : Natural) : nat_to_neg a + inverse (nat_to_neg a) = zero := by
  simp [inverse, add_succ]
  rw [add_comm, ←add_succ]
  have h : succ (nat_to_neg a) = inverse (nat_to_pos a) := by rfl
  rw [h]
  exact add_inverse_1 a

theorem add_inv (a : Integer) : a + inverse a = zero := by
  cases a
  rename_i a
  exact add_inverse_1 a
  rename_i a
  exact add_inverse_2 a

theorem inv_add (a : Integer) : inverse a + a = zero := by
  rw [add_comm, add_inv]

def mul : Integer → Integer → Integer
  |nat_to_pos a, nat_to_pos b                 => nat_to_pos (a * b)
  |nat_to_neg _, nat_to_pos Natural.zero      => zero
  |nat_to_neg a, nat_to_pos (Natural.succ b)  => mul (nat_to_neg a) (nat_to_pos b) + nat_to_neg a

  |nat_to_pos a, nat_to_neg Natural.zero      => succ (nat_to_neg a)
  |nat_to_pos a, nat_to_neg (Natural.succ b)  => mul (nat_to_pos a) (nat_to_neg b) + succ (nat_to_neg a)

  |nat_to_neg a, nat_to_neg b                 =>nat_to_pos (Natural.succ a * Natural.succ b)

infixl:65 " * " => mul

theorem mul_zero (a : Integer) : a * zero = zero := by cases a; rfl; rfl

theorem zero_mul (a : Integer) : zero * a = zero := by
  cases a
  simp [zero, mul, Natural.zero_mul]

  rename_i a
  induction a with
  |zero =>
    rfl
  |succ d hd =>
    simp [zero, mul]
    rw [←zero, hd]
    simp [succ, zero_add]

theorem mul_one (a : Integer) : a * one = a := by
  cases a
  simp [one, zero, succ, mul]
  rw [←Natural.one, Natural.mul_one]

  rename_i a
  simp [one, zero, succ, mul]
  rw [←zero, zero_add]

theorem one_mul (a : Integer) : one * a = a := by
  cases a
  simp [one, zero, succ, mul]
  rw [←Natural.one, Natural.one_mul]

  rename_i a
  simp [one, zero, succ]
  cases a
  rfl
  simp [mul]
  rename_i a
  calc
    _ = succ (nat_to_pos Natural.zero) * nat_to_neg a + succ (pred (nat_to_neg Natural.zero)) := by simp [succ, pred]
    _ = nat_to_neg a + nat_to_neg Natural.zero := by rw [←zero, ←one, one_mul, succ_pred]
    _ = pred (nat_to_neg a) := by rw [pred_eq_add_neg_one]
    _ = nat_to_neg (Natural.succ a) := by simp [pred]

def neg_one := inverse one

theorem neg_one_eq_neg_zero : neg_one = nat_to_neg Natural.zero := by rfl

theorem inv_eq_mul_neg_one (a : Integer) : inverse a = a * neg_one := sorry
