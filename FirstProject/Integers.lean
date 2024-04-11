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
