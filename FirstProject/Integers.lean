import FirstProject.Naturals

inductive Integer where
  |nat_to_pos : Natural → Integer
  |nat_to_neg : Natural → Integer
  deriving Repr

/- Two Copies of Natural are defined to make up the Integer
One copy corrresponds to the non-negative Integers
While the other corresponds to the negative Integers-/

-- ... ,  3,  2,  1,  0,  0,  1,  2,  3, ...  (Two Naturals)
--        ↓   ↓   ↓   ↓   ↓   ↓   ↓   ↓
-- ... , -4, -3, -2, -1,  0,  1,  2,  3, ...   (Integers)


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

/-Proof that the succ function is Injective-/
theorem succ_inj (a b : Integer) (h : succ a = succ b) : a = b := by
  calc a
  _ = pred (succ a) := by rw [pred_succ]
  _ = pred (succ b) := by rw [h]
  _ = b             := by rw [pred_succ]

/-Proof that the pred function is Injective-/
theorem pred_inj (a b : Integer) (h : pred a = pred b) : a = b := by
  calc a
    _ = succ (pred a) := by rw [succ_pred]
    _ = succ (pred b) := by rw [h]
    _ = b             := by rw [succ_pred]

theorem succ_pos_eq_succ (a : Natural) : nat_to_pos (Natural.succ a) = succ (nat_to_pos a) := by rfl

theorem pred_neg_eq_succ (a : Natural) : nat_to_neg (Natural.succ a) = pred (nat_to_neg a) := by rfl

def add : Integer → Integer → Integer
  |nat_to_pos a, nat_to_pos b => nat_to_pos (a + b)
  |nat_to_neg a, nat_to_neg b => pred (nat_to_neg (a + b))
  |nat_to_pos a, nat_to_neg (Natural.succ b) => pred (add (nat_to_pos a) (nat_to_neg b))
  |nat_to_pos a, nat_to_neg (Natural.zero) => pred (nat_to_pos a)
  |nat_to_neg a, nat_to_pos (Natural.succ b) => succ (add (nat_to_neg a) (nat_to_pos b))
  |nat_to_neg a, nat_to_pos (Natural.zero) => nat_to_neg a

infixl:65 " + " => add

def one := succ zero
def two := succ one

theorem add_zero (a : Integer) : a + zero = a := by
  cases a
  rfl
  rfl

/-Proof that the succ function is equivalent to adding one -/
theorem succ_eq_add_one (a : Integer) : succ a = a + one := by
  cases a
  rfl
  rfl

/-Proof that the pred function is equivalent to adding negative one -/
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

/-Proof that succ function splits over addition to the right-/
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

/-Proof that succ function splits over addition to the left-/
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

/-Proof that addition is Commutative-/
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

/-Proof that pred function splits over addition to the right-/
theorem add_pred (a b : Integer) : a + pred b = pred (a + b) := by
  let c := pred a
  have h : c = pred a := by rfl
  have hac : a = succ c := by exact pred_to_succ c a h
  rw [hac, succ_add, succ_add, pred_succ, ←add_succ, succ_pred]

/-Proof that pred function splits over addition to the left-/
theorem pred_add (a b : Integer) : pred a + b = pred (a + b) := by
  rw [add_comm, add_pred, add_comm]

/-Proof that addition is associative-/
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

/-Lemma to prove that a + inverse a = zero -/
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

/-Lemma to prove that a + inverse a = zero -/
theorem add_inverse_2 (a : Natural) : nat_to_neg a + inverse (nat_to_neg a) = zero := by
  simp [inverse, add_succ]
  rw [add_comm, ←add_succ]
  have h : succ (nat_to_neg a) = inverse (nat_to_pos a) := by rfl
  rw [h]
  exact add_inverse_1 a

/-Proof that a + inverse a = zero -/
theorem add_inv (a : Integer) : a + inverse a = zero := by
  cases a
  rename_i a
  exact add_inverse_1 a
  rename_i a
  exact add_inverse_2 a

theorem inv_add (a : Integer) : inverse a + a = zero := by
  rw [add_comm, add_inv]

theorem right_add (a b c : Integer) (h : a = b) : a + c = b + c := by
  rw [h]

theorem left_add (a b c : Integer) (h : a = b) : c + a = c + b := by
  rw [h]

/-Proof of right cancelation of addition-/
theorem right_cancel (a b c : Integer) (h : a + c = b + c) : a = b := by
  have h1 : a + c + (inverse c) = b + c + (inverse c) := by rw [h]
  simp [add_assoc, add_inv, add_zero] at h1
  exact h1

/-Proof of left cancelation of addition-/
theorem left_cancel (a b c : Integer) (h : c + a = c + b) : a = b := by
  simp [add_comm] at h
  exact (right_cancel a b c h)

def mul : Integer → Integer → Integer
  |nat_to_pos a, nat_to_pos b                 => nat_to_pos (a * b)
  |nat_to_neg _, nat_to_pos Natural.zero      => zero
  |nat_to_neg a, nat_to_pos (Natural.succ b)  => mul (nat_to_neg a) (nat_to_pos b) + nat_to_neg a

  |nat_to_pos a, nat_to_neg Natural.zero      => succ (nat_to_neg a)
  |nat_to_pos a, nat_to_neg (Natural.succ b)  => mul (nat_to_pos a) (nat_to_neg b) + succ (nat_to_neg a)

  |nat_to_neg a, nat_to_neg b                 =>nat_to_pos (Natural.succ a * Natural.succ b)

infixl:70 " * " => mul

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

/-neg_one = inverse one = nat_to_neg Natural.zero-/
theorem neg_one_eq_neg_zero : neg_one = nat_to_neg Natural.zero := by rfl

/-Proof that inverse function is same as multiplying by neg_one-/
theorem inv_eq_mul_neg_one (a : Integer) : inverse a = a * neg_one := by
  cases a
  rfl
  simp [inverse]
  rw [neg_one, one, zero]
  simp [succ, inverse, mul]
  rw [←Natural.one, Natural.mul_one]

/-Proof that inverse (inverse a) = a-/
theorem inv_inv (a : Integer) : inverse (inverse a) = a := by
  have h : inverse (inverse a) + inverse a = a + inverse a := by simp [add_inv, inv_add]
  exact right_cancel (inverse (inverse a)) a (inverse a) h

prefix:75  "-"   => inverse

/-Proof that inverse is a linear function-/
theorem inv_lin (a b : Integer) : -a + -b = -(a + b) := by
  have h : -a + -b + (a + b) = -(a + b) + (a + b) := by
    simp [inv_add]
    rw [add_comm (-a), add_assoc, ←add_assoc (-a), inv_add, zero_add, inv_add]
  exact right_cancel (-a + -b) (-(a + b)) (a + b) h

/-Describes how multiplaction takes place w.r.t succ-/
theorem mul_succ (a b : Integer) : a * succ b = (a * b) + a := by
  cases a
  rename_i apos
  induction apos with
  |zero =>
    rw [←zero]
    simp [zero_mul, add_zero]
  |succ d hd =>
    cases b
    rename_i bpos
    simp [succ, mul, Natural.succ_mul, Natural.mul_succ, hd, add]

    rename_i bneg
    cases bneg

    simp [succ, mul_zero]
    rw [←neg_one_eq_neg_zero, ←inv_eq_mul_neg_one, inv_add]

    rename_i bN
    simp [mul, succ]
    apply Eq.symm
    calc
      _ = nat_to_pos (Natural.succ d) * nat_to_neg bN + nat_to_neg d + succ (nat_to_pos d) := by simp [succ]
      _ = nat_to_pos (Natural.succ d) * nat_to_neg bN + nat_to_neg d + -(nat_to_neg d) := by simp [inverse]
      _ = nat_to_pos (Natural.succ d) * nat_to_neg bN := by rw [add_assoc, add_inv (nat_to_neg d), add_zero]
  rename_i aneg
  induction aneg with
  |zero =>
    cases b
    rename_i b
    simp [succ, mul]
    rename_i b
    cases b
    simp [succ, mul_zero]
    rw [←neg_one_eq_neg_zero, ←inv_eq_mul_neg_one, inv_add]
    rename_i bN
    simp [succ, mul]
    rw [←Natural.one, Natural.one_mul, Natural.one_mul, ←pred_eq_add_neg_one]
    simp [pred]
  |succ d hd =>
    cases b
    simp [succ, mul]
    rename_i bN
    cases bN
    simp [succ, mul_zero]
    rw [←neg_one_eq_neg_zero, ←inv_eq_mul_neg_one, inv_add]
    rename_i bN
    simp [succ, mul, Natural.mul_succ, Natural.succ_mul]
    apply Eq.symm
    calc
      _ = nat_to_pos (d * bN + bN + bN + Natural.succ (Natural.succ d)) + nat_to_pos (Natural.succ (Natural.succ d)) +
    nat_to_neg (Natural.succ d) := by simp [add]
      _ = nat_to_pos (d * bN + bN + bN + Natural.succ (Natural.succ d)) + succ (nat_to_pos (Natural.succ d)) +
    nat_to_neg (Natural.succ d) := by simp [succ]
      _ = nat_to_pos (d * bN + bN + bN + Natural.succ (Natural.succ d)) + -(nat_to_neg (Natural.succ d)) +
    nat_to_neg (Natural.succ d) := by simp [inverse]
      _ = nat_to_pos (d * bN + bN + bN + Natural.succ (Natural.succ d)) := by simp [add_assoc, inv_add, add_zero]

/-Proof that inverse funtion splits over multiplication to the left-/
theorem inv_mul (a b : Integer) : -a * b = -(a * b) := by
  cases b
  rename_i b
  induction b with
  |zero =>
    rw [←zero, mul_zero, mul_zero, inv_zero]
  |succ d hd =>
    cases a
    rename_i a
    simp [inverse, mul]
    cases a
    simp [Natural.zero_mul, succ, zero_mul]
    rename_i e
    simp [Natural.mul_succ, Natural.add_succ, succ]
    calc
      _ = nat_to_neg e * succ (nat_to_pos d) := by simp [succ]
      _ = nat_to_neg e * nat_to_pos d + nat_to_neg e := by rw [mul_succ]
      _ = succ (nat_to_neg (Natural.succ e)) * nat_to_pos d + nat_to_neg e := by simp [succ]
      _ = -nat_to_pos (Natural.succ e) * nat_to_pos d + nat_to_neg e := by simp [inverse]
      _ = -(nat_to_pos (Natural.succ e) * nat_to_pos d) + nat_to_neg e := by rw [hd]
      _ = -(nat_to_pos (Natural.succ e * d)) + nat_to_neg e := by simp [mul]
      _ = succ (nat_to_neg (Natural.succ e * d)) + nat_to_neg e := by simp [inverse]
      _ = succ (nat_to_neg (Natural.succ e * d) + nat_to_neg e) := by rw [succ_add]
      _ = succ (pred (nat_to_neg (Natural.succ e * d + e))) := by simp [add]
      _ = nat_to_neg (Natural.succ e * d + e) := by rw [succ_pred]

    rename_i a
    simp [mul]
    calc
      _ = -nat_to_neg a * succ (nat_to_pos d) := by simp [succ]
      _ = -nat_to_neg a * nat_to_pos d + -nat_to_neg a := by rw [mul_succ]
      _ = -(nat_to_neg a * nat_to_pos d) + -nat_to_neg a := by rw [hd]
      _ = -(nat_to_neg a * nat_to_pos d + nat_to_neg a) := by rw [inv_lin]

  rename_i b
  induction b with
  |zero =>
    rw [←neg_one_eq_neg_zero, ←inv_eq_mul_neg_one, ←inv_eq_mul_neg_one]
  |succ d hd =>
    cases a
    rename_i a
    apply Eq.symm
    calc
      _ = -(nat_to_pos a * nat_to_neg d + succ (nat_to_neg a)) := by simp [mul]
      _ = -(nat_to_pos a * nat_to_neg d) + -succ (nat_to_neg a) := by rw [inv_lin]
      _ = -nat_to_pos a * nat_to_neg d + -(-nat_to_pos a) := by rw [Eq.symm hd, inverse]
      _ = -nat_to_pos a * nat_to_neg d + nat_to_pos a := by rw [inv_inv]
    simp [inverse]
    cases a
    simp [succ, zero_mul, zero_add]
    rfl
    rename_i a
    simp [succ, mul, add, Natural.mul_succ]

    rename_i a
    calc
      _ = succ (nat_to_pos a) * nat_to_neg (Natural.succ d) := by simp [inverse]
      _ = nat_to_pos (Natural.succ a) * nat_to_neg (Natural.succ d) := by simp [succ]
      _ = nat_to_pos (Natural.succ a) * nat_to_neg d + succ (nat_to_neg (Natural.succ a)) := by simp [mul]
      _ = succ (nat_to_pos a) * nat_to_neg d + succ (nat_to_neg (Natural.succ a)) := by simp [succ]
      _ = -nat_to_neg a * nat_to_neg d + -nat_to_pos (Natural.succ a) := by simp [inverse]
      _ = -(nat_to_neg a * nat_to_neg d) + -nat_to_pos (Natural.succ a) := by rw [hd]
      _ = -(nat_to_pos (Natural.succ a * Natural.succ d) + nat_to_pos (Natural.succ a)) := by simp [mul, inv_lin]
      _ = -(nat_to_pos (Natural.succ a * Natural.succ d + Natural.succ a)) := by simp [add]
      _ = -(nat_to_pos (Natural.succ a * Natural.succ (Natural.succ d))) := by simp [Natural.mul_succ]
      _ = -(nat_to_neg a * nat_to_neg (Natural.succ d)) := by simp [mul]

/-Proof that inverse funtion splits over multiplication to the right-/
theorem mul_inv (a b : Integer) : a * -b = -(a * b) := by
  cases b
  cases a
  rename_i b a
  induction b with
  |zero =>
    rfl
  |succ d hd =>
    simp [mul, inverse, mul_succ, Natural.mul_succ]
    calc
      _ = nat_to_pos a * nat_to_neg d + -(nat_to_pos a) + nat_to_pos a := by simp [inverse]
      _ = nat_to_pos a * nat_to_neg d := by rw [add_assoc, inv_add (nat_to_pos a), add_zero]
    apply Eq.symm
    calc
      _ = -nat_to_pos (a * d + a) := by simp [inverse]
      _ = -(nat_to_pos (a * d) + nat_to_pos a) := by simp [add]
      _ = -(nat_to_pos a * nat_to_pos d + nat_to_pos a) := by simp [mul]
      _ = nat_to_pos a * -nat_to_pos d + -nat_to_pos a := by rw [←inv_lin, hd]
      _ = nat_to_pos a * succ (nat_to_neg d) + -nat_to_pos a := by simp [inverse]
      _ = nat_to_pos a * nat_to_neg d + nat_to_pos a + -nat_to_pos a := by rw [mul_succ]
      _ = nat_to_pos a * nat_to_neg d := by rw [add_assoc, add_inv (nat_to_pos a), add_zero]

  rename_i b a
  rw [←inv_mul]; simp [inverse, mul, mul_succ]
  simp [succ, mul, Natural.mul_succ]
  calc
    _ = nat_to_pos (Natural.succ a * b) + nat_to_pos (Natural.succ a) + nat_to_neg a := by simp [add]
    _ = nat_to_pos (Natural.succ a * b) + succ (nat_to_pos a) + nat_to_neg a := by simp [succ]
    _ = nat_to_pos (Natural.succ a * b) + -nat_to_neg a + nat_to_neg a := by simp [inverse]
    _ = nat_to_pos (Natural.succ a * b) := by rw [add_assoc, inv_add, add_zero]

  cases a
  rename_i b a
  calc
    _ = nat_to_pos a * succ (nat_to_pos b) := by simp [inverse]
    _ = nat_to_pos (a * b + a) := by simp [mul_succ, mul, add]
    _ = nat_to_pos (a * Natural.succ b) := by simp [Natural.mul_succ]
  cases a
  rw [←zero]; simp [Natural.zero_mul, Natural.add_zero, zero_mul, inv_zero]
  rw [zero]
  rename_i d
  calc
    _ = nat_to_neg d * nat_to_neg b := by simp [mul]
    _ = -(-nat_to_neg d) * nat_to_neg b := by simp [inv_inv]
    _ = -(succ (nat_to_pos d)) * nat_to_neg b := by simp [inverse]
    _ = -(nat_to_pos (Natural.succ d) * nat_to_neg b) := by simp [inv_mul, succ]

  rename_i b a
  calc
    _ = nat_to_neg a * succ (nat_to_pos b) := by simp [inverse]
    _ = nat_to_neg a * nat_to_pos b + nat_to_neg a := by simp [mul_succ]
  apply Eq.symm
  calc
    _ = -(nat_to_pos (Natural.succ a * Natural.succ b)) := by simp [mul]
    _ = succ (nat_to_neg (a * Natural.succ b + Natural.succ b)) := by simp [inverse, Natural.succ_mul]
    _ = succ (nat_to_neg (a * b + a + Natural.succ b)) := by simp [Natural.mul_succ]
    _ = succ (nat_to_neg (Natural.succ (a * b + a + b))) := by simp [Natural.add_succ]
    _ = nat_to_neg (a * b + a + b) := by simp [succ]
    _ = nat_to_neg (a * b + b + a) := by rw [←Natural.add_assoc, Natural.add_comm a, Natural.add_assoc]
    _ = succ (pred (nat_to_neg (a * b + b + a))) := by rw [succ_pred]
    _ = succ (nat_to_neg (a * b + b) + nat_to_neg a) := by simp [add]
    _ = succ (nat_to_neg (Natural.succ a * b)) + nat_to_neg a := by simp [succ_add, Natural.succ_mul]
    _ = -nat_to_pos (Natural.succ a * b) + nat_to_neg a := by simp [inverse]
    _ = -(nat_to_pos (Natural.succ a) * nat_to_pos b) + nat_to_neg a := by simp [mul]
    _ = -nat_to_pos (Natural.succ a) * nat_to_pos b + nat_to_neg  a := by simp [inv_mul]
    _ = succ (nat_to_neg (Natural.succ a)) * nat_to_pos b + nat_to_neg a := by simp [inverse]
    _ = nat_to_neg a * nat_to_pos b + nat_to_neg a := by simp [succ]


/-Proof that the inverse function is injective-/
theorem inv_inj (a b : Integer) (h : -a = -b) : a = b := by
  rw [←inv_inv a, h, inv_inv]

/-Proof that multiplication distributes over addition from the right-/
theorem add_mul (a b c : Integer) : (b + c) * a = (b * a) + (c * a) := by
  cases a
  rename_i a
  induction a with
  |zero =>
    rw [←zero]
    simp [mul_zero, add_zero]
  |succ d hd =>
    simp [succ_pos_eq_succ, mul_succ]
    rw [hd]
    rw [add_assoc, add_comm (c * nat_to_pos d), add_assoc, add_comm c, add_assoc]

  rename_i a
  induction a with
  |zero =>
    simp [←neg_one_eq_neg_zero, ←inv_eq_mul_neg_one, inv_lin]
  |succ d hd =>
    calc
      _ = -(-((b + c) * nat_to_neg (Natural.succ d))) := by rw [inv_inv]
      _ = -((b + c) * -nat_to_neg (Natural.succ d)) := by rw [mul_inv]
      _ = -((b + c) * succ (nat_to_pos (Natural.succ d))) := by simp [inverse]
      _ = -((b + c) * nat_to_pos (Natural.succ d) + (b + c)) := by rw [mul_succ]
      _ = -((b + c) * nat_to_pos (Natural.succ d)) + -(b + c) := by rw [inv_lin]
      _ = (b + c) * -nat_to_pos (Natural.succ d) + -(b + c) := by rw [←mul_inv]
      _ = (b + c) * succ (nat_to_neg (Natural.succ d)) + -(b + c) := by simp [inverse]
      _ = (b + c) * nat_to_neg d + -(b + c) := by simp [succ]
      _ = b * nat_to_neg d + c * nat_to_neg d + (-b + -c) := by rw [hd, ←inv_lin]
      _ = (b * nat_to_neg d + -b) + (c * nat_to_neg d + -c) := by rw [add_assoc, ←add_assoc (c * nat_to_neg d), add_comm (c * nat_to_neg d), add_assoc (-b), ←add_assoc (b * nat_to_neg d)]
      _ = (b * succ (nat_to_neg (Natural.succ d)) + -b) + (c * succ (nat_to_neg (Natural.succ d)) + -c) := by simp [succ]
      _ = (b * -nat_to_pos (Natural.succ d) + -b) + (c * -nat_to_pos (Natural.succ d) + -c) := by simp [inverse]
      _ = (-(b * nat_to_pos (Natural.succ d)) + -b) + (-(c * nat_to_pos (Natural.succ d)) + -c) := by simp [mul_inv]
      _ = (-(b * nat_to_pos (Natural.succ d) + b)) + (-(c * nat_to_pos (Natural.succ d) + c)) := by simp [inv_lin]
      _ = (-(b * succ (nat_to_pos (Natural.succ d)))) + (-(c * succ (nat_to_pos (Natural.succ d)))) := by simp [mul_succ]
      _ = (-(b * -nat_to_neg (Natural.succ d))) + (-(c * -nat_to_neg (Natural.succ d))) := by simp [inverse]
      _ = (-(-(b * nat_to_neg (Natural.succ d)))) + (-(-(c * nat_to_neg (Natural.succ d)))) := by simp [mul_inv]
      _ = (b * nat_to_neg (Natural.succ d)) + (c * nat_to_neg (Natural.succ d)) := by simp [inv_inv]

theorem succ_mul (a b : Integer) : succ a * b = a * b + b := by
  rw [succ_eq_add_one, add_mul, one_mul]

theorem inv_succ (a : Integer) : -(succ a) = pred (-a) := by
  rw [succ_eq_add_one, ←inv_lin, ←neg_one, pred_eq_add_neg_one, neg_one_eq_neg_zero]

theorem inv_pred (a : Integer) : -(pred a) = succ (-a) := by
  rw [←inv_inv (succ (-a)), inv_succ, inv_inv]

theorem mul_pred (a b : Integer) : a * pred b = a * b + -a := by
  rw [←inv_inv (a * pred b), ←mul_inv, inv_pred, mul_succ, ←inv_lin, ←mul_inv, inv_inv]

theorem pred_mul (a b : Integer) : pred a * b = a * b + -b := by
  rw [pred_eq_add_neg_one, add_mul, ←neg_one_eq_neg_zero, neg_one, inv_mul, one_mul]

/-Proof that multiplication distributes over addition from the left-/
theorem mul_add (a b c : Integer) : a * (b + c) = a * b + a * c := by
  cases a
  rename_i a
  induction a with
  |zero =>
    rw [←zero]
    simp [zero_mul, add_zero]
  |succ d hd =>
    simp [succ_pos_eq_succ, succ_mul, hd]
    rw [add_assoc, add_comm (nat_to_pos d * c), add_assoc, ←add_assoc (nat_to_pos d * b), add_comm c]

  rename_i a
  induction a with
  |zero =>
    rw [←neg_one_eq_neg_zero, neg_one]
    simp [inv_mul, inv_lin, one_mul]
  |succ d hd =>
    simp [pred_neg_eq_succ, pred_mul, hd]
    rw [←inv_lin]
    rw [add_assoc, add_comm (nat_to_neg d * c), add_assoc, ←add_assoc (nat_to_neg d * b), add_comm (-c)]

/-Proof that multiplication is commutative-/
theorem mul_comm (a b : Integer) : a * b = b * a := by
  cases a
  rename_i a
  induction a with
  |zero =>
    rw [←zero ,zero_mul, mul_zero]
  |succ d hd =>
    rw [succ_pos_eq_succ, mul_succ, succ_mul, hd]

  rename_i a
  induction a with
  |zero =>
    rw [←neg_one_eq_neg_zero, neg_one, inv_mul, mul_inv, mul_one, one_mul]
  |succ d hd =>
    rw [pred_neg_eq_succ, mul_pred, pred_mul, hd]

/-Proof that multiplication is associative-/
theorem mul_assoc (a b c : Integer) : (a * b) * c = a * (b * c) := by
  cases a
  rename_i a
  induction a with
  |zero =>
    rw [←zero]
    simp [zero_mul]
  |succ d hd =>
    rw [succ_pos_eq_succ, succ_mul, succ_mul, add_mul, hd]

  rename_i a
  induction a with
  |zero =>
    rw [←neg_one_eq_neg_zero, neg_one]
    simp [inv_mul, one_mul]
  |succ d hd =>
    rw [pred_neg_eq_succ]
    simp [pred_mul, add_mul, hd, inv_mul]

/-Type Integer forms a commutative ring with unity :) -/
