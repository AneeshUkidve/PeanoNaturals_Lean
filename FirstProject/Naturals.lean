/- Peano Axioms implementation-/
inductive natnum where
| zero : natnum
| succ (n: natnum) : natnum

namespace natnum

axiom succ_inj (a b : natnum) (h: succ a = succ b) : a = b

axiom zero_ne_succ (a:natnum): zero ≠ succ a

/-Elementary results from axioms-/

def one:natnum := succ zero

def two:natnum := succ one

theorem one_eq_succ_zero : one = succ zero := by
  rfl

theorem succ_ne_zero (a : natnum) : succ a ≠ zero := by
  exact Ne.symm (zero_ne_succ a)


/-Defining Addition-/

def add : natnum → natnum → natnum
  | m, zero => m
  | m, (succ n) => succ (add m n)


theorem add_zero : add m zero = m := by rfl

theorem add_succ : add m (succ n) = succ (add m n) := by rfl

theorem zero_add : add zero m = m := by
  induction m with
  |zero =>
    rw [add_zero]
  |succ d hd =>
    rw [add_succ, hd]

theorem succ_add (m n : natnum) : add (succ m) n = succ (add m n) := by
  induction n with
  |zero =>
    repeat rw [add_zero]
  |succ d hd =>
    rw [add_succ, add_succ, hd]

theorem add_comm (m n : natnum) : add m n = add n m := by
  induction n with
    |zero =>
      rw [add_zero, zero_add]
    |succ d hd =>
      rw [add_succ, succ_add, hd]

theorem add_assoc : add a (add b c) = add (add a b) c := by
  induction a with
    |zero =>
      repeat rw [zero_add]
    |succ d hd =>
      repeat rewrite [succ_add]
      rw [hd]

theorem pred_exists (a : natnum) (h : a ≠ zero) : ∃ (b : natnum), succ b = a := by
  cases a
  contradiction
  rename_i n
  exists n

infixl:65 " + " => add --overloading + with add

theorem right_cancel (a b c : natnum) (h: a + c = b + c) : a = b := by
  induction c with
  |zero =>
    repeat rewrite [add_zero] at h
    exact h
  |succ d hd =>
    repeat rewrite [add_succ] at h
    exact hd (succ_inj (a + d) (b + d) h)

theorem left_cancel (a b c : natnum) (h: c + a = c + b) : a = b := by
  rewrite [add_comm c, add_comm c] at h
  exact right_cancel a b c h


/-Defining Order-/

def le : natnum → natnum → Prop
  |m, n => ∃ c:natnum, m + c = n

infixl:65 " ≤ " => le --overloading ≤ with le

theorem zero_le (m:natnum) : zero ≤ m := by
  exists m
  rw[zero_add]

theorem succ_le_succ (h: succ m ≤ succ n) : m ≤ n := by
  cases h
  rename_i d h1
  rewrite [succ_add] at h1
  have h2 : m + d = n := by exact succ_inj (m+d) n h1
  exists d

theorem le_succ (m : natnum) : m ≤ succ m := by
  exists one

/-Defining Multiplaction-/

def mul : natnum → natnum → natnum
  |_, zero => zero
  |m, succ n => mul m n + m

infixl:65 " * " => mul --overloading * with mul

theorem mul_zero (m : natnum) : m * zero = zero := by rfl

theorem mul_succ (m n : natnum) : m * (succ n) = m * n + m := by rfl

theorem zero_mul (m : natnum) : zero * m = zero := by
  induction m with
  |zero =>
    exact mul_zero zero
  |succ d hd =>
    rw [mul_succ, hd, add_zero]

theorem succ_mul (m n : natnum) : (succ m) * n = m * n + n := by
  induction n with
  |zero =>
    simp [mul_zero, add_zero]
  |succ d hd =>
    simp [mul_succ, hd, add_succ, add_comm, add_assoc]

theorem mul_comm (m n : natnum) : m * n = n * m := by
  induction n with
  |zero =>
    simp [mul_zero, zero_mul]
  |succ d hd =>
    simp [mul_succ, succ_mul, hd]

theorem mul_add (a b c : natnum) : a * (b + c) = (a * c) + (a * b) := by
  induction a with
  |zero =>
    simp [zero_mul, zero_add]
  |succ d hd =>
    simp [succ_mul, hd, add_comm, add_assoc]

theorem add_mul (a b c : natnum) : (b + c) * a = (c * a) + (b * a) := by
  rewrite [mul_comm, mul_add]
  simp [mul_comm]

theorem mul_assoc (a b c : natnum) : (a * b) * c = a * (b * c) := by
  induction a with
  |zero =>
    simp [mul_zero, zero_mul]
  |succ d hd =>
    repeat rewrite [succ_mul]
    rewrite [add_mul]
    rw [hd, add_comm]

theorem mul_one (a : natnum) : a * one = a := by
  rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem one_mul (a : natnum) : one * a = a := by
  rw [mul_comm]
  exact mul_one a

/-Defining "divides"-/

def div : natnum → natnum → Prop
  |a, b => ∃(c:natnum), a * c = b -- a divides b (div a b) if ∃c s.t. a*c = b

theorem div_zero (a : natnum) : div a zero := by exists zero

theorem one_div (a : natnum) : div one a := by
  exists a
  rw [one_mul]

theorem div_self (a : natnum) : div a a := by
  exists one
  rw [mul_one]

end natnum
