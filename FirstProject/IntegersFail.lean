import FirstProject.Naturals

inductive integer where
|zero : integer
|succ (n : integer) : integer
|pred (n : integer) : integer

namespace integer

def cast_int : natnum → integer
  |natnum.zero => integer.zero
  |natnum.succ a => integer.succ (cast_int a)

axiom succ_inj (a b : integer) (h: succ a = succ b) : a = b

axiom pred_inj (a b : integer) (h: pred a = pred b) : a = b

axiom pred_succ (a : integer) : pred (succ a) = a

theorem zero_map_zero : cast_int natnum.zero = zero := by rfl

theorem succ_map_succ : cast_int (natnum.succ a) = succ (cast_int a) := by rfl

theorem succ_pred (a : integer) : succ (pred a) = a := by
  let b := pred a
  have h : b = pred a := by rfl
  have h1 : b = pred (succ (pred a)) := by
    rewrite [←h]
    exact Eq.symm (pred_succ b)
  rewrite [h] at h1
  apply Eq.symm (pred_inj a (succ (pred a)) h1)

def one := succ zero
def two := succ one

def add : integer → integer → integer
  |a, zero => a
  |a, succ b => succ (add a b)
  |a, pred b => pred (add a b)

infixl:65 " + " => add

theorem add_zero (a : integer) : a + zero = a := by rfl
theorem add_succ (a b : integer) : a + succ b = succ (a + b) := by rfl
theorem add_pred (a b : integer) : a + pred b = pred (a + b) := by rfl

/-Proof that addition in the naturals is preserved by inclusion map-/
theorem add_same (a b : natnum) : cast_int (a + b) = cast_int a + cast_int b := by
  induction b with
  |zero =>
    rw [natnum.add_zero, zero_map_zero, add_zero]
  |succ d hd =>
    rewrite [natnum.add_succ]
    repeat rewrite [succ_map_succ]
    rewrite [hd]
    rw [add_succ]

theorem zero_add (a : integer) : zero + a = a := by
  induction a with
  |zero =>
    exact add_zero zero
  |succ d hd =>
    rw [add_succ, hd]
  |pred d hd =>
    rw [add_pred, hd]

theorem succ_add (a b : integer) : succ a + b = succ (a + b) := by
  induction b with
  |zero =>
    repeat rw [add_zero]
  |succ d hd =>
    repeat rewrite [add_succ]
    rw [hd]
  |pred d hd =>
    repeat rewrite [add_pred]
    rw [hd, pred_succ, succ_pred]

theorem pred_add (a b : integer) : pred a + b = pred (a + b) := by
  induction b with
  |zero =>
    repeat rw [add_zero]
  |succ d hd =>
    repeat rewrite [add_succ]
    rw [hd, pred_succ, succ_pred]
  |pred d hd =>
    repeat rewrite [add_pred]
    rw [hd]

theorem pred_add_succ (a b : integer) : pred a + succ b = a + b := by
  rw [add_succ, pred_add, succ_pred]

theorem succ_to_pred (a b : integer) (h: a = succ b) : b = pred a := by
  rw [h, pred_succ]

theorem pred_to_succ (a b : integer) (h : a = pred b) : b = succ a := by
  rw [h, succ_pred]

/-Addition is commutative-/
theorem add_comm (a b : integer) : a + b = b + a := by
  induction b with
    |zero =>
      rw [add_zero, zero_add]
    |succ d hd =>
      rw [add_succ, succ_add, hd]
    |pred d hd =>
      rw [add_pred, pred_add, hd]

/-(a + 1) + (b - 1) = a + b-/
theorem succ_add_pred (a b : integer) : succ a + pred b = a + b := by
  rw [add_comm, pred_add_succ, add_comm]

/-Addition is Associtive-/
theorem add_assoc (a b c : integer): a + (b + c) = (a + b) + c := by
  induction a with
    |zero =>
      repeat rw [zero_add]
    |succ d hd =>
      repeat rewrite [succ_add]
      rw [hd]
    |pred d hd =>
      repeat rewrite [pred_add]
      rw [hd]

/-Additive inverse defined recursively -(a+1) = (-a-1) ∧ -(a-1) = (-a+1)  -/
def inverse : integer → integer
  |zero => zero
  |succ a => pred (inverse a)
  |pred a => succ (inverse a)

theorem inv_zero : inverse zero = zero := by rfl
theorem inv_succ : inverse (succ a) = pred (inverse a) := by rfl
theorem inv_pred : inverse (pred a) = succ (inverse a) := by rfl

/-Additive inverse property holds a + (-a) = zero ∀ a  -/
theorem add_inverse (a : integer) : a + inverse a = zero := by
  induction a with
  |zero =>
    rw [inv_zero, add_zero]
  |succ d hd =>
    rw [inv_succ, succ_add_pred, hd]
  |pred d hd =>
    rw [inv_pred, pred_add_succ, hd]

theorem inverse_add (a : integer) : inverse a + a = zero := by
  rw [add_comm, add_inverse]

/-Inverse is a linear operator-/
theorem inv_lin (a b : integer) : inverse (a + b) = inverse a + inverse b := by
  induction b with
  |zero =>
    simp [inv_zero, add_zero]
  |succ d hd =>
    rw [add_succ, inv_succ, inv_succ, add_pred, hd]
  |pred d hd =>
    rw [add_pred, inv_pred, inv_pred, add_succ, hd]

/-Either a natural number can be casted to a or it can be casted to its inverse-/
theorem totality (a : integer) : (∃ (n : natnum), a = cast_int n) ∨ (∃ (n : natnum), a = inverse (cast_int n)) := by
  induction a with
  |zero =>
    left
    exists natnum.zero
  |succ d hd =>
    cases hd
    rename_i hzp
    /-CASE 1: d natnum-/
    cases hzp
    rename_i m hm
    left
    exists natnum.succ m
    rewrite [hm]
    exact succ_map_succ

    /-CASE 2: inverse d natnum-/
    rename_i hn
    cases hn
    rename_i m hm
    cases m

    /-Subcase 2.1: d = zero-/
    rewrite [zero_map_zero, inv_zero] at hm
    left
    exists natnum.succ natnum.zero
    rw [hm, succ_map_succ, zero_map_zero]

    /-Subcase 2.2: d = succ m-/
    rename_i m
    rewrite [succ_map_succ, inv_succ] at hm
    right
    exists m
    rw [hm, succ_pred]

  |pred d hd =>
    cases hd
    rename_i hzp
    /-CASE 1: d natnum-/
    cases hzp
    rename_i m hm
    cases m

    /-Subcase 1.1: d = zero-/
    right
    exists natnum.succ natnum.zero
    rw [hm, succ_map_succ, zero_map_zero, inv_succ, inv_zero]

    /-Subcase 1.2: d = succ m-/
    rename_i m
    left
    exists m
    rw [hm, succ_map_succ, pred_succ]

    /-CASE 2: inverse d natnum-/
    rename_i hn
    cases hn
    rename_i m hm
    right
    exists natnum.succ m
    rw [hm, succ_map_succ, inv_succ]

/-Defining order on integers-/
def le : integer → integer → Prop
  |a, b => ∃ (c : natnum), a + cast_int c = b

infixl:65 " ≤ " => le

theorem le_succ (a : integer): a ≤ succ a := by
  exists natnum.one

theorem pred_le (a : integer): pred a ≤ a := by
  exists natnum.one
  rw [pred_add, natnum.one_eq_succ_zero, succ_map_succ, zero_map_zero, add_succ, pred_succ, add_zero]

/-The order we defined is a total order-/
theorem total_order (a : integer) : (zero ≤ a) ∨ (a ≤ zero) := by
  have h : (∃ (n : natnum), a = cast_int n) ∨ (∃ (n : natnum), a = inverse (cast_int n)) := by
    exact totality a
  cases h

  /-Case 1: a natural can be casted to a (i.e a is nonnegative)-/
  rename_i h1
  left
  cases h1
  rename_i m hm
  exists m
  rw [zero_add]
  exact Eq.symm hm

  /-Case 2: a natural can be cast to inverse a-/
  rename_i h2
  right
  cases h2
  rename_i m hm
  exists m
  rw [hm, inverse_add]

theorem succ_le_succ (a b : integer) (h: succ a ≤ succ b) : a ≤ b := by
  cases h
  rename_i m hm
  rewrite [succ_add] at hm
  exists m
  exact succ_inj (a + cast_int m) b hm

theorem pred_le_pred (a b : integer) (h: pred a ≤ pred b) : a ≤ b := by
  cases h
  rename_i m hm
  rewrite [pred_add] at hm
  exists m
  exact pred_inj (a + cast_int m) b hm

theorem right_cancel (a b c : integer) (h: a + c = b + c) : a = b := by
  induction c with
  |zero =>
    repeat rewrite [add_zero] at h
    exact h
  |succ d hd =>
    repeat rewrite [add_succ] at h
    exact hd (succ_inj (a + d) (b + d) h)
  |pred d hd =>
    repeat rewrite [add_pred] at h
    exact hd (pred_inj (a + d) (b + d) h)

theorem left_cancel (a b c : integer) (h: c + a = c + b) : a = b := by
  rewrite [add_comm c, add_comm c] at h
  exact right_cancel a b c h

/-inverse (inverse a) = a  ∀a -/
theorem inv_inv (a : integer) : inverse (inverse a) = a := by
  have h : (inverse (inverse a) + inverse a = a + inverse a) := by
    simp [add_inverse, inverse_add]
  exact right_cancel (inverse (inverse a)) a (inverse a) h


/-Defining Multiplication-/
def mul : integer → integer → integer
  |_, zero => zero
  |a, succ b => mul a b + a
  |a, pred b => mul a b + inverse a

infixl:65 " ⬝ " => mul

theorem mul_zero (a : integer) : a ⬝ zero = zero := by rfl
theorem mul_succ (a b : integer) : a ⬝ succ b = a ⬝ b + a := by rfl
theorem mul_pred (a b : integer) : a ⬝ pred b = a ⬝ b + inverse a := by rfl

theorem zero_mul (a : integer) : zero ⬝ a = zero := by
  induction a with
  |zero =>
    exact mul_zero zero
  |succ d hd =>
    rw [mul_succ, hd, add_zero]
  |pred d hd =>
    rw [mul_pred, hd, inv_zero, add_zero]

theorem succ_mul (a b : integer) : (succ a) ⬝ b = a ⬝ b + b := by
  induction b with
  |zero =>
    rw [mul_zero, mul_zero, add_zero]
  |succ d hd =>
    rw [mul_succ, mul_succ, hd, add_succ, add_succ, ←add_assoc, add_comm d, add_assoc]
  |pred d hd =>
    rw [mul_pred, mul_pred, hd, inv_succ ,add_pred,add_pred, ←add_assoc, add_comm d, add_assoc]

theorem pred_mul (a b : integer) : (pred a) ⬝ b = a ⬝ b + inverse b := by
  induction b with
  |zero =>
    rw [mul_zero, mul_zero, inv_zero, add_zero]
  |succ d hd =>
    rw [mul_succ, mul_succ, hd, inv_succ,add_pred, add_pred, ←add_assoc, add_comm (inverse d), add_assoc]
  |pred d hd =>
    rw [mul_pred, mul_pred, hd, inv_pred , inv_pred ,add_succ, add_succ, ←add_assoc, add_comm (inverse d), add_assoc]

theorem mul_one (a : integer) : a ⬝ one = a := by
  rw [one, mul_succ, mul_zero, zero_add]

theorem one_mul (a : integer) : one ⬝ a = a := by
  rw [one, succ_mul, zero_mul, zero_add]

/-Multipication is commutative-/
theorem mul_comm (a b : integer) : a ⬝ b = b ⬝ a := by
  induction b with
  |zero =>
    rw[mul_zero, zero_mul]
  |succ d hd =>
    simp [succ_mul, mul_succ, hd]
  |pred d hd =>
    simp [pred_mul, mul_pred, hd]

/-Multiplication is left-distributive-/
theorem mul_add (a b c : integer) : a ⬝ (b + c) = (a ⬝ b) + (a ⬝ c) := by
  induction a with
  |zero =>
    simp [zero_mul, add_zero]
  |succ d hd =>
    simp [succ_mul, hd, add_assoc, add_comm]
  |pred d hd =>
    simp [pred_mul, hd, add_assoc, add_comm, inv_lin]

/-Multiplication is right-distributive-/
theorem add_mul (a b c : integer) : (b + c) ⬝ a = (b ⬝ a) + (c ⬝ a) := by
  simp [mul_comm, mul_add]

/-inverse and multiplication are interchangable-/
theorem mul_inv (a b : integer) : a ⬝ inverse b = inverse (a ⬝ b) := by
  induction b with
  |zero =>
    simp [inv_zero, mul_zero]
  |succ d hd =>
    rw [mul_succ, inv_succ, mul_pred, hd, inv_lin]
  |pred d hd =>
    rw [mul_pred, inv_lin, inv_pred, mul_succ, hd, inv_inv]

theorem inv_mul (a b : integer) : inverse a ⬝ b  = inverse (a ⬝ b) := by
  simp [mul_comm, mul_inv]

/-Multiplication is Associative-/
theorem mul_assoc (a b c : integer) : (a ⬝ b) ⬝ c = a ⬝ (b ⬝ c) := by
  induction c with
  |zero =>
    simp [mul_zero]
  |succ d hd =>
    simp [mul_succ, hd, mul_add]
  |pred d hd =>
    simp [mul_pred, hd, mul_add, mul_inv]

/-inverse a = a ⬝ (inverse one) -/
theorem inv_eq_mul_inv_one : inverse a = a ⬝ inverse one := by
  rw [mul_inv, mul_one]

/-type integer forms a commutative ring-/

/-Inductive types come with a theorem that allows one term of the type to
be constructed Uniquely from the constructors

Since pred(succ 0) = 0 for this definition, this violates the theorem.

Along with the axiom pred_succ and this auto noConfusion theorem,
we can prove a contradiction.-/
