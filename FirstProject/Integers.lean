import FirstProject.Naturals

inductive integer where
|zero : integer
|succ (n : integer) : integer
|pred (n : integer) : integer

namespace integer

def cor_int : natnum → integer
  |natnum.zero => integer.zero
  |natnum.succ a => integer.succ (cor_int a)

axiom succ_inj (a b : integer) (h: succ a = succ b) : a = b

axiom pred_inj (a b : integer) (h: pred a = pred b) : a = b

axiom pred_succ (a : integer) : pred (succ a) = a

theorem zero_map_zero : cor_int natnum.zero = zero := by rfl

theorem succ_map_succ : cor_int (natnum.succ a) = succ (cor_int a) := by rfl

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

theorem add_same (a b : natnum) : cor_int (a + b) = cor_int a + cor_int b := by
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

theorem add_comm (a b : integer) : a + b = b + a := by
  induction b with
    |zero =>
      rw [add_zero, zero_add]
    |succ d hd =>
      rw [add_succ, succ_add, hd]
    |pred d hd =>
      rw [add_pred, pred_add, hd]

theorem succ_add_pred (a b : integer) : succ a + pred b = a + b := by
  rw [add_comm, pred_add_succ, add_comm]

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

def inverse : integer → integer
  |zero => zero
  |succ a => pred (inverse a)
  |pred a => succ (inverse a)

theorem inv_zero : inverse zero = zero := by rfl
theorem inv_succ : inverse (succ a) = pred (inverse a) := by rfl
theorem inv_pred : inverse (pred a) = succ (inverse a) := by rfl

theorem add_inverse (a : integer) : a + inverse a = zero := by
  induction a with
  |zero =>
    rw [inv_zero, add_zero]
  |succ d hd =>
    rw [inv_succ, succ_add_pred, hd]
  |pred d hd =>
    rw [inv_pred, pred_add_succ, hd]

theorem totality (a : integer) : (∃ (n : natnum), a = cor_int n) ∨ (∃ (n : natnum), a = inverse (cor_int n)) := by
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
