/- Peano Axioms implementation-/
inductive natnum where
| zero : natnum
| succ (n: natnum) : natnum

namespace natnum

axiom succ_inj (a b : natnum) (h: succ a = succ b) : a = b

axiom zero_ne_succ (a:natnum): zero ≠ succ a

/-Elementary results from axioms-/

def one:natnum := succ zero

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
