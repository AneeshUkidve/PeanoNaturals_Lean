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
