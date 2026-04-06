theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
-- Use the induction tactic to turn the theorem
-- into a base case and an induction hypothesis
induction c with d ih
rw [add_zero, add_zero]
rfl
rw [add_succ]
rw [add_succ]
rw [add_succ] 
rw [ih]
rfl
