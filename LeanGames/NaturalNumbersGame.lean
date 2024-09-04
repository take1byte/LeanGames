import Mathlib

/- ## Tutorial World -/

/- Prove that for all natural numbers x and q the following identity holds:
   37x + q = 37x + q -/
example (x q: ℕ) : 37 * x + q = 37 * x + q := by rfl
/- Explanation:
rfl stands for reflexivity. It is a tactic for closing equality goals such as A = B, where
the expressions on the two sides of the equals sign are equal or can be made equal by evaluation.
In this example, A = 37x + q and B = 37x + q are equal.

References:
* rfl tactic in mathlib4 tactic catalog:
  https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md#rfl
* rfl tactic description: https://course.ccs.neu.edu/cs2800sp23/ref.html
-/

/- Prove: If x and y are natural numbers, and y=x+7, then 2y=2(x+7) -/
example (x y: ℕ)(h: y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw[h]
/- Proof:
```
rw[h]
rfl
```
Explanation:
rw is a tactic for rewriting the goal using the arguments given to it.
In this example, the argument to rw is h: y = x + 7.  When we rewrite the goal 2y = 2(x + 7)
using h, the goal becomes 2(x + 7) = 2(x + 7), which is closed by rfl. According to mathlib4 docs
cited below, rw is the composition of rewrite tractic followed by rfl tactic. Note that the
game server requires an explicit rfl after rw to close the goal.

References:
* [rw](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md#rw)
-/

/- Prove: 2 is the number after the number after 0 -/
example (two_eq_succ_one : 2 = Nat.succ 1): 2 = Nat.succ (Nat.succ 0) := by
  rw[two_eq_succ_one]
/- Proof 1:
```
rw[two_eq_succ_one]
rw[one_eq_succ_zero]
rfl
```

Explanation: After the first rewrite, the goal becomes Nat.succ 1 = Nat.succ (Nat.succ 0). After
the second rewrite, the goal becomes Nat.succ (Nat.succ 0) = Nat.succ (Nat.succ 0), which is
closed by rfl. In lean, the goal can be closed by rfl even without two_eq_succ_one, which is why a
single application of rw closes the goal.
-/

/- Proof 2:
```
rw[← one_eq_succ_zero]
rw[← two_eq_succ_one]
rfl
```

Explanation: If h: A = B, then rw[← h] rewrites B's into A's. In our example, after the first
rewrite the goal becomes 2 = Nat.succ 1. After the second rewrite, the goal becomes 2 = 2,
which is closed by rfl.
-/

/- Prove: a+(b+0)+(c+0)=a+b+c -/
example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[add_zero]
  rw[add_zero]
/- Proof:
```
rw[add_zero]
rw[add_zero]
rfl
```

Explanation: The first rw transforms the goal to a + b + (c + 0) = a + b + c. The second rw
transforms the goal to a + b + c = a + b + c, which is then closed by rfl.
-/

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[add_zero c]
  rw[add_zero]

/- Proof:
```
rw[add_zero c]
rw[add_zero]
rfl
```

Explanation: rw[add_zero] rewrites the first occurence of x + 0 into x. rw[add_zero c] rewrites
c + 0 into c and is called precision rewriting.
-/

/- Prove: For all natural numbers a, we have succ(a) = a + 1. -/
theorem succ_eq_add_one (n) (one_eq_succ_zero: 1 = Nat.succ 0) : Nat.succ n = n + 1 := by
  nth_rewrite 1 [← Nat.add_zero n]
  rewrite[← Nat.add_succ n 0]
  rewrite[← one_eq_succ_zero]
  rfl
/- Proof:
```
nth_rewrite 1 [← add_zero n]
rw[← add_succ]
rw[← one_eq_succ_zero]
rfl
```
Explanation: one_eq_succ_zero is a stated as an assumption because Nat.one_eq_succ_zero
[is deprecated in Lean 4](https://github.com/leanprover-community/mathlib4/blob/91d155587e2c92d55afb8565687863555bfc300c/Mathlib/Init/Data/Nat/Lemmas.lean#L42-L43).
nth_rewrite tactic with argument 1 rewrites the first occurence of n into n + 0.
-/

/- Prove: 2 + 2 = 4. -/
example (one_eq_succ_zero: 1 = Nat.succ 0)
        (two_eq_succ_one: 2 = Nat.succ 1)
        (three_eq_succ_two: 3 = Nat.succ 2)
        (four_eq_succ_three: 4 = Nat.succ 3): (2 : ℕ) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rewrite[Nat.add_succ]
  rewrite[one_eq_succ_zero]
  rewrite[Nat.add_succ]
  rewrite[Nat.add_zero]
  rewrite[← three_eq_succ_two]
  rewrite[← four_eq_succ_three]
  rfl
/- Proof:
```
nth_rewrite 2 [two_eq_succ_one]
rw[add_succ]
rw[one_eq_succ_zero]
rw[add_succ]
rw[add_zero]
rw[← three_eq_succ_two]
rw[← four_eq_succ_three]
rfl
```

Explanation: We use rewrite instead of rw because rw in Lean 4 completes the goal, and therefore,
doesn't allow us to show the steps of the proof. We include the four lemmas as arguments to example
because these lemmas are available in the game.
-/

/- ## Addition World -/
/- Prove: For all natural numbers n, we have 0 + n = n. -/
theorem _zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rw[Nat.add_zero]
  | succ n ih =>
    rw[Nat.add_succ, ih]
/- Proof:
```
induction n with d hd
rw[add_zero]
rfl
rw[add_succ]
rw[hd]
rfl
```

Explanation: Theorem name is _zero_add instead of zero_add because zero_add is a similar and
more general theorem in Mathlib. Our Lean 4 proof uses pattern matching syntax for induction
and the server proof uses the notation that doesn't highlight the base case and the inductive step.
-/
