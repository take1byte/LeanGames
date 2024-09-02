import Mathlib

/- Tutorial World -/

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
/- Solution:
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
/- Solution 1:
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

/- Solution 2:
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
/- Solution:
```
rw[add_zero]
rw[add_zero]
rfl
```

Explanation: The first rw transforms the goal to a + b + (c + 0) = a + b + c. The second rw
transforms the goal to a + b + c = a + b + c, which is then closed by rfl.
-/
