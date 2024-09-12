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

/- Prove: For all natural numbers a,b, we have succ(a) + b = succ(a + b). -/
theorem succ_add (a : Nat) (b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rw [Nat.add_zero (Nat.succ a), Nat.add_zero a]
  | succ b ih =>
    rw [Nat.add_succ (Nat.succ a) b, ih, Nat.add_succ]

/- Proof:
```
induction b with b ih
rw[add_zero]
rw[add_zero]
rfl
rw[add_succ (succ a) b]
rw[ih]
rw[add_succ]
rfl
```

Explanation: The first step is to decide whether to pursue induction on a or induction on b.

First, let's consider induction on a.
The base case requres us to prove succ 0 + b = succ (0 + b) using only add_succ, add_zero, and
zero_add. This means proving 1 + b = b + 1. We could try proving this by induction on b.
Base Case: 1 + 0 = 0 + 1
Inductive Hypothesis: 1 + b = b + 1
Inductive Step: 1 + (b + 1) = (b + 1) + 1
add_succ 1 b + 1 gives us 1 + (b + 1) = (1 + b) + 1
ih gives us (1 + b) + 1 = (b + 1) + 1 and the proof of inductive step follows by rfl. This feels
like a lot of work just for the base case.

Therefore, let's consider induction on b instead.
The base case is (a + 1) + 0 = (a + 0) + 1. We apply add_zero (a + 1) and add_zero a to rewrite the
hypothesis into a + 1 = a + 1, which is proved by reflexivity.
The inductive hypothesis is succ a + b = succ (a + b), which is the same as
(a + 1) + b = (a + b) + 1, and can be thought of as ability to swap 1 + b and b + 1.
The inductive step requires us to prove that succ a + succ b = succ (a + succ b). We will rewrite
both sides into succ (succ (a + b)).
We first apply add_succ to (succ a) and b to rewrite succ a + succ b as succ (succ a + b).
We then apply the inductive hypothesis to rewrite succ (succ a + b) as succ (succ (a + b)).
Finally we apply add_succ to re-write succ (a + succ b) as succ (succ (a + b)). The proof
now follows by reflexivity.
-/

/- Prove: On the set of natural numbers, addition is commutative. In other words, if a and b
are arbitrary natural numbers, then a + b = b + a .-/
theorem _add_comm (a : Nat) (b: Nat) : a + b = b + a := by
  induction a with
  | zero => rw[Nat.zero_add, Nat.add_zero]
  | succ a ih =>
    rw[succ_add, ih, Nat.add_succ b a]

/- Proof:
```
induction a with d hd
rw [zero_add, add_zero]
rfl
rw [succ_add, hd, add_succ b d]
rfl
```

Explanation: The proof is by induction on a. The base case uses zero_add and add_zero to rewrite
(0 + b) and (b + 0) into b. The inductive step uses succ_add, add_succ, and the inductive hypothesis
to rewrite ((succ a) + b) and (b + succ a) into succ (b + a).
-/

/- Prove: On the set of natural numbers, addition is associative. In other words, if a, b and c
are arbitrary natural numbers, we have (a + b) + c = a + (b + c). -/
theorem _add_assoc (a : Nat) (b : Nat) (c : Nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => rw[Nat.zero_add, Nat.zero_add]
  | succ a ih =>
    rw[Nat.succ_add a (b + c), <-ih, <-Nat.succ_add (a + b) c, Nat.succ_add a b]

/- Proof:
```
induction a with a ih
rw[zero_add, zero_add]
rfl
rw[succ_add a (b + c)]
rw[<-ih]
rw[<-succ_add (a + b) c]
rw[succ_add a b]
rfl
```

Explanation: The proof is by induction on a. The base case is proven by applying zero_add tactic
to both left and right hand side of the goal. In the inductive step, we first transform the
right hand side into succ(a + b + c) using succ_add a (b + c) and the inductive hypothesis. We then
apply succ_add to both right hand side and left hand side to rewrite both into succ (a + b) + c.
-/

/- Prove: If a, b and c are arbitrary natural numbers, we have (a + b) + c = (a + c) + b. -/
theorem _add_right_comm (a : Nat) (b : Nat) (c : Nat) : (a + b) + c = (a + c) + b := by
  rw[add_assoc a b c, add_comm b c, <-add_assoc a c b]
/- Proof:
rw[add_assoc a b c, add_comm b c, <-add_assoc a c b]
rfl

Explanation: We first use associativity to rewrite the left hand side from (a + b) + c into
a + (b + c). We then use commutativity to rewrite a + (b + c) into a + (c + b). Finally we use
associativity again and the proof follows by reflexivity.
-/

/- ## Multiplication World -/

/- Multiplication world starts with two definitions:
mul_zero a := a * 0 = 0
mul_succ a b := a * Nat.succ b = a * b + b. -/

/- Prove:  For any natural number m, we have m * 1 = m. -/
theorem _mul_one (a : Nat) : a * 1 = a := by
  rw[<-Nat.zero_add 1, <-Nat.succ_eq_add_one 0]
  nth_rewrite 2 [<-Nat.zero_add a]
  nth_rewrite 2 [<- Nat.mul_zero a]
  rw [Nat.mul_succ]
/- Proof:
```
rw[<-zero_add 1]
rw[<-succ_eq_add_one 0]
nth_rewrite 2 [<-zero_add m]
nth_rewrite 2 [<-mul_zero m]
rw [mul_succ]
rfl
```

Explanation: The proof proceeds by rewriting both sides of the goal into m * 0 + m. To rewrite the
left hand side (lhs), we rewrite 1 = 0 + 1 = succ 0 and apply mul_succ tactic. To rewrite the right
hand side (rhs), we rewrite m = 0 + m and apply mul_zero in reverse to get m * 0 + m.
-/

/- Prove:  For all natural numbers m, we have 0 * m = 0. -/
theorem _zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with
  | zero => rw[Nat.mul_zero]
  | succ m ih => rw[Nat.mul_succ, ih, Nat.add_zero]

/- Proof:
```
induction m with m ih
rw[mul_zero]
rfl
rw[mul_succ]
rw[ih]
rw[add_zero]
rfl
```

Explanation: The proof is by induction on m. The base case follows from mul_zero. In the inductive
step we apply mul_succ to rewrite 0 * succ m into 0 * m + 0. We then apply the inductive hypothesis
and add_zero tactic to rewrite 0 * m + 0 into 0. We close the goal by reflexivity.
-/


/- Prove: For all natural numbers a and b, we have (succ a) * b = a * b + b. -/
theorem _succ_mul (a : Nat) (b : Nat) : Nat.succ a * b = a * b + b := by
  induction b with
  | zero => rw[Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  | succ b ih =>
    rw[Nat.mul_succ (Nat.succ a) b, ih]
    rw[Nat.mul_succ]
    rw[Nat.succ_eq_add_one a]
    rw[← Nat.succ_eq_add_one b]
    rw[Nat.add_assoc (a*b) a (b+1), ← Nat.add_assoc a b 1]
    rw[Nat.add_comm a b]
    rw[Nat.add_assoc b a 1]
    rw[Nat.add_assoc (a*b) b (a+1)]
/- Proof:
```
induction b with b ih
repeat rw [mul_zero]
rw[add_zero]
rfl
rw[mul_succ (succ a) b, ih]
nth_rewrite 1 [succ_eq_add_one]
rw [mul_succ]
rw [succ_eq_add_one]
rw [add_assoc (a*b) a (b+1)]
rw[<-add_assoc a b 1]
rw [add_comm a b]
rw [add_assoc (a*b) b (a+1)]
rw [<-add_assoc b a 1]
rfl
```

Explanation: The proof is by induction on b. The base case follows by applying mul_zero and
add_zero tactics. The inductive step uses mul_succ, add_assoc, add_comm, and succ_eq_add_one tactics
to rewrite both the lhs and the rhs into a * b + (b + a + 1). First, we apply mul_succ and the
inductive hypothesis to rewrite (succ a) * (succ b) into a * b + b + succ a, which we then rewrite
into a * b + b + (a + 1) using succ_eq_add_one tactic. Next, we apply mul_succ and succ_eq_add_one
to rewrite the rhs from (a * succ b + succ b) to  a * b + a + (b + 1). We then apply associativity
of addition tactics to both the rhs and lhs, rewrite a + b into b + a using add_comm on the rhs,
and apply add_assoc again to get a * b + (b + a + 1) on both sides. The proof is closed by rfl.
-/

/- Prove: Multiplication is commutative. -/
theorem _mul_comm (a : Nat) (b : Nat) : a * b = b * a := by
  induction b with
  | zero => rw [Nat.mul_zero, Nat.zero_mul]
  | succ b ih =>
    rw[Nat.mul_succ, Nat.succ_mul, ih]

/- Proof:
```
induction b with b ih
rw [mul_zero, zero_mul]
rfl
rw [mul_succ, succ_mul, ih]
rfl
```

Explanation: The proof is by induction on b. The base case is closed with mul_zero and zero_mul
tactics. The inductive step is closed by applying mul_succ on the lhs, succ_mul on the rhs, the
inductive hypothesis, and finally rfl.
-/

/- Template -/
/- Prove: -/
/- Proof:
```
```

Explanation:
-/
