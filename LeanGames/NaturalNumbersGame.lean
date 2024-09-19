import Mathlib.Tactic.NthRewrite
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.applyAt

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
  rw[Nat.add_zero]
  rw[Nat.add_zero]
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
  rw[Nat.add_zero c]
  rw[Nat.add_zero]

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
  rw[Nat.add_assoc a b c, Nat.add_comm b c, ← Nat.add_assoc a c b]
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

/- Prove: For any natural number m, we have 1 * m = m. -/
theorem _one_mul (one_eq_succ_zero: 1 = Nat.succ 0) (m : Nat) : 1 * m = m := by
  rw[one_eq_succ_zero, Nat.succ_mul, Nat.zero_mul, Nat.zero_add]

/- Proof:
```
rw [one_eq_succ_zero, succ_mul, zero_mul, zero_add]
rfl
```

Explanation: In Lean 4 proof, we include one_eq_succ_zero as an assumption because Nat.one_eq_succ_zero
has been deprecated and one_eq_succ_zero is available in the game server at this stage. The proof
starts by rewriting 1 on the lhs as succ 0 and applying succ_mul to rewrite (succ 0) * m into
0 * m + m. The proof is completed by applying zero_mul to rewrite 0 * m into 0, zero_add to
rewrite 0 + m into m, and rfl.
-/

/- Prove: For any natural number m, we have 2 * m = m + m. -/
theorem _two_mul (two_eq_succ_one : 2 = Nat.succ 1)(m : Nat) : 2 * m = m + m := by
  rw[two_eq_succ_one, Nat.succ_mul, Nat.one_mul]


/- Proof:
```
rw [two_eq_succ_one, succ_mul, one_mul]
rfl
```

Explanation: In Lean 4 proof, we include two_eq_succ_one as an assumption because it's not part of
mathlib and it's available at this stage of the game in the game server. To produce a proof, we
first rewrite 2 as succ 1. We then apply succ_mul to rewrite (succ 1) * m as
1 * m + m. Finally, we apply one_mul to rewrite 1 * m as m and complete the proof by rfl.
-/

/- Prove: Multiplication is distributive over addition on the left. In other words, for all
natural numbers a, b and c, we have a * (b + c) = a * b + a * c. -/
theorem _mul_add (a : Nat) (b : Nat) (c : Nat) : a * (b + c) = a * b + a * c:= by
  induction a with
  | zero => repeat rw[Nat.zero_mul]
  | succ a ih =>
    repeat rw[Nat.succ_mul]
    rw[ih]
    rw[Nat.add_assoc (a * b) b (a * c + c)]
    rw[<-Nat.add_assoc b (a * c) c]
    rw[Nat.add_comm b (a * c)]
    rw[Nat.add_assoc (a * c) b c]
    rw[<-Nat.add_assoc (a * b) (a * c) (b + c)]
/- Proof:
```
induction a with a ih
repeat rw[zero_mul]
rw[zero_add]
rfl
repeat rw[succ_mul]
rw[ih]
rw[add_assoc (a * b) b (a * c + c)]
rw[<-add_assoc b (a * c) c]
rw[add_comm b (a * c)]
rw[add_assoc (a * c) b c]
rw[<-add_assoc (a * b) (a * c) (b + c)]
rfl
```

Explanation: The proof is by induction on a. The base case is completed by repeated application of
zero_mul followed by zero_add and rfl. The inductive step starts with a repeated application of
succ_mul to rewrite the lhs into a * (b + c) + (b + c) and the rhs into a * b + b + (a * c + c). We
then apply the inductive hypothesis to rewrite the lhs into a * b + a * c + (b + c). The proof
concludes by applying associativity and commutativity of addition to rewrite both sides into
a * b + a * c + (b + c) and using rfl.
-/

/- Prove: Addition is distributive over multiplication. In other words, for all natural numbers
a, b and c, we have (a + b) * c = a * c + b * c. -/
theorem _add_mul (a : Nat) (b : Nat) (c : Nat) : (a + b) * c = a * c + b * c := by
  rw[Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]
/- Proof:
```
rw[mul_comm (a + b) c, mul_add, mul_comm c a, mul_comm c b]
rfl
```

Explanation: The proof uses commutativity of multiplication and distributivity of multiplication over
addition. First we rewrite (a + b) * c into c * (a + b) with mul_comm tactic. We then use mul_add
to rewrite c * (a + b) into c * a + c * b. The proof completes by applying mul_comm to both terms
of the sum c * a + c * b to get a * c + b * c and using rfl.
-/

/- Prove: Multiplication is associative. In other words, for all natural numbers a, b and c, we
have (a * b) * c = a * (b * c). -/
theorem _mult_assoc (a : Nat) (b : Nat) (c: Nat) : (a * b) * c = a * (b * c) := by
  induction a with
  | zero => repeat rw[Nat.zero_mul]
  | succ a ih => rw[Nat.succ_mul, Nat.add_mul, ih, Nat.succ_mul]
/- Proof:
```
induction a with a ih
repeat rw[zero_mul]
rfl
rw[succ_mul,add_mul, ih, succ_mul]
rfl
```

Explanation: The proof proceeds by induction on a. The base case follows by repeated application of
zero_mul tactic. In the inductive step, we first use succ_mul to rewrite (succ a) * b * c into
(a * b + b) * c, which we rewrite into a * b * c + b * c with add_mul tactic. We then apply the
inductive hypothesis to rewrite a * b * c + b * c into a * (b * c) + b * c. Finally, we apply
succ_mul to the rhs of the goal to get a * (b * c) + b * c and close the goal by rfl.
-/

/- ## Power World -/

/- Power worlds starts with these definitions

pow_zero (a : ℕ) : a ^ 0 = 1
pow_succ (a b : ℕ) : a ^ succ b = a ^ b * a
-/

/- Prove: 0 ^ 0 = 1. -/
theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  rw [Nat.pow_zero 0]

/- Proof:
```
rw [pow_zero 0]
rfl
```

Explanation: The proof follows from the definition of pow_zero by setting a = 0 in a ^ 0 = 1.
-/

/- Prove: For all natural numbers m, 0 ^ succ(m) = 0. -/
theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (Nat.succ m) = 0 := by
  induction m with
  | zero => rw[Nat.pow_succ, zero_pow_zero]
  | succ m ih => rw [Nat.pow_succ, ih]

/- Proof:
```
induction m with m ih
rw[pow_succ, zero_pow_zero]
rw[mul_zero]
rfl
rw [pow_succ, ih]
rw[mul_zero]
rfl
```

Explanation: The proof is by induction on m. The base case applies pow_succ to rewrite 0 ^ (succ 0)
into 0 ^ 0 * 0, which is then rewritten into 1 * 0 with zero_pow_zero tactic. The base case is
closed by mul_zero and rfl. The inductive step rewrites 0 ^ (succ (succ m)) as 0 ^ (succ m) * 0,
applies the inductive hypothesis to get 0 * 0 and closes the goal with mul_zero and rfl.
-/

/- Prove: For all naturals a, a ^ 1 = a. -/
theorem _pow_one (a : ℕ) (one_eq_succ_zero: 1 = Nat.succ 0) : a ^ 1 = a := by
  rw[one_eq_succ_zero, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

/- Proof:
```
rw[one_eq_succ_zero]
rw[pow_succ, pow_zero, one_mul]
rfl
```

Explanation: We first rewrite 1 in the exponent of a into succ 0 using one_eq_succ_zero. We include
one_eq_succ_zero as an assumption in the theorem because this tactic has been deprecated from
Mathlib. We then apply pow_succ and pow_zero to rewrite a ^ succ 0 into a ^ 0 * a and 1 * a. We
close the goal with one_mul and rfl.
-/


/- Prove: For all naturals m, 1 ^ m = 1. -/
theorem _one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with
  | zero => rw[Nat.pow_zero]
  | succ m ih => rw[Nat.pow_succ, ih]
/- Proof:
```
induction m with m ih
rw[pow_zero]
rfl
rw[pow_succ, ih, mul_one]
rfl
```

Explanation: The proof is by induction on m. The base case follows by applying pow_zero. The
inductive step is proved by apply pow_succ to rewrite 1 ^ succ m into 1 ^ m * 1 and the inductive
hypothesis to get 1 * 1. The prove concludes by apply mul_one and rfl tactics.
-/

/- Prove: For all naturals a, a ^ 2 = a * a. -/
theorem _pow_two (a : ℕ) (two_eq_succ_one : 2 = Nat.succ 1) : a ^ 2 = a * a := by
  rw[two_eq_succ_one, Nat.pow_succ, Nat.pow_one]
/- Proof:
```
rw[two_eq_succ_one, pow_succ, pow_one]
rfl
```

Explanation: We first rewrite 2 in the exponent of a into succ 1. We then apply pow_succ to rewrite
a ^ succ 1 into a ^ 1 * a. Finally, we apply pow_one to rewrite a ^ 1 into a and the goals is closed
by rfl.
-/


/- Prove: For all naturals a, m, n, we have a ^ (m + n) = a ^ m * a ^ n. -/
theorem _pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ n ih =>
       rw[Nat.pow_succ a n, ← Nat.mul_assoc]
       rw[← ih, ← Nat.pow_succ]
       rw[← Nat.add_assoc]
/- Proof:
```
induction n with n ih
rw[add_zero, pow_zero, mul_one]
rfl
rw[pow_succ a n, ← mul_assoc]
rw[← ih, ← pow_succ]
rw [succ_eq_add_one n, ← add_assoc, ← succ_eq_add_one]
rfl
```

Explanation: The proof is by induction on n. The base case requires us to prove that a ^ (m + 0) is
equal to a ^ m * a ^ 0. We do that by rewriting both sides into a ^ m. On the lhs, we apply
add_zero to rewrite a ^ (m + 0) into a ^ m. On the rhs, we apply pow_zero to rewrite a ^ 0 into 1
and mul_one to rewrite a ^ m * 1 into a ^ m.

In the inductive step we prove that both sides of the goal can be rewritten to  a ^ succ (m + n).
First, we rewrite a ^ succ n into a ^ n * a on the rhs using pow_succ tactic. We then rewrite
a ^ m * (a ^ n * a) into (a ^ m * a ^ n) * a using mul_assoc tactic in reverse. We apply the
inductive hypothesis in reverse to rewrite a ^ m * a ^ n into a ^ (m + n) and pow_succ in reverse
to rewrite a ^ (m + n) * a into a ^ succ (m + n). On the lhs, we apply succ_eq_add_one to rewrite
succ n into n + 1. We then apply add_assoc to rewrite m + (n + 1) into (m + n) + 1 and apply
succ_eq_add_one in reverse to rewrite (m + n) + 1 as succ (m + n). The goal is now closed by rfl.

Note that in Lean 4 proof, we don't need to apply succ_eq_add_one because Lean 4 automatically
rewrites succ x into x + 1.
-/

/- Prove:  For all naturals a, b, n, we have (ab) ^ n = a ^ n * b ^ n. -/
theorem _mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    repeat rw[Nat.pow_zero]
  | succ n ih =>
    repeat rw[Nat.pow_succ]
    rw[← Nat.mul_assoc (a^n * a) (b^n) b]
    rw[Nat.mul_assoc (a^n) a (b^n)]
    rw[Nat.mul_comm a (b^n)]
    rw[← Nat.mul_assoc (a^n) (b^n) a]
    rw[ih]
    rw[← Nat.mul_assoc (a ^ n * b ^ n) a  b]
/- Proof:
```
induction n with n ih
repeat rw[pow_zero]
rw[mul_one]
rfl
repeat rw[pow_succ]
rw[← mul_assoc (a^n * a) (b^n) b]
rw[mul_assoc (a^n) a (b^n)]
rw[mul_comm a (b^n)]
rw[← mul_assoc (a^n) (b^n) a]
rw[ih]
rw[← mul_assoc (a ^ n * b ^ n) a  b]
rfl
```

Explanation: Our proof is by induction on n. The base case follows by repeated application of
pow_zero tactic followed by mul_one tactic and rfl.

We will close the inductive step goal by proving that both the lhs and the rhs can be rewritten
into a ^ n * b ^ n * a * b. We start the inductive step by applying pow_succ three times to rewrite
(a * b) ^ (succ n) into (a * b) ^ n * (a * b), a ^ (succ n) into a ^ n * a, and b ^ (succ n) into
b ^ n * b. We the apply mul_assoc backwards and forwards to rewrite a ^ n * a * (b ^ n * b) into
a ^ n * (a * b ^ n) * b, which allows us to apply mul_comm to a and b^n to obtain
a ^ n * (b ^ n * a) * b. Now we apply mul_assoc in reverse once again to obtain
a ^ n * b ^ n * a * b. Next, we use the inductive hypothesis to rewrite (a * b) ^ n into
(a ^ n) * (b ^ n) and mul_assoc in reverse to obtain a ^ n * b ^ n * a * b. The goal is closed by
rfl.
-/


/- Prove: For all naturals a, m, n, we have (a ^ m) ^ n = a^(mn). -/
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero => rw[Nat.pow_zero, Nat.mul_zero, Nat.pow_zero]
  | succ n ih =>
    rw[Nat.pow_succ, ih]
    rw[← Nat.pow_add]
    rw[Nat.mul_succ]
/- Proof:
```
induction n with n ih
rw[pow_zero, mul_zero, pow_zero]
rfl
rw[pow_succ, ih]
rw[← pow_add]
rw[mul_succ]
rfl
```

Explanation: The proof is by induction on n. In the base case, we use pow_zero to rewrite
(a ^ m) ^ 0 into 1. We use mul_zero and pow_zero to rewrite a ^ (m * 0) into 1 and close the base
case by rfl.

In the inductive step, we use pow_succ to rewrite (a ^ m) ^ (succ n) into (a ^ m) ^ n * a ^ m. We
then apply the inductive hypothesis to rewrite (a ^ m) ^ n * a ^ m into a ^ (m * n) * a ^ m. Next,
we use pow_add to rewrite a ^ (m * n) * a ^ m into a ^ (m * n + m). Finally, we apply mul_succ
on the rhs to rewrite a ^ (m * succ n) into a ^ (m * n + m) and close the inductive steps with rfl.
-/

/- Prove: For all numbers a and b, we have (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b. -/
theorem _add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw[Nat.pow_two, Nat.mul_add]
  repeat rw[Nat.add_mul]
  rw[Nat.mul_comm b a]
  repeat rw[← Nat.pow_two]
  rw[Nat.add_assoc, Nat.add_comm (a * b) (a * b + b ^ 2), Nat.add_comm (a * b)  (b ^ 2)]
  rw[Nat.add_assoc (b ^ 2) (a * b) (a * b), ← Nat.two_mul]
  rw[← Nat.mul_assoc 2 a b]
  rw[← Nat.add_assoc (a ^ 2) (b ^ 2) (2 * a * b)]
/- Proof:
```
rw[pow_two, mul_add]
repeat rw[add_mul]
rw[mul_comm b a]
repeat rw[← pow_two]
rw[add_assoc, add_comm (a * b) (a * b + b ^ 2), add_comm (a * b)  (b ^ 2)]
rw[add_assoc (b ^ 2) (a * b) (a * b), ← two_mul]
rw[← mul_assoc 2 a b]
rw[← add_assoc (a ^ 2) (b ^ 2) (2 * a * b)]
rfl
```

Explanation: We will complete the proof by rewriting the lhs into the rhs. First, we use pow_two
tactic to rewrite (a + b) ^ 2 into (a + b) * (a + b). We then use mul_add tactic to rewrite this
further into (a + b) * a + (a + b) * b. Next, we apply add_mul twice to obtain
a * a + b * a + (a * b + b * b). Next, we apply mul_comm to rewrite b * a into a * b. This gives us
a * a + a * b + (a * b + b * b) and the goal is now in sight. We proceed by applying pow_two in
reverse twice to rewrite a * a into a ^ 2 and b * b into b ^ 2. We then use add_assoc once and
add_comm twice to move b ^ 2 into the position of the second summand. We than apply associativity
again and collect the sum of two copies of a * b into 2 * (a * b) using two_mul tactic in reverse.
We rewrite the term 2 * (a * b) into 2 * a * b using associativity in reverse. Finally, we
associate the sum to the left and close the goal by rfl. -/

/- ## Implication World -/

/- Prove: Assuming x + y = 37 and 3 * x + z = 42, we have x + y = 37. -/
example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1
/- Proof:
```
exact h1
```

Explanation: The `exact` tactic closes the goal by applying one of the hypotheses verbatim. In this
example, we close the goal x + y = 37 by applying the hypothesis h1 which has the same type as
the goal. h2 is underlined because it's not used in the body of the proof.
-/

/- Prove: Assuming 0 + x = (0 + y) + 2, we have x = y + 2. -/
example (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  repeat rw [Nat.zero_add] at h
  exact h
/- Proof:
```
repeat rw [zero_add] at h
exact h
```

Explanation: We can use the suffix at h to do a rewrite of the hypothesis. In this example, we use
zero_add tactic twice to rewrite h into x = y + 2, which we the use to close the goal with the
`exact` tactic.
-/

/- Prove: If x = 37 and we know that x = 37  implies y = 42 then we can deduce y = 42. -/
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1
  exact h1
/- Proof:
```
apply h2 at h1
exact h1
```

Explanation: For the Lean 4 proof to work, we need to include `import Mathlib.Tactic.applyAt` in
the imports section because `apply at` tactic we need is [defined in mathlib](https://github.com/leanprover-community/mathlib4/blob/b9b0429f74af0747d75eae9c3c74f524d9e6e435/Mathlib/Tactic/ApplyAt.lean#L10).
The `apply e at h` tactic applies the implications from `e` to hypothesis `h`. In this example,
`apply h2 at h1` starts with hypothesis `h1: x = 37` and applies the implication
`x = 37 implies y = 42` to rewrite `h1` into `y = 42`. The goal now can be closed with `exact h1`.
-/

/- Prove: If x + 1 = 4 then x = 3. -/
theorem four_eq_succ_three : 4 = Nat.succ 3 := by rfl

theorem succ_inj (a : ℕ) (b : ℕ) : Nat.succ a = Nat.succ b -> a = b := by
  skip

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three] at h
  rw[← Nat.succ_eq_add_one] at h
  apply succ_inj at h
  exact h
/- Proof:
```
rw [four_eq_succ_three] at h
rw[← succ_eq_add_one] at h
apply succ_inj at h
exact h
```

Explanation: In this level, the game instructions allow us to assume `succ_inj` as a fact, which we
state as a theorem without proof so we can use it in the example. We also state and prove
`four_eq_succ_three` because it's availabe in the game server at this level.

As for the proof, we first rewrite `4` as `succ 3` using `four_eq_succ_three` and then rewrite
`x + 1` as `succ x` using `succ_eq_add_one` tactic in reverse. We then apply `succ_inj` theorem to
`h: succ x = succ 3`, which rewrites `h` into `x = 3` and allows us to close the goal with
`exact h`.
-/

/- Prove: x = 37 implies x = 37. -/
example (x : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h
/- Proof:
```
intro h
exact h
```

Explanation: In this example, we are proving an implication of the form P implies Q. We start with
`intro h` tactic to assume the hypothesis and assign its proof to `h`. We then close the goal with
`exact h` because the hypothesis is equal to the conclusion.
-/


/- Prove: x + 1 = y + 1 implies x = y. -/
example (x : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  repeat rw[← Nat.succ_eq_add_one] at h
  apply succ_inj at h
  exact h
/- Proof:
```
intro h
repeat rw[← succ_eq_add_one] at h
apply succ_inj at h
exact h
```

Explanation: Since the goal is an implication, we start our proof by introducing the hypothesis and
call its proof h with `intro h`. We then rewrite `x + 1` and `y + 1` into `succ x` and `succ y`
with `succ_eq_add_one` tactic in reverse and `h` becomes `succ x = succ y`. Next, we apply
`succ_inj` at `h`, which rewrites `h` into `x = y`. We close the goal with `exact` tactic.
-/

/- Prove: If x = y and x is not equal to y then we can deduce a contradiction. -/
example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1
  exact h1
/- Proof:
```
apply h2 at h1
exact h1
```

Explanation:  In Lean 4, `x ≠ y` means `(x = y) → False`. We use this interpretation to rewrite h1
into False by applying `h2: (x = y) → False` at `h1: x = y`. We then close the goal with `exact`.
-/

/- Prove: 0 is not equal to 1. -/
theorem zero_ne_succ (a : ℕ) : 0 ≠ Nat.succ a := by skip

theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  exact zero_ne_succ 0
/- Proof:
```
exact zero_ne_succ 0
```

Explanation: In this level, the goal is to prove that 0 is not equal to 1 using Peano's axiom that
0 is not equal to a successor of any natural number. We state this Peano axiom as a theorem
zero_ne_succ without proof.

We notice that `zero_ne_one` is a special case of `zero_ne_succ` when `a = 0` and close the goal
with `exact` tactic.
-/

/- Prove: 1 is not equal to 0. -/
theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  symm
  exact zero_ne_one
/- Proof:
```
symm
exact zero_ne_one
```

Explanation: We use `symm` tactic to interchange the lhs and the rhs in the goal and complete the
goal with `exact` tactic.
-/

/- Prove: 2 + 2 is not equal to 5. -/
example : Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0) ≠
          Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
  intro h
  rw [Nat.add_succ, Nat.add_succ, Nat.add_zero] at h
  repeat apply succ_inj at h
  apply zero_ne_succ 0
  exact h
/- Proof:
```
intro h
rw [add_succ, add_succ, add_zero] at h
repeat apply succ_inj at h
apply zero_ne_succ 0
exact h
```

Explanation: To prove that `a` is not equal to `b` in Lean 4, we must prove that `a = b` implies
`False`. We start by introducing the hypothesis of equality with `intro` tactic. We then rewrite
the left hand side of the hypothesis into four applications of `Nat.succ` to `0` using `add_succ`
tactic twice and `add_zero` tactic once. We then apply `succ_inj` tactic four times to rewrite
the hypothesis into `0 = Nat.succ 0`. We apply `zero_ne_succ 0` to rewrite the hypothesis into
`False`. We close the goal with `exact` tactic.
-/


/- Template -/
/- Prove: -/
/- Proof:
```
```

Explanation:
-/
