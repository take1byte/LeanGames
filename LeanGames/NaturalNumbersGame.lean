import Mathlib.Tactic.NthRewrite
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.applyAt
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use

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
  intro h
  rw [← Nat.pred_succ a]
  rw [← Nat.pred_succ b]
  rw [h]

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

/- ## Algorithm World -/
/- Prove: If a, b, c are natural numbers, then a + (b + c) = b + (a + c). -/
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw[Nat.add_comm b (a + c), Nat.add_assoc a c b, Nat.add_comm c b]
/- Proof:
```
rw[add_comm b (a + c), add_assoc a c b, add_comm c b]
rfl
```

Explanation: We first rewrite the rhs from `b + (a + c)` into `(a + c) + b` using `add_comm` tactic.
We then rewrite `(a + c) + b` into `a + (c + b)` using `add_assoc` tactic. Finally, we rewrite
`a + (c + b)` into `a + (b + c)` with `add_comm` tactic applied to the sub-term `(c + b)` and close
the goal with `rfl`.
-/

/- Prove: If a,b, c and d are numbers, we have (a + b) + (c + d) = ((a + c) + d) + b. -/
example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  repeat rw [Nat.add_assoc]
  rw [add_left_comm b c d]
  rw [Nat.add_comm b d]

/- Proof:
```
repeat rw [add_assoc]
rw [add_left_comm b c]
rw [add_comm b d]
rfl
```

Explanation: We first rewrite the goal into `a + (b + (c + d)) = a + (c + (d + b))` using
`add_assoc` tactic. We then rewrite `a + (b + (c + d))` into `a + (c + (b + d))` using
`add_left_comm` tactic applied to the sub-term `b + (c + d)`. Finally, we rewrite
`a + (c + (b + d))` into `a + (c + (d + b))` using `add_comm` tactic applied to the sub-term
`(b + d)` and close the goal with `rfl`.
-/

/- Prove: If `a, b, ..., h` are arbitrary natural numbers, we have
`(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h`. -/
example (a b c d e f g h : ℕ) :
  (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_left_comm, Nat.add_comm]
/- Proof:
```
simp only [add_left_comm, add_comm]
```

Explanation: We will use Lean 4 simplifier to complete this goal automatically instead of manually
appying `add_assoc` and `add_comm` lots of time. The simplifier searches through different ways of
rewriting the goal with the aim of completing it. The simplifier is invoked by `simp` tactic.

In general, `simp` can be slow because it searches through a large number of tactics and ways of
combining them into proofs. We can speed up the search by constraining it to a minimal set of
tactics we want Lean to use for simplification, e.g., `simp only [add_left_comm, Nat.add_comm]`
tells Lean simplifier to use only `add_left_comm` and `Nat.add_comm`.

If we aren't sure what tactics suffice for simplifying a given expression, we can run `simp?`,
which will instruct Lean simplifier to find the tactics for us.
-/

/- Prove: If `a, b, ..., h` are arbitrary natural numbers, we have
`(d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h` by defining a new tactic
`simp_add` that simplifies the goal using a minimal set of tactics. -/

macro "simp_add" : tactic => `(tactic|(simp only [add_left_comm, Nat.add_comm]))

example (a b c d e f g h : ℕ) :
  (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add
/- Proof:
```
simp_add
```

Explanation: First, we use Lean 4 `macro` feature to define a new tactic `simp_add`. We the use
this tactic to close the goal in our example.

For an overview of macros, take a look [here](https://lean-lang.org/lean4/doc/macro_overview.html),
and for tactics, see [here](https://github.com/leanprover/lean4/blob/master/doc/tactics.md) and
[here](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html).
-/

/- Prove: If `succ(a) = succ(b)` then `a = b`. You may not use `succ_inj`. You may use `pred_succ`,
which is the proof that `pred (succ n) = n`.
-/
example (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  rw [← Nat.pred_succ a]
  rw [← Nat.pred_succ b]
  rw [h]
/- Proof:
```
rw [← pred_succ a]
rw [← pred_succ b]
rw [h]
rfl
```

Explanation: We first rewrite the goal into `pred (succ a) = pred (succ b)` by applying `pred_succ`
tactic in reverse to `a` and `b`. We then use the hypothesis `h` to rewrite `succ a` into `succ b`
in the new goal and obtain a new goal `pred (succ b) = pred (succ b)`, which we close by `rfl`.
-/

/- Prove: `Nat.succ a` is not equal to `0`. -/
def is_zero : Nat -> Bool
| 0 => True
| Nat.succ _ => False

theorem is_zero_succ (n : ℕ): is_zero (Nat.succ n) = False := by
  skip

theorem succ_ne_zero (a : ℕ) : Nat.succ a ≠ 0 := by
  intro h
  rw[← is_zero_succ a]
  rw[h]
  trivial
/- Proof:
```
intro h
rw[← is_zero_succ a]
rw[h]
trivial
```

Explanation: In this level, we are asked to use `is_zero` definition and `is_zero_succ` theorem to
prove that `Nat.succ a` is not equal to `0`.

First, we use `intro` tactic to state the hypothesis we want to falsify, which is `Nat.succ a = 0`
and bind it to `h`. We then rewrite the goal, which is `False` into `is_zero (Nat.succ a) = true`
using `is_zero_succ` theorem. We apply the hypothesis `h` to rewrite our goal into
`is_zero 0 = true` by rewriting the term `Nat.succ a` into `0`. We close the goal
using `trivial` tactic because `is_zero 0 = true` is `True` follows from the definition of
`is_zero`.
-/

/- Prove: If `a` is not equal to `b` then `Nat.succ a` is not equal to `Nat.succ b`. -/
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : Nat.succ m ≠ Nat.succ n := by
  contrapose! h
  apply succ_inj m n at h
  exact h
/- Proof:
```
contrapose! h
apply succ_inj m n at h
exact h
```

Explanation: First, we use `contrapose!` tactic to rewrite the implication we want to prove into
its logically equivalent contrapositive: `Nat.succ m = Nat.succ n` implies `m = n`. We then apply
`succ_inj` to rewrite our new hypothesis `Nat.succ m = Nat.succ n` into `m = n` and close the goal
with `exact` tactic.
-/

/- Prove: 20 + 20 = 40. -/
instance instDecidableEq : DecidableEq ℕ
  | 0, 0 => isTrue <| by
    show 0 = 0
    rfl
  | Nat.succ m, 0 => isFalse <| by
    show Nat.succ m ≠ 0
    exact succ_ne_zero m
  | 0, Nat.succ n => isFalse <| by
    show 0 ≠ Nat.succ n
    exact zero_ne_succ n
  | Nat.succ m, Nat.succ n =>
    match instDecidableEq m n with
    | isTrue (h : m = n) => isTrue <| by
      show Nat.succ m = Nat.succ n
      rw [h]
    | isFalse (h : m ≠ n) => isFalse <| by
      show Nat.succ m ≠ Nat.succ n
      exact succ_ne_succ m n h

example : (20 : ℕ) + 20 = 40 := by decide
/- Proof:
```
decide
```

Explanation: `decide` is a tactic that attempts to close a goal by finding an algorithm it can
run to produce a proof. In the case of our example, `20 + 20 = 40`, the `decide` tactic uses the
fact that equality of natural numbers can be proven algorithmically as shown in the algorithm
above the example. The `instance` keyword declares that `instDecidableEq` is an instance of
`DecidableEq ℕ` typeclass. `DecidableEq ℕ` asserts that natural numbers have decidable equality.

Note that the declaration of type `(20 : ℕ)` in the example is necessary because [numerals are
polymorphic in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/type_classes.html#numerals).
-/

/- Prove: 2 + 2 is not equal to 5. -/
example : (2 : ℕ) + 2 ≠ 5 := by decide
/- Proof:
```
decide
```

Explanation: Inequality of natural numbers is decidable by the same algorithm as in the previous
example. Therefore, `decide` tactic is able to close the goal.
-/

/- ## Advanced Addition World -/
/- Prove: For all natural numbers `a, b, n`, we have `a + n = b + n` implies `a = b`. -/
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with
  | zero =>
    intro h
    rw[Nat.add_zero, Nat.add_zero] at h
    exact h
  | succ n ih =>
    intro h
    repeat rw[← Nat.add_assoc, ← Nat.succ_eq_add_one] at h
    apply succ_inj at h
    apply ih at h
    exact h
/- Proof:
```
induction n with n ih
intro h
repeat rw[add_zero] at h
exact h
intro h
repeat rw[succ_eq_add_one] at h
repeat rw[← add_assoc, ← succ_eq_add_one] at h
apply succ_inj at h
apply ih at h
exact h
```

Explanation: The proof is by induction on h. For the base case we have to prove that `a + 0 = b + 0`
implies `a = b`. We introduce the hypothesis as `h` and rewrite it from `a + 0 = b + 0` to `a = b`
with `add_zero` tactic applied twice. We then close the base case goal with `exact` tactic because
the hypothesis and the goal are now equal.

For the inductive step, we assume `a + n = b + n` implies `a = b` and we have to prove that
`a + Nat.succ n = b + Nat.succ n` implies `a = b`. We start the proof by introducing the hypothesis
`a + Nat.succ n = b + Nat.succ n` as `h`. In the server version of then proof, we rewrite
`Nat.succ n` as  `n + 1` and in the Lean 4 this rewrite is not necessary because Lean 4 expands
`Nat.succ` into `+1` automatically. We then apply `add_assoc` tactic to rewrite `a + (n + 1)` into
`(a + n) + 1` and `b + (n + 1)` into `(b + n) + 1`. We then apply `succ_inj` at `h` to rewrite `h`
into `a + n = b + n`. We then apply `ih` at `h` to further rewrite `h` into `a = b`. We close the
goal with `exact` tacitc.
-/

/- Prove: For all natural numbers `a, b, n`, we have `n + a = n + b` implies `a = b`. -/

theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  repeat rw[Nat.add_comm n]
  exact add_right_cancel a b n

theorem add_left_cancel_second_proof (a b n : ℕ) : n + a = n + b → a = b := by
  induction n with
  | zero =>
  intro h
  repeat rw[Nat.zero_add] at h
  exact h
  | succ n ih =>
  intro h
  repeat rw[Nat.add_assoc] at h
  rw[Nat.add_comm 1 a, Nat.add_comm 1 b] at h
  repeat rw[← Nat.add_assoc] at h
  apply succ_inj at h
  apply ih at h
  exact h
/- Proof:

First proof:
```
repeat rw[add_comm n]
exact add_right_cancel a b n
```

Second proof:
```
induction n with n ih
intro h
repeat rw[zero_add] at h
exact h
intro h
repeat rw[succ_eq_add_one, add_assoc, add_assoc] at h
rw[add_comm 1 a, add_comm 1 b] at h
rw[← add_assoc, ← add_assoc] at h
rw[← succ_eq_add_one, ← succ_eq_add_one] at h
apply succ_inj at h
apply ih at h
exact h
```

Explanation: We can use `add_comm` to rewrite the goal into `a + n = b + n` implies `a = b`, which
we can close with `add_right_cancel` that we proved in the previous level.

Alternatively, we can use induction and give a proof similar to that of `add_right_cancel`. In the
base case, we introduce the hypothesis as `h` and apply `zero_add` tactic twice to rewrite `h` into
the goal `a = b`.

In the inductive step, we introduce the hypothesis `n + 1 + a = n + 1 + b` implies `a = b` as `h`.
We then use associativity and commutativity of addition tactics, `add_assoc` and `add_comm`, to
rewrite `h` into `(n + a) + 1 = (n + b) + 1`. Next, we apply `succ_inj` to rewrite `h` further into
`n + a = n + b`. We now apply the inductive hypothesis `ih` at `h` to rewrite `h` into `a = b` and
close the goal with `exact`.
-/

/- Prove: `x + y = y` implies `x = 0`. -/
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  nth_rw 2 [← Nat.zero_add y]
  exact add_right_cancel x 0 y

/- Proof:
```
nth_rewrite 2 [← zero_add y]
exact add_right_cancel x 0 y
```

Explanation: First, we observe that the goal can be rewritten into a special case of
`add_left_cancel` by adding `0` on the left of the second occurrence of `y`. We do this rewrite
with `nth_rw 2` tactic. We then use `exact` tactic to close the goal as a special case of
`add_right_cancel`.
-/


/- Prove: `x + y = x` implies `y = 0`. -/
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  rw[Nat.add_comm x y]
  exact add_left_eq_self y x
/- Proof:
```
rw[add_comm x y]
exact add_left_eq_self y x
```

Explanation: We observe that we can rewrite the goal into `add_left_eq_self y x` by rewriting
`x + y` into `y + x`. To elaborate, `add_left_eq_self y x` is the proof that `y + x = x` implies
`y = 0`, which would prove our goal except that our goal has `x + y` instead of `y + x`. We use
`Nat.add_comm x y` to rewrite our goal so the proof `add_left_eq_self y x` can close it.
-/

/- Prove: If `a + b = 0` then `a = 0`. -/
theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b
  rw[Nat.add_zero]
  intro h
  exact h
  intro h
  apply succ_ne_zero at h
  cases h
/- Proof:
```
cases b with d
rw[add_zero]
intro h
exact h
rw[add_succ]
intro h
apply succ_ne_zero at h
cases h
```

Explanation: We use `cases` tactic to split our proof into two cases: `b = 0` and `b = Nat.succ d`
for some `d ∈ ℕ`. When `b = 0`, we have to show `a + 0 = 0` implies `a = 0`. We rewrite `a + 0` into
`a` with `add_zero` tactic, introduce the hypothesis `a = 0` as `h`, and close the goal with
`exact` because the hypothesis is identical to the conclusion.

When `b = Nat.succ d`, we will show that the hypothesis `h: a + Nat.succ d = 0` is `False`. We will
use `cases h` to close the goal. This works because when `h` is `False`, any implication `h → q` is
automatically `True`, which means there's nothing to prove. Now, getting to the proof, we first
introduce the hypothesis as `h` and then rewrite it into `Nat.succ (a + d)`. Next, we use
`succ_ne_zero` applied at `h` to conclude that `h` is `False`. Finally, we close the goal with
`cases h`.
-/

/- Prove: If `a + b = 0` then `b = 0`. -/
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw[Nat.add_comm]
  exact add_right_eq_zero b a
/- Proof:
```
rw[add_comm]
exact add_right_eq_zero b a
```

Explanation: We observe that `add_left_eq_zero` can be rewritten into `add_right_eq_zero` by
rewriting `a + b` into `b + a` and exchanging the roles of `a` and `b`. The first rewrite is done
with `Nat.add_comm` and the exchange of roles of `a` and `b` is done with changing the order of
parameters in `add_right_eq_zero` from `a b` into `b a`.
-/

/- ## ≤ World -/
/- This world starts with a definition: For natural numbers `a, b`, we write `a ≤ b` if and only
if there exists a natural number `c` such that `b = a + c`. In this World, `a ≤ b` is notation for
`∃ c, b = a + c` per https://github.com/ImperialCollegeLondon/natural_number_game/blob/6b30156c5025760d1ed8753de3b44a075e2f8a51/src/mynat/le.lean#L8/.
-/

/- Prove: If `x` is a natural number, then `x ≤ x`. -/
theorem _le_refl (x : ℕ) : ∃ c : ℕ, x = x + c := by
  use 0
  rw[Nat.add_zero]
/- Proof:
```
use 0
rw[add_zero]
rfl
```


Explanation: For this proof, we need to import the `use` tactic from `Mathlib`. This is done with
the statement `import Mathlib.Tactic.Use`. Tactic `use` in Lean 4, expects an `∃` statement, which
is why we expand the definition of `≤` in the statement of the theorem.

In the game server, we start the proof with `use 0`, which rewrites the goal into `x + 0 = x`. We
then use `add_zero` tactic to rewrite the goal into `x = x`, which we close with `rfl`.
-/

/- Prove:  If `x` is a natural number, then `0 ≤ x`. -/
theorem zero_le (x : ℕ) : ∃ c, x = 0 + c := by
  use x
  rw[Nat.zero_add]
/- Proof:
```
use x
rw[zero_add]
rfl
```

Explanation: `0 ≤ x` is, by definition, `∃ c, x = 0 + c`. We invoke `use x` to rewrite the goal
into `x = 0 + x`. We then use `Nat.zero_add` to further rewrite the goal into `x = x`, which is
closed by `rfl`.
-/

/- Prove: If `x` is a number, then `x ≤ succ(x)`. -/
theorem le_succ_self (x : ℕ) : ∃ c, Nat.succ x = x + c := by
  use 1
/- Proof:
```
use 1
exact succ_eq_add_one x
```

Explanation: In Lean 4, the goal is closed with `use 1`. In the game server, `use 1` rewrites
the goal into `succ x = x + 1`, which we can close with `exact succ_eq_add_one x`.
-/

/- Prove: If `x ≤ y` and `y ≤ z`, then `x ≤ z`. -/
--theorem _le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by skip
/- Proof:
```
cases hxy with a ha
cases hyz with b hb
use (a + b)
rw[hb, ha, add_assoc]
rfl
```

Explanation: We first rewrite hypothesis `hxy` into `ha: y = x + a` and `hyz` into `hb : z = x + b`
using `cases` tactic. We then rewrite the goal `x ≤ z` into `z = x + (a + b)` with `use` tactic.
Next, we rewrite `z` in the new goal using `hb` and `ha` to get `x + a + b = x + (a + b)`. Finally,
we apply `add_assoc` and `rfl` to close the goal.
-/


/- Prove:  If `x ≤ 0`, then `x = 0`. -/
/- theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by -/
/- Proof:
```
cases hx with a h
symm at h
apply (add_right_eq_zero x a) at h
exact h
```

Explanation: We start the proof with `cases` tactic to rewrite hypothesis `hx` using the definition
of `≤`. The new hypothesis is ` 0 = x + a`, which we rewrite into `x + a = 0` with `symm`
tactic. Next, we apply `add_right_eq_zero` to rewrite the hypothesis into `x = 0`. We close the
goal with `exact`.
-/

/- Prove: If `x ≤ y` and `y ≤ x`, then `x = y`. -/
/- theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by -/
/- Proof:
```
cases hxy with a ha
cases hyx with b hb
rw[ha] at hb
nth_rewrite 1 [← add_zero x] at hb
rw[add_assoc] at hb
apply add_left_cancel 0 (a+b) x at hb
symm at hb
apply add_right_eq_zero at hb
rw[hb, add_zero] at ha
symm at ha
exact ha
```

Explanation: First, we use `cases` tactic to rewrite the hypotheses as `ha: y = x + a` and
`hb: x = y + b`. We then use `ha` to rewrite `hb` into `x = x + a + b`. We rewrite the first
occurrence of `x` into `x + 0` with precision rewriting tactic `nth_rewrite` and `add_zero` in
reverse. Next, we rewrite `x + a + b` into `x + (a + b)` with `add_assoc` tactic. Now, `hb` is
`x + 0 = x + (a + b)` and we apply `add_left_cancel` to rewrite `hb` into `0 = a + b`. Next, we
use `symm` tactic to rewrite `0 = a + b` into `a + b = 0` and apply `add_right_eq_zero` to rewrite
`hb` into `a = 0`. Now, we use `hb` and `add_zero` tactic to rewrite `ha:  y = x + a` into `y = x`.
Finally, we apply `symm` and close the goal with `exact`.
-/

/- Prove: If `x = 37` or `y = 42`, then `y = 42` or `x = 37`.-/
/- example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by -/
/- Proof:
```
cases h with hx hy
right
rw[hx]
rfl
left
rw[hy]
rfl
```

Explanation: We start the proof with `cases` tactic to split the `or` in the hypothesis `h` into
two branches. We then use `right` tactic to select the branch `x = 37`. We rewrite the goal using
`hx` and close `37 = 37` with `rfl`. Next, we select the branch `y = 42` with `left` tactic,
rewrite the goal with `hy`, and close `42 = 42` with `rfl`.
-/

/- Prove:  If `x` and `y` are numbers, then either `x ≤ y` or `y ≤ x`. -/
/- theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by -/
/- Proof:
```
induction y with d hd
right
exact zero_le x
cases hd with hdl hdr
left
cases hdl
use (w + 1)
rw[← add_assoc x w 1, succ_eq_add_one]
rw[h]
rfl
cases hdr with e he
cases e with a
rw[add_zero] at he
left
rw[he]
exact le_succ_self d
right
use a
rw[succ_eq_add_one, add_comm a 1, ← add_assoc d 1 a, ← succ_eq_add_one] at he
exact he
```

Explanation: Our proof is by induction on `y`. The base case is `x ≤ 0 ∨ 0 ≤ x`. We choose the right
branch with `right` tactic because `x ∈ ℕ` and close the goal with `exact zero_le x`.

The inductive hypothesis is `x ≤ d ∨ d ≤ x` and the goal is `x ≤ succ d ∨ succ d ≤ x`. We split the
hypothesis into `hdl: x ≤ d` and `hdr: d ≤ x`. We observe that the left branch `x  ≤ succ d` of our
goal follows from `x ≤ d`, and therefore, we select is with `left` tactic. To prove that `x ≤ d`
implies `x ≤ succ d`, we use the definition of `≤` to find `w` such that `d = x + w`. This implies
`d + 1 = x + w + 1`, which proves that `x ≤ succ d`. To write this proof in game server, we first
use `cases hdl` tactic to rewrite `hdl` into `h: d = x + w`. We then execute `use (w + 1)` tactic
to rewrite our goal from `x  ≤ succ d` into `succ d = x + (w + 1)`. We further rewrite this into
`d + 1 = (x + w) + 1`. Next, we apply `h` and our goal becomes `(x + w) + 1 = (x + w) + 1`, which
we close by rfl.

Next, we need to prove that `hdr: d ≤ x` implies `x ≤ succ d ∨ succ d ≤ x`. We first rewrite `hdr`
into `he: x = d + e`. Since `he` doesn't immediately imply either `x ≤ succ d` or `succ d ≤ x`, we
use `cases e with a` to split `he` into cases when `e = 0` and `e = succ a`. When `e = 0`, `he`
becomes `x = d`, which implies `x ≤ succ d` by `le_succ_self`. When `e = succ a`, `he` becomes
`x = d + succ a`, which we observe is enough to prove `succ d ≤ x` because we can borrow `+1` from
`succ a` and add it to `d` to get `succ d`. To execute this strategy, we select the right branch of
the goal with `right` tactic and rewrite the goal into `x = succ d + a` with `use` tactic. We then
transfer `+1` from `succ a` to `d` in the hypothesis `he`, which becomes `he: x = succ d + a`. We
close the goal with `exact` tactic.
-/

/- Prove: If `succ(x) ≤ succ(y)` then `x ≤ y`. -/
/- theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by -/
/- Proof:
```
cases hx with a ha
rw[succ_eq_add_one, succ_eq_add_one, add_comm y 1, add_comm x 1, add_assoc] at ha
apply add_left_cancel at ha
use a
exact ha
```

Explanation: Our proof starts by rewriting `hx` as `ha: succ y = succ x + a`. We then rewrite `ha`
further into ` 1 + y = 1 + (x + a)` and apply `add_left_cancel` to cancel `1`'s on the lhs and rhs.
We close the goal with `exact`.

The server gives as shorter proof that uses `succ_add` and `succ_inj`:
```
cases hx with d hd
use d
rw [succ_add] at hd
apply succ_inj at hd
exact hd
```
-/

/- Prove:  If `x ≤ 1` then either `x = 0` or `x = 1`. -/
/- theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by -/
/- Proof:
```
cases hx with a ha
cases a with b
rw[add_zero] at ha
symm at ha
right
exact ha
symm at ha
rw[add_succ, one_eq_succ_zero] at ha
apply succ_inj at ha
apply add_right_eq_zero x b at ha
left
exact ha
```

Explanation: Our proof starts with rewriting `hx` into `ha: 1 = x + a` with `cases` tactic. We then
use `cases` again to consider two cases `a = 0` and `a = succ b`. When `a = 0`, we rewrite `ha`
into `x = 1` and select the right branch of the goal with `right` tactic, which we close with
`exact`. When `a = succ b`, we rewrite `ha` from `1 = x + succ b` to `succ (x + b) = succ 0` and
apply `succ_inj` to conclude that `x + b = 0`. Therefore, by `add_right_eq_zero` implies that
`x = 0`. We select the left branch of our goal and close it with `exact`.

The game server has a shorter proof that splits the proof into cases `x = 0` and `x = succ y`:
```
cases x with y
left
rfl
rw [one_eq_succ_zero] at hx ⊢
apply succ_le_succ at hx
apply le_zero at hx
rw [hx]
right
rfl
```
-/

/- Prove: If `x ≤ 2` then `x = 0` or `1` or `2`. -/
/- theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by -/
/- Proof:
```
cases x with a
left
rfl
rw[two_eq_succ_one] at hx
rw[two_eq_succ_one]
apply succ_le_succ a 1 at hx
apply le_one a at hx
cases hx
right
left
rw[one_eq_succ_zero]
rw[h]
rfl
right
right
rw[h]
rfl
```

Explanation: We start the proof by splitting it into two cases `x = 0` and `x = succ a`. When
`x = 0`, the goal is `0 = 0 ∨ 0 = 1 ∨ 0 = 2`. We select the right branch with `right` and close the
goal with `rfl`.  When `x = succ a`, our hypothesis is `hx: succ a ≤ 2` and our goal is
`succ a = 0 ∨ succ a = 1 ∨ succ a = 2`. To bring `hx` closer to something we can use to prove the
goal, we rewrite `2` as `succ 1` and apply `succ_le_succ` to rewrite `hx` into `a ≤ 1`. We then
apply `le_one` to rewrite `hx` into `a = 0 ∨ a = 1`. Next, we consider the left and right branches
of `hx` one by one using `cases hx`. When `a = 0`, we select the branch `succ a = 1` of the
goal using `right` and `left` tactics and close it by using the hypothesis `a = 0` and `rfl`. When
`a = 1`, we select the branch `succ a = succ 1`, apply the hypothesis and close the goal with `rfl`.
-/

/- ## Advanced Multiplication World -/
/- Prove: -/
/- theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by -/
/- Proof:
```
cases h with d hd
use d * t
rw [hd, add_mul]
rfl
```

Explanation: We start the proof by rewriting the hypothesis `h` into `hd: b = a + d`. We then use
the definition of `≤` to rewrite the goal into `b * t = a * t + d * t` with `use` tactic. Next,
we rewrite `b` into `a + d` by using `hd` and expand the product `(a + d) * t` into `a * t + d * t`
using `add_mul` tactic. We close the goal with rfl.
-/

/- Prove: -/
/- theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by -/
/- Proof:
```
contrapose! h
rw[h, mul_zero]
rfl
```

Explanation: We prove the logically equivalent contrapositive, which is `b = 0` implies `a * b = 0`.
We rewrite `b` into `0` and use `mul_zero` to rewrite the goal into `0 = 0`, which we close with
`rfl`.
-/

/- Prove: -/
/- theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by -/
/- Proof:
```
cases a with b
tauto
tauto
```

Explanation: We split the proof into two cases `a = 0` and `a = succ b`. When `a = 0`, our
hypothesis `h: a ≠ 0` is False, which means we can close the goal with `tauto` tactic because
`false → Q` is true for any `Q`. When `a = succ b`, our goal is `∃ n, succ b = succ n`, which we can
close with `tauto` because setting `n = b` makes the statement into a tautology.
-/

/- Prove: -/
/- theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by -/
/- Proof:
```
apply eq_succ_of_ne_zero at ha
cases ha
use w
rw[succ_eq_add_one, add_comm] at h
exact h
```

Explanation: First, we rewrite `ha` into `ha: ∃ n, a = succ n` by applying `eq_succ_of_ne_zero`. We
further rewrite `ha` into `h: a = succ w` with `cases`. Next, we rewrite the goal into `a = 1 + w`
with `use w`. Finally, we rewrite the `h` into `a = 1 + w` with `succ_eq_add_one` and `add_comm`,
and close the goal with `exact`.
-/

/- Prove: -/
/- theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by -/
/- Proof:
```
apply mul_left_ne_zero at h
apply one_le_of_ne_zero b at h
apply mul_le_mul_right 1 b a at h
rw[one_mul, mul_comm] at h
exact h
```

Explanation: First, we apply `mul_left_ne_zero` to `h` to rewrite `h` into `h: b ≠ 0`. We then
apply `one_le_of_ne_zero` to rewrite `h` into `h: 1 ≤ b`. Next, we `mul_le_mul_right` to `h` with
multiple `a` to rewrite `h` into  `1 * a ≤ b * a`. We then rewrite `h` into `a ≤ a * b` with
`one_mul` and `mul_comm` and close the goal with `exact`.
-/

/- Prove: -/
/- theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by -/
/- Proof:
```
have h2: x * y ≠ 0
rw[h]
exact one_ne_zero
apply (le_mul_right x y) at h2
rw[h] at h2
apply le_one x at h2
cases h2 with h0 h1
rw[h0, zero_mul, one_eq_succ_zero] at h
symm at h
tauto
exact h1
```

Explanation: To prove `x = 1`, we will show `x ≤ 1` and use `le_one` tactic. To show `x ≤ 1`, we
will use `le_mul_right` tactic. To use `le_mul_right`, we need the hypothesis `x * y ≠ 0`. We
introduce this hypothis as `h2` with `have` tactic and prove it first. We rewrite `x * y ≠ 0` into
`1 ≠ 0` using `h` and close the goal for `h2` with `exact one_ne_zero`. Next, we apply
`le_mul_right` at `h2` and rewrite `h2` into  `x ≤ x * y`. We then rewrite `h2` further into
`x ≤ 1` using `h` and apply `le_one` tactic at `h2` to conclude that `x = 0 ∨ x = 1`. We split the
two branches using `cases` tacitc. When `x = 0`, we rewrite `h` into `succ 0 = 0` using `zero_mul`,
`one_eq_succ_zero`, and `symm` tactics. Since `succ 0 ≠ 0`, we close this sub-goal with `tauto`
tactic. Finally, we close the main goal with `exact` tactic because the second branch `x = 1` of
`h1` is equal to the goal.
-/

/- Prove: -/
/- theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by -/
/- Proof:
```
apply eq_succ_of_ne_zero a at ha
cases ha with x hx
apply eq_succ_of_ne_zero b at hb
cases hb with y hy
rw[hx, hy, mul_succ]
nth_rewrite 2 [succ_eq_add_one]
rw[← add_assoc, ← succ_eq_add_one]
exact succ_ne_zero (succ x * y + x)
```

Explanation: We will show that `a * b` can be written as `succ` of a natural number and apply
`succ_ne_zero`. First, we apply `eq_succ_of_ne_zero` and `cases` to `ha` and `hb` to rewrite them
into `hx: a = succ x` and `hy: b = succ y`. We then use `hx` and `hy` to rewrite the goal into
`succ x * y + succ x ≠ 0`. We then use `succ_eq_add_one` and `add_assoc` to rewrite the goal into
`succ (succ x * y + x)`. We close the goal with `succ_ne_zero (succ x * y + x)`.
-/

/- Prove: -/
/- theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by -/
/- Proof:
```
contrapose! h
cases h with ha hb
exact mul_ne_zero a b ha hb
```

Explanation: We recognize that this theorem is the contrapositive of `mul_ne_zero`. We apply
`contrapose!` to `h`, split `a ≠ 0 ∧ b ≠ 0` into `ha: a ≠ 0` and `hb: b ≠ 0`  with `cases`, and
use `exact mul_ne_zero` to close the goal.
-/

/- Prove: -/
/- theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by  -/
/- Proof:
```
induction b with d hd generalizing c
rw[mul_zero] at h
symm at h
apply mul_eq_zero a c at h
cases h with az cz
tauto
symm
exact cz
cases c with e
rw[mul_zero] at h
apply mul_eq_zero a (succ d) at h
cases h with hl hr
tauto
exact hr
repeat rw[mul_succ] at h
apply add_right_cancel at h
apply hd at h
rw[h]
rfl
```

Explanation: We use induction on `b` to prove the following statement
`∀ c ∈ ℕ, a * b = a * c → b = c`. Having `c` be any natural number is crucial for us to be able to
apply the inductive hypothesis. The syntax for letting `c` vary over its domain is `generalizing c`.

The base case is `a ≠ 0` and  `h: a * 0 = a * c` implies `0 = c`. We rewrite `h` into `a * c = 0`,
use `mul_eq_zero` to conclude that `a = 0` or `c = 0`, and consider each branch separately using
`cases`. We close the branch `a = 0` with `tauto` because one of our hypotheses is `a ≠ 0`. The
branch `c = 0` gives us the goal using `exact`.

The inductive hypothesis is `hd: ∀ (c : ℕ), a * d = a * c → d = c` and in the inductive step we
show that `ha: a ≠ 0` and `h: a * succ d = a * c` imply `succ d = c`. We split `hd` into `cases`
when `c = 0` and `c = succ e`. When `c = 0`, we rewrite `h` into `a * succ d = 0` and close the
goal using `mul_eq_zero`, `cases`, and `a ≠ 0`. When `c = succ e`, we rewrite `h` into
`h: a * d + a = a * e + a` and use `add_right_cancel` to further rewrite `h` into `a * d = a * e`.
We then apply the inductive hypothesis `hd` to conclude that `d = e` and close the goal by
rewriting `succ d = succ e` into `succ e = succ e` and using `rfl`.
-/

/- Prove: -/
/- theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by -/
/- Proof:
```
nth_rewrite 2 [← mul_one a] at h
apply mul_left_cancel a b 1 ha at h
exact h
```

Explanation: We recognize that this is a special case of `mul_left_cancel`. We rewrite `h` into
`a * b = a * 1` and apply `mul_left_cancel`.
-/



/- Template -/
/- Prove: -/
/- Proof:
```
```

Explanation:
-/
