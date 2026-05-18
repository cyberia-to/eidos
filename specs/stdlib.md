---
tags: eidos, spec
crystal-type: spec
crystal-domain: eidos
status: draft
---
# stdlib

the eidos standard library. all definitions here are eidos declarations — they elaborate to kernel terms and are admitted only after the kernel accepts the proof. the simp default set is drawn from lemmas marked `@[simp]`.

the ordering follows the dependency graph. earlier definitions are available to later ones.

## propositional logic

### False

```
inductive False : Prop where
  -- no constructors
```

eliminator: `False.elim : {C : Sort u} → False → C`

### True

```
inductive True : Prop where
  | intro : True
```

`True.intro : True`

### And

```
inductive And (P Q : Prop) : Prop where
  | intro : P → Q → And P Q
```

projections:

```
def And.left  : And P Q → P := fun h => match h with | And.intro p _ => p
def And.right : And P Q → Q := fun h => match h with | And.intro _ q => q
```

notation: `P ∧ Q = And P Q`

### Or

```
inductive Or (P Q : Prop) : Prop where
  | left  : P → Or P Q
  | right : Q → Or P Q
```

notation: `P ∨ Q = Or P Q`

### Not

```
def Not (P : Prop) : Prop := P → False
```

notation: `¬P = Not P`

### Eq

```
inductive Eq {A : Type_0} (a : A) : A → Prop where
  | refl : Eq a a
```

notation: `a = b = Eq a b`

key lemmas:

```
theorem Eq.symm      : a = b → b = a
theorem Eq.trans     : a = b → b = c → a = c
theorem Eq.transport : {P : A → Prop} → a = b → P a → P b  -- transport a proof along equality
theorem map_eq       : (f : A → B) → a = b → f a = f b
theorem fun_eq       : f = g → (x : A) → f x = g x
```

`@[simp] theorem Eq.self_eq_true : a = a = True`

### Iff

```
def Iff (P Q : Prop) : Prop := And (P → Q) (Q → P)
notation: P ↔ Q = Iff P Q

theorem Iff.intro    : (P → Q) → (Q → P) → P ↔ Q
def Iff.forward  (h : P ↔ Q) : P → Q := And.left  h
def Iff.backward (h : P ↔ Q) : Q → P := And.right h
```

## Nat

```
inductive Nat : Type_0 where
  | zero : Nat
  | next : Nat → Nat
```

notation: `0 = Nat.zero`, `1 = Nat.next 0`, etc. numeric literals elaborate to iterated `next`.

### arithmetic

```
def Nat.add : Nat → Nat → Nat
  | n, 0      => n
  | n, next m => next (Nat.add n m)

def Nat.mul : Nat → Nat → Nat
  | _, 0      => 0
  | n, next m => Nat.add (Nat.mul n m) n

def Nat.pred : Nat → Nat
  | 0      => 0
  | next n => n
```

```
@[simp] theorem Nat.mul_zero : n * 0 = 0
@[simp] theorem Nat.zero_mul : 0 * n = 0
@[simp] theorem Nat.mul_one  : n * 1 = n
@[simp] theorem Nat.one_mul  : 1 * n = n
```

notation: `n + m`, `n * m`

### order

```
inductive Nat.le (n : Nat) : Nat → Prop where
  | refl : Nat.le n n
  | grow : Nat.le n m → Nat.le n (next m)

def Nat.lt (n m : Nat) : Prop := Nat.le (next n) m
```

notation: `n ≤ m = Nat.le n m`, `n < m = Nat.lt n m`

### key lemmas (Nat)

required for nox T2 (bound monotonicity):

```
@[simp] theorem Nat.zero_add   : 0 + n = n
@[simp] theorem Nat.add_zero   : n + 0 = n
@[simp] theorem Nat.next_add   : next n + m = next (n + m)
@[simp] theorem Nat.add_next   : n + next m = next (n + m)
        theorem Nat.add_comm   : n + m = m + n
        theorem Nat.add_assoc  : (n + m) + k = n + (m + k)
        theorem Nat.le_refl    : n ≤ n
        theorem Nat.le_trans   : n ≤ m → m ≤ k → n ≤ k
        theorem Nat.le_antisymm: n ≤ m → m ≤ n → n = m
        theorem Nat.next_le_next : n ≤ m → next n ≤ next m
        theorem Nat.le_next    : n ≤ next n
        theorem Nat.zero_le    : 0 ≤ n
        theorem Nat.le_add_right : n ≤ n + m
        theorem Nat.le_add_left  : n ≤ m + n
        theorem Nat.max_le     : n ≤ k → m ≤ k → max n m ≤ k
        theorem Nat.le_max_left  : n ≤ max n m
        theorem Nat.le_max_right : m ≤ max n m
```

```
def Nat.max : Nat → Nat → Nat
  | 0,      m      => m
  | n,      0      => n
  | next n, next m => next (Nat.max n m)
```

### Nat.rec (built-in eliminator)

the eliminator for Nat is structural recursion. the induction tactic produces:

```
ELIM(Nat_id, motive,
  [case_zero, case_next],
  target)
```

where `case_zero : motive 0` and `case_next : (n : Nat) → motive n → motive (next n)`.

## Bool

```
inductive Bool : Type_0 where
  | false : Bool
  | true  : Bool

def Bool.and : Bool → Bool → Bool
  | true,  b => b
  | false, _ => false

def Bool.or : Bool → Bool → Bool
  | false, b => b
  | true,  _ => true

def Bool.not : Bool → Bool
  | true  => false
  | false => true

def Bool.decEq : (a b : Bool) → Decidable (a = b)
```

```
@[simp] theorem Bool.not_true  : Bool.not true  = false
@[simp] theorem Bool.not_false : Bool.not false = true
```

notation: `a && b`, `a || b`, `!a`

### decidable

```
inductive Decidable (P : Prop) : Type_0 where
  | isFalse : ¬P → Decidable P
  | isTrue  : P  → Decidable P
```

`Decidable` instances for Nat equality and order allow `decide` tactic on concrete propositions.

## Ordering

comparison result, used by the Ord interface:

```
inductive Ordering : Type_0 where
  | lt : Ordering
  | eq : Ordering
  | gt : Ordering
```

## Ord

comparison interface for totally ordered types:

```
class Ord (A : Type_0) where
  compare : A → A → Ordering
```

`[Ord A]` in a signature is an instance argument — the elaborator resolves it automatically when a unique instance is in scope.

```
instance Ord Nat where
  compare : Nat → Nat → Ordering
    | 0,      0      => Ordering.eq
    | 0,      next _ => Ordering.lt
    | next _, 0      => Ordering.gt
    | next n, next m => compare n m
```

## List

```
inductive List (A : Type_0) : Type_0 where
  | nil  : List A
  | link (head : A) (tail : List A) : List A
```

notation: `[] = List.nil`, `a :: l = List.link a l`, `[a, b, c]` sugar.

### basic operations

```
def List.length : List A → Nat
  | []      => 0
  | _ :: l  => next (List.length l)

def List.append : List A → List A → List A
  | [],     l => l
  | h :: t, l => h :: List.append t l

def List.map : (A → B) → List A → List B
  | _, []      => []
  | f, h :: t  => f h :: List.map f t

def List.reverse : List A → List A
  | []      => []
  | h :: t  => List.append (List.reverse t) [h]
```

```
@[simp] theorem List.length_nil  : List.length [] = 0
@[simp] theorem List.length_link : List.length (a :: l) = next (List.length l)
@[simp] theorem List.append_nil  : l ++ [] = l
@[simp] theorem List.nil_append  : [] ++ l = l
```

notation: `l₁ ++ l₂ = List.append l₁ l₂`

### permutations

required for nox T1 (trace equivalence) and T3 (sort permutation):

```
inductive List.Perm : List A → List A → Prop where
  | nil   : Perm [] []
  | prepend : Perm l₁ l₂ → Perm (a :: l₁) (a :: l₂)
  | swap  : Perm (a :: b :: l) (b :: a :: l)
  | trans : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃
```

key lemmas:

```
theorem List.Perm.refl   : Perm l l
theorem List.Perm.symm   : Perm l₁ l₂ → Perm l₂ l₁
theorem List.Perm.append_comm : Perm (l₁ ++ l₂) (l₂ ++ l₁)
```

### sorted

a list is sorted when each adjacent pair satisfies the order:

```
inductive List.Sorted {A : Type_0} [Ord A] : List A → Prop where
  | nil  : List.Sorted []
  | one  : List.Sorted [a]
  | link : compare a b = Ordering.lt ∨ compare a b = Ordering.eq →
           List.Sorted (b :: l) → List.Sorted (a :: b :: l)
```

### merge sort

required for nox T3:

```
def List.merge {A : Type_0} [Ord A] : List A → List A → List A
def List.mergeSort {A : Type_0} [Ord A] : List A → List A

theorem List.mergeSort_perm     : List.Perm l (List.mergeSort l)
theorem List.mergeSort_sorted   : List.Sorted (List.mergeSort l)
theorem List.mergeSort_idempotent : List.mergeSort (List.mergeSort l) = List.mergeSort l
```

### membership and subset

```
inductive List.Mem (a : A) : List A → Prop where
  | head : List.Mem a (a :: l)
  | tail : List.Mem a l → List.Mem a (b :: l)

notation: a ∈ l = List.Mem a l

theorem List.Perm.mem_iff : Perm l₁ l₂ → (a ∈ l₁ ↔ a ∈ l₂)
```

## Vec

```
inductive Vec (A : Type_0) : Nat → Type_0 where
  | nil  : Vec A 0
  | link (head : A) (tail : Vec A n) : Vec A (next n)
```

length is tracked in the type. out-of-bounds access is a type error, not a runtime error.

```
def Vec.get : Vec A n → Fin n → A
def Vec.map : (A → B) → Vec A n → Vec B n

theorem Vec.get_map : Vec.get (Vec.map f v) i = f (Vec.get v i)
```

## Fin

```
inductive Fin : Nat → Type_0 where
  | mk : (i : Nat) → i < n → Fin n
```

`Fin n` is the type of natural numbers strictly less than n. used for safe indexing.

```
def Fin.index   : Fin n → Nat
def Fin.bounded : (i : Fin n) → i.index < n

def Fin.zero : Fin (next n) := Fin.mk 0 (Nat.next_le_next (Nat.zero_le _))
def Fin.next : Fin n → Fin (next n)
```

## well-founded recursion

required for prysm termination (Newman's lemma) and the nox bound proof:

```
-- Accessible: accessibility predicate
inductive Accessible {A : Type_0} (r : A → A → Prop) : A → Prop where
  | intro : ((y : A) → r y x → Accessible r y) → Accessible r x

def WellFounded {A : Type_0} (r : A → A → Prop) : Prop :=
  (x : A) → Accessible r x

-- Nat is well-founded under <
theorem Nat.lt_wf : WellFounded Nat.lt

-- well-founded recursion principle
theorem WellFounded.recursion :
  WellFounded r → (x : A) → ((y : A) → r y x → C y) → C x
```

the `induction` tactic uses `Accessible` when the induction measure is not syntactic.

## sigma and prod types

```
inductive Sigma {A : Type_0} (B : A → Type_0) : Type_0 where
  | mk : (a : A) → B a → Sigma B

notation: ⟨a, b⟩ = Sigma.mk a b
          (x : A) × B x = Sigma (fun x => B x)

inductive Prod (A B : Type_0) : Type_0 where
  | mk : A → B → Prod A B

notation: A × B = Prod A B
          (a, b) = Prod.mk a b
```

## Exists

```
inductive Exists {A : Type_0} (P : A → Prop) : Prop where
  | intro : (a : A) → P a → Exists P

notation: ∃ x, P x = Exists (fun x => P x)
```

`Exists.intro a ha : ∃ x, P x` introduces an existential. `cases h` on `h : ∃ x, P x` gives the witness and proof.

```
theorem Exists.elim : (∃ x, P x) → (∀ x, P x → Q) → Q
```

## relation properties

required for prysm Newman's lemma:

```
def Reflexive  (r : A → A → Prop) : Prop := (x : A) → r x x
def Symmetric  (r : A → A → Prop) : Prop := (x y : A) → r x y → r y x
def Transitive (r : A → A → Prop) : Prop := (x y z : A) → r x y → r y z → r x z

-- confluence and local confluence
def Confluent (r : A → A → Prop) : Prop :=
  (x y z : A) → Closure r x y → Closure r x z →
    ∃ w, Closure r y w ∧ Closure r z w

def LocallyConfluent (r : A → A → Prop) : Prop :=
  (x y z : A) → r x y → r x z →
    ∃ w, Closure r y w ∧ Closure r z w

-- reflexive-transitive closure
inductive Closure (r : A → A → Prop) : A → A → Prop where
  | refl  : Closure r x x
  | via   : r x y → Closure r y z → Closure r x z

-- Newman's lemma
theorem newman :
  WellFounded (fun x y => r y x) →    -- r is terminating (well-founded on reversed r)
  LocallyConfluent r →
  Confluent r
```

proof sketch: well-founded induction on x. for any y, z with r* x y and r* x z, if x = y or x = z the result is immediate. otherwise, x reduces to x₁ (toward y) and x₂ (toward z). by local confluence: x₁ and x₂ join at some w₁. by IH on x₁ (which is r-smaller than x): y and w₁ join at some w₂. by IH on x₂: z and w₁ join at some w₃. by IH on w₁: w₂ and w₃ join. this gives the required join for y and z.

## simp default set

the default simp lemmas (applied automatically by `simp` with no arguments):

```
Nat.zero_add, Nat.add_zero, Nat.next_add, Nat.add_next
Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul
List.length_nil, List.length_link
List.append_nil, List.nil_append
Bool.not_true, Bool.not_false
Eq.self_eq_true
```

additional lemmas are added to the simp set via `@[simp]` attribute on their declaration.

`And.intro`, `Or.left`, and `Or.right` are not in the default set — applying them unconditionally would loop or over-split goals.
