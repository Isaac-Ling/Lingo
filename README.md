# Lingo

An implementation of Martin-Löf Type Theory, following closely to the Homotopy Type Theory (HoTT) book.

## Rosetta Stone

| English          | Math                | Lingo            |
|------------------|---------------------|------------------|
| Initial Type     | $ \mathbb{0} $      | `_|_`            |
| Terminal Type    | $ \mathbb{1} $      | `T`              |
| Singleton Term   | $ \ast $            | `*`              |
| Coproduct        | $ A + B $           | `A + B`          |
| Product          | $ A \times B $      | `A x B`          |
| Sigma            | $ \sum_{a : A} B $  | `(a : A) x B`    |
| Arrow            | $ A \rightarrow B $ | `A -> B`         |
| Pi               | $ \prod_{a : A} B $ | `(a : A) -> B`   |
| Lambda           | $ \lambda a. b $    | `\a. b`          |
| Left Injection   | $ \text{inl}(a) $   | `inl(a)`         |
| Right Injection  | $ \text{inr}(b) $   | `inr(b)`         |
| Natural Numbers  | $ \mathbb{N} $      | `Nat`            |
| Natural Number   | $ 4 $               | `4`              |
| Successor        | $ \text{succ}(4) $  | `succ(4)`        |
| Identity         | $ A = B $           | `A = B`          |
| Reflexivity      | $ \text{refl} $     | `refl`           |
| Universe         | $ #text{Univ}_2 $   | `U2`             |
| Type annotation  | $ a : A $           | `a : A`          |
| Definition       | $ a := \text{foo} $ | `a := foo`       |

## Induction

The notation for induction operators follows that of the HoTT book, e.g. defining the double function using natural induction would be:

```
double : Nat -> Nat
double := \n. ind[Nat](Nat, 0, n. y. succ(succ(y)), n)
```

# Pragmas

Use the `#check` pragma to print out the normal form of the term supplied, along with it's type.
