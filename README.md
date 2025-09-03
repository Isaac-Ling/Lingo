# Lingo

An implementation of Martin-Löf Type Theory, following closely to the Homotopy Type Theory (HoTT) book.

## Rosetta Stone

| English                 | Math                 | Lingo            |
|-------------------------|----------------------|------------------|
| Initial Type            | $\mathbb{0}$         | `_\|_`           |
| Terminal Type           | $\mathbb{1}$         | `T`              |
| Singleton Term          | $\ast$               | `*`              |
| Coproduct               | $A + B$              | `A + B`          |
| Product                 | $A \times B$         | `A x B`          |
| Sigma                   | $\sum_{a : A} B(a)$  | `(a : A) x B a`  |
| Arrow                   | $A \rightarrow B$    | `A -> B`         |
| Pi                      | $\prod_{a : A} B(a)$ | `(a : A) -> B a` |
| Explicit Lambda         | $\lambda (a : A). b$ | `\(a : A). b`    |
| Implicit Lambda         | $\lambda a. b$       | `\a. b`          |
| Left Injection          | $\text{inl}(a)$      | `inl(a)`         |
| Right Injection         | $\text{inr}(b)$      | `inr(b)`         |
| Natural Numbers         | $\mathbb{N}$         | `Nat`            |
| Natural Number          | $4$                  | `4`              |
| Successor               | $\text{succ}(4)$     | `succ(4)`        |
| Identity                | $A = B$              | `A = B`          |
| Reflexivity             | $\text{refl}_A$      | `refl[A]`        |
| Universe                | $\text{Univ}_2$      | `U2`             |
| Function Extensionality | $\text{funext}(p)$   | `funext(p)`      |
| Type annotation         | $a : A$              | `a : A`          |
| Definition              | $a := \text{foo}$    | `a := foo`       |

## Induction

The notation for induction operators follows that of the HoTT book, e.g. defining the double function using natural induction would be:

```
double : Nat -> Nat
double := \n. ind[Nat](Nat, 0, n. y. succ(succ(y)), n)
```

# Implicits

Leading pi types can be left explicit by writing `{A : U} -> ...`. Semantically this is equivalent to a standard pi type, but it doesn't need a corresponding leading lambda in its definition. It also can be left out when applying another term to a term of this type.

For example, we can define and use the identity function with implicits like so:

```
id : {A : U} -> A -> A
id := \a. a

#check id 32
```

The check on the last line with give `id {Nat} 32 =>* 32 : Nat`.

Implicits can be made explicit in both a lambda and an application by using curly braces:

```
id : {A : U} -> A -> A
id := \{B}. \(a : B). a

#check id {Nat} 32
```

# Pragmas

Use the `#check` pragma to print out the normal form of the term supplied, along with it's type.

Using `#type` will print out the type of the given term, and `#eval` will print out the normal form of the given term.

Use the `#include` pragma to include another Lingo source file. For example,

```
#include "foo"
```

Will mean that the source of `foo.lingo` is included at the location of the include statement.
