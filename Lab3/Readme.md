# Lab 3

## Table of Contents

1. [Theme](#theme)
2. [Tasks](#tasks)
3. [Useful Links](#useful-links)

<hr><br>

## Theme

### Coinduction and Corecursion in Dafny

<br>

## Tasks

- _Define in Dafny the conatural numbers as a coinductive datatype and use this for:_

  - _explaining why the following coinductive property does not hold:_

    ```dafny
    lemma ConstructorConat(n: Conat)
        ensures n != Succ(n)
    {
        // why?
    }
    ```

  - _showing that the constructor successor is injective_
  - _defining the constant (as a corecursive function) `∞ = s(s(. . .))`_
  - _defining the addition of conaturals_
  - _showing that by adding `∞` to itself, it remains unchanged._

- _Define the parametric streams as coinductive datatype using the rule (**where s ranges over streams**):_

$$\dfrac{s}{cons(a, s)},\ \forall a \in A$$

- _Use it for:_

  - _corecursively defining the pointwise addition of two streams of integers `add(s, s′)`_

  - _defining a parametric integer constant stream `cnst(n)`_

  - _proving by coinduction that `add(s, cnst(0)) = s`_

  - _defining coinductively the predicate `leq(s, s′)`_

  - _defining the stream `blink`_

  - _proving by coinduction that `leq(cnst(0), blink)`_

  - _defining a function that zips two streams_

  - _proving that by zipping `cnst(0)` and `cnst(1)` you obtain `blink`_

<br>

## Useful Links

### Dafny Group

[Coinductive Datatypes](https://dafny.org/dafny/DafnyRef/DafnyRef)
