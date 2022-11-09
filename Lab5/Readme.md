# Lab 5

## Table of Contents

1. [Theme](#theme)
2. [Tasks](#tasks)
3. [Useful Links](#useful-links)

<hr><br>

## Theme

### Specification of Programs and Verification in Dafny I

<br>

## Tasks

- _Write similar examples of instances of the inference rules of the Floyd-Hoare logic. Namely:_

  - _Assignment_
  - _Composition_
  - _Block_
  - _Implies_
  - _If-Else_
  - _While_

- _Find and prove (using Dafny) an invariant of the loop for the following method:_

  ```dafny
    method m3(a: int, b: int) returns (q: int, r: int)
      decreases *
    {
      q := 0;
      r := a;
      while (r >= b)
        decreases *
      {
        r := r - b;
        q := q + 1;
      }
    }
  ```

  - _Can you find an expression decreased by the loop (a variant)? If yes, check it by replacing \* with that expression. If necessary, you may add preconditions to avoid infinite computations._

- _Find and prove (using Dafny) an invariant of the loop for the following method:_

  ```dafny
    method m4(n: int) returns (s: int)
      requires n >= 0
    {
      var i, k: int;
      s := 0;
      k := 1;
      i := 1;
      while (i <= n)
      {
        s := s + k;
        k := k + 2 * i + 1;
        i := i+1;
      }
    }
  ```

- _Sequences in Dafny_

  - _Write a method that computes the two largest elements from an array._

  - _Write a specification (precondition, postcondition) for that method._

  - _Prove that the method satisfies the specification, using Dafny._

- _Write a specification for m3 and show, using Dafny, that the method satisfies it._

- _Write a specification for m4 and show, using Dafny, that the method satisfies it._

<br>

## Useful Links

### João F. Ferreira PhD

[Hoare Logic](https://web.tecnico.ulisboa.pt/~joaofernandoferreira/1920/SoftSpec/02-hoare.html#/)

[Hoare Logic (Extended)](https://web.tecnico.ulisboa.pt/~joaofernandoferreira/1920/SoftSpec/03-hoare-cont.html#/)

### Verification Corner

[Basics of Specification and Verification](https://www.youtube.com/watch?v=oLS_y842fMc&t=4s)

[Specifications](https://www.youtube.com/watch?v=HOl11mP4V68)

[Partial Solutions](https://www.youtube.com/watch?v=BLQo5d3hI4M)
