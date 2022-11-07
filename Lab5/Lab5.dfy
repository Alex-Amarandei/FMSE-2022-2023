// Exercise 1

// Block Inference Rule
method exampleBlock() {
    var x: int;

    assume x >= 0;              // P
    x := x + 1;                 // A
    assert x > 0;               // Q

    assume x >= 0;              // P
    {       
        x := x + 1;             // {A}
    }
    assert x > 0;               // Q
}

// Implication Inference Rule
method exampleImplies() {
    var x: int;

    x := 3;                     // P'

    assume x % 5 == 3;          // P
    x := x + 2;                 // A
    assert x % 5 == 0;          // Q

    assert (x - 5) % 5 == 0;    // Q' 


    assume x == 3;              // P'
    x := x + 2;                 // A
    assert (x - 5) % 5 == 0;    // Q'
}

// If-Else Inference Rule
method exampleIfElse() {
    var x: int, y: int;

    assume x < 0 && y > 0;      // P && E
    x := x * (-1);              // A
    assert x * y > 0;           // Q

    assume x < 0 && y <= 0;     // P && !E
    y := y - 1;                 // B
    assert x * y > 0;           // Q

    assume x < 0;               // P
    if (y > 0) {                // if (E)
        x := x * (-1);          // A
    } else {                    // !E
        y := y - 1;             // B
    }
    assert x * y > 0;           // Q
}

// While Inference Rule
method exampleWhile() {
    var x: int, n: int;

    assume x <= n && x < n;     // INV && E
    x := x + 1;                 // A
    assert x <= n;              // Q
    
    assume x <= n;              // INV
    while (x < n)               // while (E)
        invariant x <= n        // INV
    {                           
        x := x + 1;             // A
    }
    assert x <= n && x >= n;    // Q
    // equivalent to: assert x == n;
}

// Exercise 2
method m3(a: int, b: int) returns (q: int, r: int)
    decreases *
{
    q := 0;
    r := a;
    while (r >= b)
        invariant a == b * q + r
        decreases *
    {
        r := r - b;
        q := q + 1;
    }
}

// the m3 method simulates a division operation having both quotient and remainder calculated
// but given that it is not properly defined, multiple problems arise

// a decreases clause cannot be found under the current circumstances due to the fact that the combination of
// (positive a and negative b) or (negative a and negative b, with a >= b) or (a > 0 and b == 0) result
// in an infinite loop

// if, for instance, some preconditions and postconditions (i.e. specifications) were established
// the situation would have been different and would allow for multiple invariants and decreases clauses

// While Invariant Proof
method m3WhileInvariantProof(a: int, b: int) 
    decreases *
{
    var q := 0;
    var r := a;

    assume a == b * q + r && r >= b;    
    r := r - b;
    q := q + 1;
    assert a == b * q + r;

    assume a == b * q + r;
    while(r >= b) 
        invariant a == b * q + r
        decreases *
    {
        r := r - b;
        q := q + 1;
    }
    assert a == b * q + r && r < b;
}

// Helpful function for computing the square of a number
function square(x: int): int
    requires x > 0
{
    x * x
}

// Helpful function for computing the sum of the first n squares
function sumOfFirstNSquares(n: int): int {
    n * (n + 1) * (2 * n + 1) / 6
}

// Exercise 3
method m4(n: int) returns (s: int)
    requires n >= 0
{
    var i, k : int;

    s := 0;
    k := 1;
    i := 1;

    while (i <= n)
        invariant 1 <= i <= n + 1
        invariant k == square(i) 
        invariant s == sumOfFirstNSquares(i - 1)
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i + 1;
    }
}

// the m4 method calculates the sum of the first n squares starting from 1 (i.e. ∑x^2, with 1 <= x <= n)
// ∑x^2 = n(n+1)(2n+1)/6, with 1 <= x <= n

method m4WhileInvariantProof1(n: int)
    requires n >= 0
{
    var i, k : int;
    var s := 0;
    k := 1;
    i := 1;

    assume k == square(i) && i <= n;
    s := s + k;
    k := k + 2 * i + 1;
    i := i + 1;
    assert k == square(i);

    assume k == square(i);
    while (i <= n) 
        invariant k == square(i) 
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i + 1;
    }
    assert k == square(i) && i > n;
}

method m4WhileInvariantProof2(n: int)
    requires n >= 0
{
    var i, k : int;
    var s := 0;
    k := 1;
    i := 1;

    assume s == sumOfFirstNSquares(i - 1) && i <= n;
    s := s + k;
    k := k + 2 * i + 1;
    i := i + 1;
    assert s == sumOfFirstNSquares(i - 1);

    assume s == sumOfFirstNSquares(i - 1);
    while (i <= n) 
        invariant k == square(i) 
        invariant s == sumOfFirstNSquares(i - 1)  
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i + 1;
    }
    assert s == sumOfFirstNSquares(i - 1) && i > n;
}

// Exercise 4
predicate largestTwoSpec(a: seq<int>, m1: int, m2: int)
    requires |a| > 1
{
    exists indexM1, indexM2 :: 0 <= indexM1 < |a| && 0 <= indexM2 < |a| && 
    indexM1 != indexM2 && 
    m1 == a[indexM1] && m2 == a[indexM2] &&
    forall k :: 0 <= k < |a| && k != indexM1 ==> a[k] <= m2 &&
    forall k :: 0 <= k < |a| ==> a[k] <= m1
}

method twoLargest(a: seq<int>) returns (m1: int, m2: int)
    requires |a| > 1
    ensures largestTwoSpec(a, m1, m2) 
{
    var indexM1, indexM2 := 1, 0;

    if (a[0] > a[1]) {
        indexM1 := 0;
        indexM2 := 1;
    }

    for i := 2 to |a|
        invariant indexM1 != indexM2
        invariant 0 <= indexM1 < |a|
        invariant 0 <= indexM2 < |a|
        invariant forall k :: 0 <= k < i ==> a[k] <= a[indexM1]
        invariant exists k :: 0 <= k < i && a[k] == a[indexM1]
        invariant forall k :: 0 <= k < i && k != indexM1 ==> a[k] <= a[indexM2] <= a[indexM1]
        invariant exists k :: 0 <= k < i && a[k] == a[indexM2]
    {
        if (a[i] > a[indexM1]) {
            indexM2 := indexM1;
            indexM1 := i;
        } else if (a[i] > a[indexM2]) {
            indexM2 := i;
        }
    }

    m1, m2 := a[indexM1], a[indexM2];

    return m1, m2;
}

// Exercise 5
predicate properDivision(a: int, b: int, q: int, r: int) {
    a == b * q + r && r < b
}

method m3_v2(a: int, b: int) returns (q: int, r: int)
    requires 0 < b <= a
    ensures properDivision(a, b, q, r)
{
    q := 0;
    r := a;
    while (r >= b)
        decreases r
        invariant a == b * q + r
    {
        r := r - b;
        q := q + 1;
    }
}

// Exercise 6
predicate sumOfSquares(n: int, s: int) 
    requires n >= 0
{
    s == sumOfFirstNSquares(n)
}

method m4_v2(n: int) returns (s: int)
    requires n >= 0
    ensures sumOfSquares(n, s)
{
    var i, k : int;

    s := 0;
    k := 1;
    i := 1;

    while (i <= n)
        invariant i <= n + 1
        invariant k == square(i) 
        invariant s == sumOfFirstNSquares(i - 1)
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i + 1;
    }
}