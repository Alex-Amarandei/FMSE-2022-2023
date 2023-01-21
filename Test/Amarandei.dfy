/*
  The class FibList includes Fibonacci-like lists: 
  * each list L has at least two elements, and
  * for valid positions i, i > 1, L[i] = L[i-1] + L[i-2].
  The goal is to specify and implement this in Dafny this list,
  following the next template (for each function/predicate/method
  add the specification and the code that formalizes/implements
  the description from the comment.)
*/

class FibList
{
    var size: int;
    var container: array<int>;
    ghost var capacity: int;
     
    function Contents() : seq<int>
    requires Valid()
    reads this, this.container
    {
        this.container[0..this.size]
    }

    constructor(aCapacity: int) 
    requires aCapacity >= 2
    ensures size == 2 && this.container.Length == aCapacity
    { 
        this.container := new int[aCapacity](_ => 0);
        this.size := 2;
        this.capacity := aCapacity;
    }

    predicate Valid()
    reads this, this.container
    {
        this.size <= this.container.Length &&
        this.container.Length == this.capacity &&
        forall i :: 2 <= i < this.size ==> this.container[i] == (this.container[i-1] + this.container[i-2])
    }

    method init(fst: int, snd: int)
    modifies this, this.container
    requires this.size >= 2
    requires this.capacity >= 2
    requires this.container.Length >= 2
    requires fst < snd
    ensures this.container[0] == fst && this.container[1] == snd
    {
        this.container[0] := fst;
        this.container[1] := snd;
    }

    method push()
    modifies this, this.container
    requires Valid()
    requires this.container.Length < this.capacity
    ensures this.size == old(this.size) + 1
    ensures Valid()
    {
        this.container[size] := this.container[size - 1] + this.container[size - 2];
        size := size + 1;
    }


    method pop()
    modifies this
    requires this.size > 2
    ensures this.size == old(this.size) - 1
    ensures Valid()
    {
        
    }

    method search(x: int) returns (res: bool)
    requires Valid()
    ensures Valid()
    ensures exists i :: 0 <= i < this.size && this.container[i] == x ==> res == true
    ensures !exists i :: 0 <= i < this.size && this.container[i] == x ==> res == false
    {
        for i: nat := 0 to this.size {
            if (this.container[i] == x) {
                res := true;
            }
        }
        
        res := false;
    }
}