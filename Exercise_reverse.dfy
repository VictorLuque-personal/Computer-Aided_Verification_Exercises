// You are given the following definitions

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate sorted(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

predicate sortedDec(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x >= y && sortedDec(xs)
}

function elems<T> (l:List<T>) : multiset<T>
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

// You must implement and verify function a reverse function satisfying 
// the specification below. The implementation should use an auxiliary function
// with an accumulator parameter, so that the time cost should be in O(n)

function reverse (l:List<int>) : (res:List<int>)
requires sorted(l)
ensures  sortedDec(res)
ensures  elems(res) == elems(l)
{
   match l
       case Nil        => Nil
       case Cons(x,xs) =>  
                           sortedAddFirst(l);
                           assert getFirst(l).0 == xs && getFirst(l).1 == x;
                           assert sorted(l) ==> forall i | i in elems(xs) :: x <= i;
                           sortedDecAddLast(x, reverse(xs));
                           add(reverse(xs),x)
}

function method add (l:List<int>,x:int): (res:List<int>)
ensures elems(res)==elems(l)+multiset{x}
ensures length(res) == length(l) + 1
{
    match l
       case Nil        => Cons(x,Nil)
       case Cons(y,ys) => Cons(y,add(ys,x))
}


function method length (l:List<int>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

lemma {:induction l} sortedDecAddLast(x:int, l:List<int>)
requires sortedDec(l)
requires forall i | i in elems(l) :: x <= i
ensures sortedDec(add(l,x))
{
   if (l == Nil) {}
   else {
      addingLastEQ(l);
      assert add(getLast(l).0, getLast(l).1) == l;
      assert getLast(l).1 in elems(l);
      assert getLast(l).1 >= x;
      assert add(add(getLast(l).0, getLast(l).1),x) == add(l,x);
      ifLastGE_sortedDec(l,x);
   }
}

lemma {:induction l} ifLastGE_sortedDec(l:List<int>, x:int)
requires length(l) > 0
requires sortedDec(l)
requires getLast(l).1 >= x
ensures sortedDec(add(l,x))
{}

lemma {:induction l} addingLastEQ(l:List<int>)
requires length(l) > 0
ensures add(getLast(l).0, getLast(l).1) == l
{}

function method getLast(l:List<int>):(res:(List<int>,int))
requires length(l) > 0
ensures elems(l) == elems(res.0) + multiset{res.1}
{
   match l
      case Cons(x,Nil) => (Nil,x)
      case Cons(x, xs)         => var (list,last) := getLast(xs);
                                  (Cons(x,list),last)
}

function method getFirst(l:List<int>):(res:(List<int>,int))
requires length(l) > 0
ensures elems(l) == elems(res.0) + multiset{res.1}
{
   match l
      case Cons(x,xs) => (xs, x)
}

lemma {:induction l} sortedAddFirst(l:List<int>)
requires length(l) > 0
requires sorted(l)
ensures forall i | i in elems(getFirst(l).0) :: getFirst(l).1 <= i;
{
   assert Cons(getFirst(l).1, getFirst(l).0) == l;
   if length(Cons(getFirst(l).1, getFirst(l).0)) == 1 {}
   else {
      assert sorted(Cons(getFirst(l).1, getFirst(l).0)) ==> getFirst(l).1 <= getFirst(getFirst(l).0).1;
   }
}