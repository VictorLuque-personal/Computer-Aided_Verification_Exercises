//Given an array of positive integers we want to know if it "evenOdd", 
// i.e. if it is formed by a (possibly empty) sequence of even numbers 
//followed by a (possibly empty) sequence of odd numbers
//In that case we want to return the integer p in [0..v.Length] such that 
//all elements in v[0..p) are even and those in v[p..v.Length) are odd

//For example: 
//array v = [2, 1, 7, 5] is evenOdd, and we return p=1
//array v = [6, 2, 20]  is evenOdd, and we return p=3 
//array v = [2, 3, 8] is not evenOdd
//array v = [5, 6] is not evenOdd


predicate positive(s:seq<int>)
{forall k::0<=k<|s| ==> s[k]>=0}

//1. Define the following predicates 

predicate even(v:array<int>,i:int,j:int)
requires 0 <= i <= j <= v.Length
reads v
//All the elements in v[i..j) are even
{
    forall x | i <= x < j :: v[x] % 2 == 0
}

predicate odd(v:array<int>,i:int,j:int)
requires 0 <= i <= j <= v.Length
reads v
//All the elements in v[i..j) are odd
{
    forall x | i <= x < j :: v[x] % 2 == 1
}

//2. Write the postcondition of method evenOdd, which returns 
// - boolean isEvenOdd, which is true if and only if array v is evenOdd as explained above
// - if isEvenOdd is true, then p is an integer in [0..v.Length] such that 
//   all elements in v[0..p) are even and those in v[p..v.Length) are odd
method evenOdd(v:array<int>) returns (isEvenOdd:bool,p:int)
requires positive(v[0..v.Length])
ensures isEvenOdd <==> exists i :: 0 <= i <= v.Length && even(v,0,i) && odd(v,i,v.Length) && i == p
//3. [3 pt] Implement and verify method evenOdd
{
    var i := 0;
    p := 0;
    isEvenOdd := true;

    while (i < v.Length && isEvenOdd)
    decreases isEvenOdd, v.Length - i
    invariant 0 <= p <= i <= v.Length
    invariant even(v,0,p)
    invariant isEvenOdd ==> odd(v,p,i)
    invariant isEvenOdd <==> even(v,0,p) && odd(v,p,i)
    {
        if (v[i] % 2 == 0) {
            if (p == i) {p := p+1;}
            else {isEvenOdd := false;}
        }
        i := i + 1;
    }
}
