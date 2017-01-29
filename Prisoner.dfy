// The Prisoner of Benda
//
// The array L represents a permutation of the minds of the crew, where index i
// is body i and contains mind L[i]. Without loss of generality (since an 
// invertable data transformer exists for any list), assume that minds and
// bodies are numbered 0 through L.Length. So originally body i had mind i.
//
// Prove that the following algorithm correctly switches everyone back,
// including the two extra bodies.
//
// The algorithm is outlined at:
//
//   https://en.wikipedia.org/wiki/The_Prisoner_of_Benda

/* README 
We aren't allowed to upload a readme to markus, so I'm including my notes
here in this file.

Please have some patience when running this file. It takes a while to
finish.

For this code, the pre and post conditions for cycle pass and I am
failing 2/3 loop invariants.
The invariants that fail are
(1) invariant x !in L[..];
(2) invariant y !in L[..];
(3) invariant forall k:: i < k < L.Length && k !in (set z | i < z < L.Length && L[z] != z) ==> L[k] == k; // Not in s 

The first two are failing due to some quirk of Dafny where it thinks
that i can be equal to x(v0) and y(v1). This is due to the boundary
where i == L.Length.  
Adding a the requirement requires v0 > L.Length && v1 > L.Length allows
these invariants to pass. This is pretty reasonable given that nothing
is lost by changing the starting values of v0, v1 as long as they
are not in L.

The other invariant (3) is needed for my cycle method to work.
Unfortunately I'm not quite sure how to prove it and it's probably
wrong.
*/
method benda(L:array<int>, v0:int, v1:int) returns (x:int, y:int)
  // Do no change these.
  requires L != null;
  requires forall i::0 <= i < L.Length ==> 0 <= L[i] < L.Length; // in range
  requires forall i,j::0 <= i < j < L.Length ==> L[i] != L[j]; // distinct
  requires v0 !in L[..] && v1 !in L[..] && v0 != v1;
  //requires v0 > L.Length && v1 > L.Length;
  modifies L;
  ensures forall j::0 <= j < L.Length ==> L[j] == j; // everyone is switched back
  ensures x == v0 && y == v1; // extras are also switched back
{
  var i;
  i,x,y := 0,v0,v1;
  //assert L.Length > 0 ==> 0 in L[..];
  while (i < L.Length)
    invariant 0 <= i <= L.Length;
    invariant x != y;
    invariant {x, y} == {v0, v1}; 
    invariant x !in L[..];
    invariant y !in L[..];
    invariant forall p,q::i <= p < q < L.Length ==> L[p] != L[q]; // distinct 
    invariant forall k::i <= k < L.Length ==> i <= L[k] < L.Length; // in range 
    invariant forall k:: 0 <= k < i ==> L[k] == k; // less than i sorted
    invariant forall k:: i < k < L.Length && k !in (set z | i < z < L.Length && L[z] != z) ==> L[k] == k; // Not in s 
    {     
    if (L[i] != i) { // if mind of i does not match with body i
      x,L[i] := L[i],x; // swap mind between i and x
      x := cycle(L,i,x,(set z | i < z < L.Length && L[z] != z));  
      
      y,L[x] := L[x],y; // swap minds between y and x
      x,L[x] := L[x],x; // put mind of x back to its body
      y,L[i] := L[i],y; // swap minds between y and i 
    }
    i := i+1;
    assert forall k:: 0 < k < L.Length && k !in (set z | i < z < L.Length && L[z] != z) ==> L[k] == k; // Not in s 
  }

  // If the two extras are switched at the end, switch back.
  if (x != v0) {
    x,y := y,x;
  } 
} 

// Put a cycle permutation back to identity permutation.
// https://en.wikipedia.org/wiki/Cyclic_permutation




// L is the array of people swapped, i is current physical body), a is the mind in the extra body
// s is the set of people not in the right body except i and the extras
method cycle(L:array<int>, i:int, a:int, s:set<int>) returns (x:int)
  requires L != null;
  requires 0 <= i < L.Length;
  requires 0 <= a < L.Length;
  requires a !in L[..]; // invar x !in L[..]
  
  requires s == (set z | i < z < L.Length && L[z] != z); // Note L[i] !in s
  requires a != i;
  requires forall k::0 <= k < L.Length && k != i ==> 0 <= L[k] < L.Length; // in range
  requires forall i,j::0 <= i < j < L.Length ==> L[i] != L[j]; // distinct
  requires forall k:: 0 <= k < i ==> L[k] == k; // less than i sorted
  requires forall k:: i < k < L.Length && k !in s ==> L[k] == k; // Not in s => sorted
  modifies L;
  decreases s;
  
  ensures i <= x < L.Length; 
  ensures L[x] == i; 
  // x is the index of where i is
  ensures forall i,j::0 <= i < j < L.Length ==> L[i] != L[j]; // Distinct 
  ensures forall k::0 <= k < L.Length && k != i ==> 0 <= L[k] < L.Length; // in range
  ensures forall k:: i < k < L.Length && k !in s ==> L[k] == k; // Not in s => sorted
  ensures forall k::0 <= k < i ==> L[k] == k;
  ensures L[a] != i ==> L[a] == a;
  ensures L[a] == i ==> L[x] == i;
  ensures x !in L[..];
  ensures x in old(L[..]) || x == a;
  ensures i == old(i);
  ensures L[i] == old(L[i]);
{
  x := a;
  print "a ", a, "\n";
  if (L[x] != i) { // mind and body do not match.
    x,L[x] := L[x],x;
    print "L : ", L[..], "\n";
    x := cycle(L,i,x,s-{a});
  } 
}

method Main()
{
  var a:= new int[5];

  //a[0],a[1],a[2],a[3],a[4]:= 3,2,1,4,0;
  a[0],a[1],a[2],a[3],a[4]:= 5,2,1,4,0;
  var ret:= cycle(a, 0, 3, (set z | 0 < z < a.Length && a[z] != z));
  print "Ret ", ret, "\n";
  print "a :", a[..], "\n";
  //var x,y:= benda(a, a.Length, a.Length + 1);
  //print a[..]," ",x," ",y,"\n";
}