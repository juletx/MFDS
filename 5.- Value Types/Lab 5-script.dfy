predicate sorted(s: seq<int>)
{
forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate palindrome<T> (s:seq<T>)
{
// forall i :: 0 rel<= i rel<=(|s|-1)/2 ==> s[i]==s[|s|-i-1]
forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1-i]
                        //easier to understand and to validate
}

// Exercise: Derivar formalmente un calculo incremental de j*j*j

method Cubes (n:int) returns (s:seq<int>)
	requires n >= 0
	ensures |s| == n
	ensures forall i:int :: 0 <= i < n ==> s[i] == i*i*i
{
var j := 0;
s := [];
var c := 0;
while j < n
	invariant  0 <= j ==|s| <= n
	invariant forall i:int :: 0 <= i < j ==> s[i] == i*i*i
	invariant c == j*j*j
	{
	s := s+[c]; 
	c := (j+1)*(j+1)*(j+1);
	assert c == (j+1)*(j+1)*(j+1);
	j := j+1;
	assert c == j*j*j;
	}
}

// MAXIMUM OF A SEQUENCE

method maxSeq(v: seq<int>) returns (max:int)
requires |v| >= 1
//ensures 
{
max := v[0];
var v' := v[1..];
while |v'| >= 1
	{
	if v'[0] > max { max := v'[0]; }
	v' := v'[1..];
	}
}

// SUM OF A SEQUENCE OF INTEGERS

function sum(v: seq<int>): int 
{
if v == [] then 0 else v[0] + sum(v[1..])
}

method vector_Sum(v:seq<int>) returns (x:int)
//ensures x == sum(v) 
{
var n := 0 ;
x := 0;
while n != |v|
   invariant 0 <= n <= |v|
   {
   x, n := x + v[n], n + 1;
   }
}

// Structural Induction on Sequences
lemma left_sum_Lemma(r:seq<int>, k:int)


// REVERSE OF A SEQUENCE

function reverse<T> (s:seq<T>):seq<T> 
{
[]
}

function seq2set<T> (s:seq<T>): set<T>
{
{}
}

lemma seq2setRev_Lemma<T> (s:seq<T>)
	ensures seq2set(reverse(s)) == seq2set(s)

lemma concat_seq2set_Lemma<T>(s1:seq<T>,s2:seq<T>)
	ensures seq2set(s1+s2) == seq2set(s1) + seq2set(s2)


// REVERSE IS ITS OWN INVERSE

lemma Rev_Lemma<T(==)>(s:seq<T>)
//  ensures forall i :: 0 <= i < |s| ==> s[i] == reverse(s)[|s|-1-i]


lemma ItsOwnInverse_Lemma<T> (s:seq<T>)
	ensures s == reverse(reverse(s))


// SCALAR PRODUCT OF TWO VECTORS OF INTEGER

function scalar_product (v1:seq<int>, v2:seq<int>):int


lemma scalar_product_Lemma (v1:seq<int>, v2:seq<int>)
requires |v1| == |v2| > 0
ensures scalar_product(v1,v2) == scalar_product(v1[..|v1|-1],v2[..|v2|-1]) + v1[|v1|-1] * v2[|v2|-1]


// MULTISETS

method multiplicity_examples<T> ()
{
var m := multiset{2,4,6,2,1,3,1,7,1,5,4,7,8,1,6};
assert m[7] == 2;
assert m[1] == 4;

assert forall m1: multiset<T>, m2 :: m1 == m2 <==> forall z:T :: m1[z] == m2[z];
}

// REVERSE HAS THE SAME MULTISET 

lemma seqMultiset_Lemma<T> (s:seq<T>)
   ensures multiset(reverse(s)) == multiset(s)


// SEQUENCES WITH EQUAL MULTISETS HAVE EQUAL SUMS

lemma sumElems_Lemma(s:seq<int>, r:seq<int>)   
requires multiset(s) == multiset(r)
ensures sum(s) == sum(r)



//MAPS

method map_Examples() {
var m1: map<int,int> := map[] ;  
var m2 := map[20 := true, 3 := false, 20 := false]; 
var m2' := m2[20 := true];
var m2'' := m2'[10 := false];
var a:int,b:int,c:int,d: int;
var m3 := map[a+b := c+d];

// comprenhesions
var m4 := map x : int | 0 <= x <= 10 :: x * x;
ghost var im1 := imap x : int :: x * x;
ghost var im2 := imap x : int | x%2 == 0 :: x * x;
}