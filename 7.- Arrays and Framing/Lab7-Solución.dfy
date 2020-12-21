method pruebas()
{
var a: array<int>;

a := new int[6](i => 0);
assert a[3] == 0;
assert forall i :: 0 <= i < a.Length ==> a[i] == 0;

a := new int[6](_ => 0);

a := new int[6](i => i*2);
assert a[3] == 6;

a := new int[6](i requires i>=0 =>  if i%2 == 0 then 5 else 7);

a := new int[6](i  requires i >=0 => f(i));
assert a[2] == 1;
assert a[3] == 1;
assert a[1] == 0; 

a := new int[6](g);
assert a[2] == 2;
assert a[3] == 2;
assert a[1] == 1;
}

function method f(i:int):int
requires i >= 0
{
if i%2 == 0 then i/2 else (i-1)/2
}

function method g(i:int):int
requires i >= 0
{
if i%2 == 0 then (i/2)+1 else (i+1)/2
}

//crear un array a partir de una secuqncia
method arrayFromSeq<T(==)>(s:seq<T>) returns (a:array<T>)
ensures a[..] == s
ensures fresh(a)
{
a := new T[|s|](i requires 0 <= i < |s| => s[i]);
}

//mínimo elemento de un array
method Min(a:array<int>) returns (m:int)
requires a.Length > 0
ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
ensures m in a[..]
{
//assert forall i :: 0 <= i < 1 ==> a[0] <= a[i];
//assert a[0] in a[..1];
m := a[0];
//assert forall i :: 0 <= i < 1 ==> m <= a[i];
//assert m in a[..1];
var k := 1;
while k < a.Length
         invariant 0 <= k <= a.Length
         invariant forall i :: 0 <= i < k ==> m <= a[i]
         invariant m in a[..k]
		 {
		 //assert (a[k] < m && forall i :: 0 <= i < k+1 ==> a[k] <= a[i]) ||
		 //       (!(a[k] < m) && forall i :: 0 <= i < k+1 ==> m <= a[i]);
		 if a[k] < m { m := a[k];}
		 //assert forall i :: 0 <= i < k+1 ==> m <= a[i];
		 k := k+1;
		 //assert forall i :: 0 <= i < k ==> m <= a[i];
		 }
}

//incrementar todos los elementos de un array
method add (v1:array<int>, c:int) returns (v2:array<int>)
ensures v2 == v1
ensures forall i :: 0 <= i < v1.Length ==> v1[i] == old(v1[i])+c
modifies v1

//suma de componentes de un array
function sum (s:seq<int>):int
{
if s == [] then 0 else s[0] + sum(s[1..])
}

lemma sum_Lemma(s:seq<int>, k:nat)
requires 0 <= k < |s|
ensures sum(s[..k]) + s[k] == sum(s[..k+1])
//EJERCICIO PARA CASA: PROBAR POR INDUCCIÓN

method addInFirst(a:array<int>) 
modifies a
requires a.Length > 0
ensures a[0] == sum(old(a[..]))
ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i])


// The Dutch Flag Problem: A classification problem
datatype Color = Red | White | Blue // horizontal tricolour (red is up)

predicate bellow(c:Color, d:Color)
{
c == Red  || c == d || d == Blue
}

predicate perm<T>(s:seq<T>,r:seq<T>)
{
multiset(s) == multiset(r)
}

method DutchFlag(a:array<Color>)
	modifies a
	ensures forall i, j :: 0 <= i < j < a.Length ==> bellow(a[i],a[j])
	ensures perm(a[..],old(a[..]))


// EJERCICIO PARA CASA: (Aplicación de la bandera holandesa) 
// Re-colocar (clasificar) los elementos de un array, poniendo los pares primero (a la izda)
// y los impares despues

predicate ord(x:nat,y:nat)
{
x%2==0 || (x%2==0 <==> y%2==0)|| y%2!=0
}

method partitionEvenOdd(a:array<nat>)
modifies a
ensures perm(a[..],old(a[..]))
ensures forall i,j :: 0 <= i < j < a.Length ==> ord(a[i],a[j])

/*
BUBBLE SORT 

First
( 5 1 4 2 3 ) ===> ( 1 5 4 2 3 ) Swap since 5 > 1.

Second
( 1 5 4 2 3 ) ===> ( 1 4 5 2 3 ) Swap since 5 > 4

Third
( 1 4 5 2 3 ) ===> ( 1 4 2 5 3 ) ===> ( 1 2 4 5 3 ) 
              Swap since 5 > 2   Swap since 4 > 2

Fourth
( 1 2 4 5 3 ) ===> ( 1 2 4 3 5 ) ===> ( 1 2 3 4 5 )
              Swap since 5 > 2   Swap since 4 > 3

*/

predicate sortedBetween(a:array<int>,lo:int,hi:int)
requires 0 <= lo <= hi <= a.Length
reads a
{
forall i, j :: lo <= i < j < hi ==> a[i] <= a[j] 
}

predicate sortedArray(a:array<int>)
reads a
{
sortedBetween(a,0,a.Length) 
}

//predicate perm<T>(s:seq<T>,r:seq<T>) //arriba

method bubbleSort (a:array<int>)
requires a.Length > 0
ensures sortedArray(a)
ensures perm(a[..],old(a[..]))
modifies a


// BINARY SEARCH: ITERATIVE AND RECURSIVE

method BinarySearch(a:array<int>, key:int) returns (index:int)
requires sortedArray(a)
ensures 0 <= index <= a.Length
ensures index < a.Length ==> a[index] == key
ensures index == a.Length ==> key !in a[..]
{
var start, end := 0, a.Length;
while start < end
   invariant 0 <= start <= end <= a.Length
   invariant key !in (a[..start] + a[end..])
   {
   var mid := (start+end)/2;
   if key > a[mid] { start := mid+1;}
   else if key < a[mid] { end := mid; }
   else { return mid; }
   }
return a.Length;
}

/*
La iteración de arriba es equivalente a: 
index := BinarySearchRec(a,key,0,a.Length);
si el method BinarySearchRec 
*/

method BinarySearchRec(a:array<int>, key:int, start:int, end:int) returns (index:int)
requires sortedArray(a)
ensures 0 <= start <= index <= end <= a.Length
ensures index < a.Length ==> a[index] == key
ensures index == a.Length ==> key !in a[start..end]
// EJERCICIO PARA CASA: Implementar este método 