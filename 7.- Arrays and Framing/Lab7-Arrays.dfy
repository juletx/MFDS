method pruebas()
{
	var a: array<int>;

	a := new int[6](i => 0);
	assert a[3] == 0;
	assert forall i :: 0 <= i < a.Length ==> a[i] == 0;

	a := new int[6](_ => 0);

	a := new int[6](i => i*2);
	assert a[3] == 6;

	a := new int[6](i requires i >= 0 => if i%2 == 0 then 5 else 7);

	a := new int[6](i requires i >= 0 => f(i));
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

//crear un array a partir de una secuencia
method arrayFromSeq<T>(s:seq<T>) returns (a:array<T>)
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
	// assert a[0] in a[..1] && forall i :: 0 <= i < 1 ==> a[0] <= a[i];
	m := a[0];
	// assert m in a[..1] && forall i :: 0 <= i < 1 ==> m <= a[i];
	var k := 1;
	// assert m in a[..1] && forall i :: 0 <= i < k ==> m <= a[i];
	while k < a.Length
		invariant 1 <= k <= a.Length
		invariant forall i :: 0 <= i < k ==> m <= a[i]
		invariant m in a[..k]
	{
		// assert (a[k] < m && forall i :: 0 <= i < k+1 ==> a[k] <= a[i]) ||
		//	(a[k] >= m && forall i :: 0 <= i < k+1 ==> m <= a[i]);
		if a[k] < m {
			m := a[k];
		}
		// assert forall i :: 0 <= i < k+1 ==> m <= a[i];
		k := k+1;
		// assert forall i :: 0 <= i < k ==> m <= a[i];
	}
}

//incrementar todos los elementos de un array
method add(v1:array<int>, c:int) returns (v2:array<int>)
	ensures v2 == v1
	ensures forall i :: 0 <= i < v1.Length ==> v1[i] == old(v1[i])+c
	modifies v1
{
	var k := 0;
	while k < v1.Length
		invariant 0 <= k <= v1.Length
		invariant forall i :: 0 <= i < k ==> v1[i] == old(v1[i])+c
		invariant forall i :: k <= i < v1.Length ==> v1[i] == old(v1[i])
	{
		// assert (forall i :: 0 <= i < k ==> v1[i] == old(v1[i])+c) && v1[k] + c == old(v1[k])+c;
		v1[k] := v1[k] + c;
		// assert forall i :: 0 <= i < k+1 ==> v1[i] == old(v1[i])+c;
		// assert (forall i :: 0 <= i < k ==> v1[i] == old(v1[i])+c) && v1[k] == old(v1[k])+c;
		k := k + 1;
		// assert forall i :: 0 <= i < k ==> v1[i] == old(v1[i])+c;
	}
	return v1;
}

//suma de componentes de un array
function sum(s:seq<int>):int
{
	if s == [] then 0 else s[0] + sum(s[1..])
}

//EJERCICIO PARA CASA: PROBAR POR INDUCCIÓN
lemma sum_Lemma(s:seq<int>, k:nat)
	requires 0 <= k < |s|
	ensures sum(s[..k]) + s[k] == sum(s[..k+1])
{
	if s != [] && k != 0 {
		calc {
			sum(s[..k]) + s[k];
			s[..k][0] + sum(s[..k][1..]) + s[k];
			{
				assert s[..k][1..] == s[1..][..k-1];
				// assert s[k] == s[1..][k-1];
			}
			s[0] + sum(s[1..][..k-1]) + s[1..][k-1];
			{
				sum_Lemma(s[1..], k-1);
				assert sum(s[1..][..k-1]) + s[1..][k-1] == sum(s[1..][..k]);
			}
			s[0] + sum(s[1..][..k]);
			{
				assert s[1..][..k] == s[1..k+1];
			}
			s[0] + sum(s[1..k+1]);
			sum(s[..k+1]);
		}
	}
}

method addInFirst(a:array<int>) 
	modifies a
	requires a.Length > 0
	ensures a[0] == sum(old(a[..]))
	ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i])
{
	var k := 1;
	while k < a.Length
		invariant 1 <= k <= a.Length
		invariant a[0] == sum(old(a[..k]))
		invariant forall i :: 1 <= i < a.Length ==> a[i] == old(a[i])
	{
		sum_Lemma(old(a[..]), k);
		// assert old(a[..])[..k] == old(a[..k]);
		// assert a[0] + a[k] == sum(old(a[..k])) + old(a[k]) == sum(old(a[..k+1]));
		a[0] := a[0] + a[k];
		// assert a[0] == sum(old(a[..k+1]));
		k := k + 1;
		// assert a[0] == sum(old(a[..k]));
	}
	// assert a[0] == sum(old(a[..a.Length]));
	assert old(a[..a.Length]) == old(a[..]); // lemma local
	// assert a[0] == sum(old(a[..]);
}


// The Dutch Flag Problem: A classification problem
datatype Color = Red | White | Blue // horizontal tricolour (red is up)

predicate bellow(c:Color, d:Color)
{
	c == Red || c == d || d == Blue
}

predicate perm<T>(s:seq<T>,r:seq<T>)
{
	multiset(s) == multiset(r)
}

method DutchFlag(a:array<Color>)
	modifies a
	ensures forall i, j :: 0 <= i < j < a.Length ==> bellow(a[i],a[j])
	ensures perm(a[..], old(a[..]))
{
	var r, w, b := 0, 0, a.Length;
	while w < b 
		invariant 0 <= r <= w <= b <= a.Length
		invariant forall i :: 0 <= i < r ==> a[i] == Red
		invariant forall i :: r <= i < w ==> a[i] == White
		invariant forall i :: b <= i < a.Length ==> a[i] == Blue
		invariant perm(a[..], old(a[..]))
	{
		match a[w] {
			case Red => {
				a[r], a[w] := a[w], a[r];
				r, w := r + 1, w + 1;
			}
			case White => {
				w := w + 1;
			}
			case Blue => {
				a[w], a[b-1] := a[b-1], a[w];
				b := b - 1;
			}
		}
	}
}

// EJERCICIO PARA CASA: (Aplicación de la bandera holandesa) 
// Re-colocar (clasificar) los elementos de un array, poniendo los pares primero (a la izda)
// y los impares despues

predicate ord(x:nat,y:nat)
{
	x%2==0 || (x%2==0 <==> y%2==0) || y%2!=0
}

method partitionEvenOdd(a:array<nat>)
	modifies a
	ensures perm(a[..], old(a[..]))
	ensures forall i,j :: 0 <= i < j < a.Length ==> ord(a[i],a[j])
{
	var e, o := 0, a.Length;
	while e < o
		invariant 0 <= e <= o <= a.Length
		invariant forall i :: 0 <= i < e ==> a[i]%2==0
		invariant forall i :: o <= i < a.Length ==> a[i]%2!=0
		invariant perm(a[..], old(a[..]))
	{
		if a[e] %2 == 0 {
			e := e + 1;
		}
		else {
			a[e], a[o-1] := a[o-1], a[e];
			o := o - 1;
		}
	}
}

/*
BUBBLE SORT 

First i = 1
( 5 1 4 2 3 ) ===> ( 1 5 4 2 3 ) Swap since 5 > 1.

Second i = 2
( 1 5 4 2 3 ) ===> ( 1 4 5 2 3 ) Swap since 5 > 4

Third i = 3
( 1 4 5 2 3 ) ===> ( 1 4 2 5 3 ) ===> ( 1 2 4 5 3 ) 
              Swap since 5 > 2   Swap since 4 > 2

Fourth i = 4
( 1 2 4 5 3 ) ===> ( 1 2 4 3 5 ) ===> ( 1 2 3 4 5 )
              Swap since 5 > 3   Swap since 4 > 3
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

method bubbleSort(a: array<int>)
	requires a.Length > 0
	ensures sortedArray(a)
	ensures perm(a[..],old(a[..]))
	modifies a
{
	var i := 1;
	while i < a.Length
		invariant 1 <= i <= a.Length
		invariant sortedBetween(a, 0, i)
		invariant perm(a[..],old(a[..]))
	{
		// metodo auxiliar que haga swap en cada uno
		pushLeft(a, i);
		// assert 1 <= i+1 <= a.Length && sortedBetween(a, 0, i+1) && perm(a[..],old(a[..]));
		i := i + 1;
		// assert 1 <= i <= a.Length && sortedBetween(a, 0, i) && perm(a[..],old(a[..]));
	}
}

method pushLeft(a: array<int>, i: nat)
	requires 1 <= i < a.Length
	requires sortedBetween(a, 0, i)
	ensures sortedBetween(a, 0, i+1)
	ensures perm(a[..],old(a[..]))
	modifies a
{
	var j := i;
	while j > 0 && a[j-1] > a[j]
		invariant 0 <= j <= i
		invariant sortedBetween(a, 0, j)
		invariant sortedBetween(a, j, i+1)
		// invariant forall k, k' :: 0 <= k <= j && j < k' <= i ==> a[k] <= a[k']
		invariant 0 < j < i ==> a[j-1] <= a[j+1]
		invariant perm(a[..],old(a[..]))
	{
		a[j-1], a[j] := a[j], a[j-1];
		// assert a[j-1] <= a[j];
		// assert forall l, k :: j-1 <= l < k < i+1 ==> a[l] <= a[k];
		// assert sortedBetween(a, j-1, i+1);
		j := j-1;
		// assert sortedBetween(a, j, i+1);
	}
}

method printArray<T>(a: array<T>)
{
	var i := 0;
	while i < a.Length {
		print(a[i]);
		i := i+1;
	}
}

// Generar ejecutable
method Main()
	decreases *
{
	var s := [8,7,4,3,2,1,9,3,6,7,2,1,5];
	var a := arrayFromSeq(s);
	printArray(a);
	print "\n";
	bubbleSort(a);
	printArray(a);
	while true decreases * {}
}

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

// EJERCICIO: Implementar este método 
method BinarySearchRec(a:array<int>, key:int, start:int, end:int) returns (index:int)
	requires sortedArray(a)
	requires 0 <= start <= end <= a.Length
	ensures 0 <= index <= a.Length
	ensures index < a.Length ==> a[index] == key
	ensures index == a.Length ==> key !in a[start..end]
	decreases end-start
{
	if start < end {
		var mid := (start+end)/2;
		if key > a[mid] {
			index := BinarySearchRec(a, key, mid+1, end);
			assert mid+1 <= index <= end &&
				index < a.Length ==> a[index] == key &&
				index == a.Length ==> key !in a[mid+1..end];
		}
		else if key < a[mid] {
			index := BinarySearchRec(a, key, start, mid);
			assert start <= index <= mid &&
				index < a.Length ==> a[index] == key &&
				index == a.Length ==> key !in a[start..mid];
		}
		else {
			index := mid;
		}
	}
	else {
		index := a.Length;
	}
}

// Ejemplo
method reverseArray<T>(a: array<T>)
	modifies a
	ensures forall k :: 0 <= k < a.Length/2 ==> 
		a[k] == old(a[a.Length-k-1]) && a[a.Length-k-1] == old(a[k])
{
	var i := 0;
	while i < a.Length/2
		invariant 0 <= i <= a.Length/2
		invariant forall k :: 0 <= k < i ==> 
			a[k] == old(a[a.Length-k-1]) && a[a.Length-k-1] == old(a[k])
		invariant a[i..a.Length-i] == old(a[i..a.Length-i])
	{
		assert a[a.Length-i-1] == old(a[a.Length-i-1]) && a[i] == old(a[i]);
		a[i], a[a.Length-i-1] := a[a.Length-i-1], a[i];
		assert a[i] == old(a[a.Length-i-1]) && a[a.Length-i-1] == old(a[i]) &&
			forall k :: 0 <= k < i ==> 
				a[k] == old(a[a.Length-k-1]) && a[a.Length-k-1] == old(a[k]);
		i := i+1;
		assert forall k :: 0 <= k < i ==> 
			a[k] == old(a[a.Length-k-1]) && a[a.Length-k-1] == old(a[k]);
	}
}
