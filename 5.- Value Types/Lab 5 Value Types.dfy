predicate sorted(s: seq<int>)
{
	forall i,j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate palindrome<T> (s:seq<T>)
{
	// forall i :: 0 <= i <=(|s|-1)/2 ==> s[i]==s[|s|-i-1]
	// easier to understand and to validate
	forall i :: 0 <= i < |s| ==> s[i] == s[|s|-1-i]
}                  

method pruebas1() {
	var s := [2,1,3,5,7,1];
	// assert s == [2] + [1,3,5,7,1];
	// assert s == [2,1] + [3,5,7,1];
	// assert s[0] == 2 && s[1] == 1;
	assert s[4] == 7 && s[5] == 1;
	assert !sorted(s);
	s := [1,2,3,2,1];
	// habría que poner predicate method
	assert palindrome(s);
	// var b := palindrome(s);
	// assert b;
}


// Exercise: Derivar formalmente un calculo incremental de j*j*j

method Cubes (n:int) returns (s:seq<int>)
	requires n >= 0
	ensures |s| == n
	ensures forall i:int :: 0 <= i < n ==> s[i] == i*i*i
{
	var j := 0;
	var k := 1;
	var m := 6;
	s := [];
	var c := 0;
	while j < n
		invariant 0 <= j ==|s| <= n
		invariant forall i:int :: 0 <= i < j ==> s[i] == i*i*i
		invariant c == j*j*j
		invariant k == 3*j*j + 3*j + 1
		invariant m == 6*j + 6
	{
		s := s+[c]; 
		// assert c == j*j*j;
		// assert k == 3*j*j + 3*j + 1;
		// assert m == 6*j + 6;
		c := c + k;
		k := k + m;
		m := m + 6;
		// assert c == (j+1)*(j+1)*(j+1) ==  j*j*j + 3*j*j + 3*j + 1;
		// assert k == 3*(j+1)*(j+1) + 3*(j+1) + 1 == 3*j*j + 9*j + 7;
		// assert m == 6*(j+1) + 6 == 6*j + 12;
		j := j+1;
		// assert c == j*j*j;
		// assert k == 3*j*j + 3*j + 1;
		// assert m == 6*j + 6;
	}
}

// MAXIMUM OF A SEQUENCE

method maxSeq(v: seq<int>) returns (max:int)
	requires |v| >= 1
	ensures forall i :: 0 <= i < |v| ==> max >= v[i]
	ensures max in v
{
	// assert forall i :: 0 <= i < |[v[0]]| ==> v[0] >= [v[0]][i];
	ghost var t := [v[0]];
	// assert forall i :: 0 <= i < |t| ==> v[0] >= t[i];
	max := v[0];
	var v' := v[1..];
	// assert forall i :: 0 <= i < |t| ==> max >= t[i];
	while |v'| >= 1
		invariant forall i :: 0 <= i < |t| ==> max >= t[i]
		invariant v == t + v'
		invariant max in t
	{
		if v'[0] > max { 
			max := v'[0]; 
		}
		// assert v == t + v' == t + ([v'[0]] + v'[1..]) == (t+[v'[0]]) + v'[1..];
		v', t := v'[1..], t + [v'[0]];
		// assert v == t + v';
	}
}

// SUM OF A SEQUENCE OF INTEGERS

function sum(v: seq<int>): int 
{
	if v == [] then 0 else v[0] + sum(v[1..])
}

method vector_Sum(v:seq<int>) returns (x:int)
	ensures x == sum(v) 
{
	var n := 0 ;
	x := 0;
	while n != |v|
		invariant 0 <= n <= |v|
		invariant x == sum(v[..n])
		decreases |v| - n
	{
		sum_Lemma(v, n);
		// assert sum(v[..n]) + v[n] == sum(v[..n + 1]);
		x, n := x + v[n], n + 1;
		// assert x == sum(v[..n]);
	}
	// assert 0 <= n <= |v| && x == sum(v[..n]) && n == |v|;
	// assert 0 <= |v| <= |v| && x == sum(v[..|v|]) && |v| == |v|;
	// assert x == sum(v[..|v|]);
	assert v[..|v|] == v; // lemma local
}

// Ejercicio probar por inducción estructural en la secuencia r
lemma sum_Lemma(r:seq<int>, k:int)
	requires 0 <= k < |r|
	ensures sum(r[..k]) + r[k] == sum(r[..k+1]);
{
	if r == [] || k == 0 {
		assert sum([]) + r[k] == r[k] == sum(r[..k+1]);
	}
	else {
		// assert r != [] && k > 0;
		// assert r[..k] != [];
		calc {
			sum(r[..k]) + r[k];
			r[..k][0] + sum(r[..k][1..]) + r[k]; // Definición de suma
			{
				// assert r[..k][1..] == r[1..k];
				assert r[1..k] == r[1..][..k-1]; // lemma local
			}
			r[0] + sum(r[1..][..k-1]) + r[1..][k-1];
			{
				sum_Lemma(r[1..], k-1);
				// assert sum(r[1..][..k-1]) + r[1..][k-1] == sum(r[1..][..k]); // HI
			}
			r[0] + sum(r[1..][..k]);
			{
				assert r[1..][..k] == r[1..k+1]; // lemma local
			}
			r[0] + sum(r[1..k+1]); // Definición de suma
			sum(r[..k + 1]);
		}
	}
}


// REVERSE OF A SEQUENCE

function reverse<T> (s:seq<T>):seq<T>
	ensures |reverse(s)| == |s|
{
	// if s == [] then [] else [s[|s|-1]] + reverse(s[..|s|-1])
	if s == [] then [] else reverse(s[1..]) + [s[0]]
}

function seq2set<T> (s:seq<T>): set<T>
{
	// if s == [] then {} else {s[0]} + seq2set(s[1..])
	set x | x in s
}

method pruebas2()
{
	var r:= [3,5,1,5,5,4];
	assert reverse(r) == [4,5,5,1,5,3];
	assert seq2set(r) == {3,5,1,4,5} == {3,5,1,4};
	assert multiset(r)[5] == 3;
}

// Ejercicio probar por inducción
lemma seq2setRev_Lemma<T> (s:seq<T>)
	ensures seq2set(reverse(s)) == seq2set(s)
{
	if s != [] {
		calc {
			seq2set(s);
			seq2set([s[0]] + s[1..]);
			seq2set([s[0]]) + seq2set(s[1..]);
			{
				seq2setRev_Lemma(s[1..]);
				assert seq2set(reverse(s[1..])) == seq2set(s[1..]);
			}
			seq2set([s[0]]) + seq2set(reverse(s[1..]));
			seq2set([s[0]] + reverse(s[1..]));
			seq2set(reverse(s[1..]) + [s[0]]);
			seq2set(reverse(s));
		}
	}
}

// Ejercicio probar por inducción
lemma seq2setRev_Lemma2<T> (s:seq<T>)
	ensures seq2set(reverse(s)) == seq2set(s)
{
	if s != [] {
		calc {
			seq2set(reverse(s));
			seq2set(reverse(s[1..]) + [s[0]]);
			seq2set(reverse(s[1..])) + seq2set([s[0]]);
			{
				seq2setRev_Lemma2(s[1..]);
				assert seq2set(reverse(s[1..])) == seq2set(s[1..]); // IH
			}
			seq2set(s[1..]) + seq2set([s[0]]);
			seq2set(s);
		}
	}
	/*if s != [] {
        assert seq2set(reverse(s[1..]) + [s[0]]) 
			== seq2set(reverse(s[1..])) + seq2set([s[0]]);
    }*/

}

// Ejercicio probar por inducción en s1
lemma {:induction false} concat_seq2set_Lemma<T>(s1:seq<T>,s2:seq<T>)
	ensures seq2set(s1+s2) == seq2set(s1) + seq2set(s2)
{
	if s1 == [] {
		assert seq2set([]+s2) == seq2set([]) + seq2set(s2);
	}
	else {
		calc {
			seq2set(s1) + seq2set(s2);
			seq2set([s1[0]]) + seq2set(s1[1..]) + seq2set(s2);
			{
				concat_seq2set_Lemma(s1[1..], s2);
				assert seq2set(s1[1..]+s2) == seq2set(s1[1..]) + seq2set(s2);
			}
			seq2set([s1[0]]) + seq2set(s1[1..]+s2);
			seq2set([s1[0]] + s1[1..] + s2);
			seq2set(s1+s2);
		}
	}
}


// REVERSE IS ITS OWN INVERSE

// Ejercicio probar por induccion en longitud de s
lemma Rev_Lemma<T(==)>(s:seq<T>)
	ensures forall i :: 0 <= i < |s| ==> s[i] == reverse(s)[|s|-1-i]
{
	if |s| > 0 {
		var r := s[1..];
		Rev_Lemma(r);
		// assert forall i :: 0 <= i < |r| ==> r[i] == reverse(r)[|r|-1-i]; // HI
		assert s[0] == reverse(s)[|s|-1];
	}
}


// Ejercicio probar por contradiccion
lemma ItsOwnInverse_Lemma<T> (s:seq<T>)
	ensures s == reverse(reverse(s))
{
	if s != reverse(reverse(s)) {
		// assert forall r:seq<T> :: |reverse(r)| == |r|; // lemma local
		// assert exists i :: 0 <= i < |s| && s[i] != reverse(reverse(s))[i];
		var k :| 0 <= k < |s| && s[k] != reverse(reverse(s))[k];
		calc ==> {
			s[k] != reverse(reverse(s))[k];
			{
				Rev_Lemma(s);
				// assert s[k] == reverse(s)[|s|-1-k];
			}
			reverse(s)[|s|-1-k] != reverse(reverse(s))[k];
			{
				Rev_Lemma(reverse(s));
				// assert reverse(s)[|s|-1-k] == reverse(reverse(s))[|s|-1-(|s|-1-k)] == reverse(reverse(s))[k];
			}
			reverse(reverse(s))[k] != reverse(reverse(s))[k];
			false;
		}
	}
}

// Ejercicio demostrar por inducción en s
/*lemma ItsOwnInverse_Lemma2<T> (s:seq<T>)
	ensures s == reverse(reverse(s))
{
	if s != [] {
		calc {
			s;
			[s[0]] + s[1..];
			{
				ItsOwnInverse_Lemma2(s[1..]);
				assert s[1..] == reverse(reverse(s[1..]));
			}
			[s[0]] + reverse(reverse(s[1..]));
			[s[0]] + reverse(reverse(s[1..]));
			reverse([s[0]]) + reverse(reverse(s[1..]));
			{
				assert reverse(s) == reverse(s[1..]) + [s[0]];
			}
			reverse([s[0]] + reverse(s[1..]));
			{
				assume reverse(reverse([s[0]] + s[1..])) == reverse(reverse(s[1..])) + reverse([s[0]]);
			}
			//reverse(reverse(s[1..]) + [s[0]]);
			// assert reverse(s) == reverse(s[1..]) + [s[0]]
			reverse(reverse(s));
		}
	}
}*/


// SCALAR PRODUCT OF TWO VECTORS OF INTEGER

function scalar_product (v1:seq<int>, v2:seq<int>):int
	requires |v1| == |v2|
{
	if |v1| == 0 then 0 else v1[0]*v2[0] + scalar_product(v1[1..], v2[1..])
}


lemma scalar_product_Lemma (v1:seq<int>, v2:seq<int>)
	requires |v1| == |v2| > 0
	ensures scalar_product(v1,v2) == scalar_product(v1[..|v1|-1],v2[..|v2|-1]) + v1[|v1|-1] * v2[|v2|-1]
{
	if |v1| > 1 {
		var v1r, v2r, t1, t2 := v1[1..], v2[1..], |v1[1..]|-1, |v2[1..]|-1;
		
		calc {
			scalar_product(v1,v2);
			v1[0]*v2[0] + scalar_product(v1r, v2r); // Definicion de scalar
			{
				scalar_product_Lemma(v1r, v2r);
				assert scalar_product(v1r,v2r) == scalar_product(v1r[..t1],v2r[..t2]) + v1r[t1] * v2r[t2]; // HI
			}
			v1[0]*v2[0] + scalar_product(v1r[..t1],v2r[..t2]) + v1r[t1] * v2r[t2];
			{
				assert scalar_product(v1[..|v1|-1],v2[..|v2|-1]) == 
					v1[0]*v2[0] + scalar_product(v1[..|v1|-1][1..], v2[..|v2|-1][1..]);
				// assume v1[0]*v2[0] + scalar_product(v1r[..t1],v2r[..t2]) == 
				// 	scalar_product(v1[..|v1|-1],v2[..|v2|-1]);
				//EJERCICIO: sustituir por 2 asserts de igualdad entre secuencias.
				assert v1r[..t1] == v1[..|v1|-1][1..];
				assert v2r[..t2] == v2[..|v2|-1][1..];
			}
			scalar_product(v1[..|v1|-1],v2[..|v2|-1]) + v1[|v1|-1] * v2[|v2|-1];
		}
	}
}


// MULTISETS

method multiplicity_examples<T> ()
{
	var ms := multiset{2,4,6,2,1,3,1,7,1,5,4,7,8,1,6};
	assert ms[7] == 2;
	assert ms[1] == 4;
	assert ms[9] == 0;

	assert forall m1: multiset<T>, m2 :: m1 == m2 <==> forall z:T :: m1[z] == m2[z];
}

// REVERSE HAS THE SAME MULTISET 

// Ejercicio parecido a set
lemma seqMultiset_Lemma<T> (s:seq<T>)
	ensures multiset(reverse(s)) == multiset(s)
{
	if s != [] {
		calc {
			multiset(reverse(s));
			multiset(reverse(s[1..]) + [s[0]]);
			multiset(reverse(s[1..])) + multiset([s[0]]);
			{
				seqMultiset_Lemma(s[1..]);
				assert multiset(reverse(s[1..])) == multiset(s[1..]); // IH
			}
			multiset(s[1..]) + multiset([s[0]]);
			multiset([s[0]] + s[1..]);
			{
				assert s == [s[0]] + s[1..];
			}
			multiset(s);
		}
	}
}


// SEQUENCES WITH EQUAL MULTISETS HAVE EQUAL SUMS

lemma Empty_Lemma<T>(s:seq<T>) 
	requires multiset(s) == multiset{}
	ensures s == []
{
	if s != [] {
		assert s[0] in multiset(s);
		assert multiset(s) != multiset{};
	}
}

// Por contraposicion y usando multiplicidad en multisets
lemma union_Lemma<T>(m: multiset<T>, m1: multiset<T>, m2:multiset<T>)
	requires m + m1 == m + m2
	ensures m1 == m2
{
	if m1 != m2 {
		assert exists z :: m1[z] != m2[z];
		var z:T :| m1[z] != m2[z];
		assert (m + m1)[z] != (m + m2)[z];
		assert m + m1 != m + m2;
	}
}

lemma firstElem_Lemma<T>(s1:seq<T>, s2:seq<T>)
	requires s1 != [] && multiset(s1) == multiset(s2)
	ensures exists i :: 0 <= i < |s2| && s2[i] == s1[0] && 
		multiset(s1[1..]) == multiset(s2[..i] + s2[i+1..]);
{
	assert s1[0] in multiset(s2);
	assert exists i :: 0 <= i < |s2| && s2[i] == s1[0];
	var i :| 0 <= i < |s2| && s2[i] == s1[0];

	assert s1 == [s1[0]] + s1[1..];
	assert multiset(s1) == multiset{s1[0]} + multiset(s1[1..]);

	assert s2 == s2[..i] + [s2[i]] + s2[i+1..];
	assert multiset(s2) == multiset{s2[i]} + multiset(s2[..i]) + multiset(s2[i+1..]);
	
	union_Lemma(multiset{s2[i]}, multiset(s1[1..]), multiset(s2[..i]) + multiset(s2[i+1..]));
	assert multiset(s1[1..]) == multiset(s2[..i]) + multiset(s2[i+1..]);
	assert multiset(s1[1..]) == multiset(s2[..i] + s2[i+1..]); 
}

lemma sumElems_Lemma(s:seq<int>, r:seq<int>)   
	requires multiset(s) == multiset(r)
	ensures sum(s) == sum(r)
{
	if s == [] {
		// assert multiset(r) == multiset{};
		Empty_Lemma(r);
		// assert r == [];
		// assert sum(s) == sum(r) == 0;
	}
	else {
		assert s == [s[0]] + s[1..];
		assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
		// lemma para este assume
		firstElem_Lemma(s, r);
		assert exists i :: 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i] + r[i+1..]);
		var i :| 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i] + r[i+1..]);
		sumElems_Lemma(s[1..], r[..i] + r[i+1..]); // llamada para hipotesis de induccion
		// assert sum(s[1..]) == sum(r[..i] + r[i+1..]); // HI
		// assert sum(s) == s[0] + sum(s[1..]);
		// Ejercicio lemma para este assume
		sumProp_Lemma(r);
		assert sum(r) == r[i] + sum(r[..i] + r[i+1..]);
		assert sum(s) == sum(r);
	}
}

// Ejercicio probar
lemma sumProp_Lemma(r:seq<int>)
	ensures forall i :: 0 <= i < |r| ==> sum(r) == r[i] + sum(r[..i] + r[i+1..])


//MAPS

method map_Examples() {
	var m1: map<int,int> := map[] ;  
	var m2:map<int, bool> := map[20 := true, 3 := false, 20 := false]; 
	assert m2[20] == false;
	var m2' := m2[20 := true];
	assert m2[20] == false;
	var m2'' := m2'[10 := false];
	assert m2''[20] == true;
	assert m2''[10] == false;
	assert m2''.Keys == {20, 3, 10};
	assert m2''.Values == {true, false};
	assert |m2''| == 3;

	var a:int,b:int,c:int,d: int;
	var m3 := map[a+b := c+d];

	// comprenhesions
	var m4 := map x : int | 0 <= x <= 10 :: x * x;
	assert m4[7] == 49;
	ghost var im1 := imap x : int :: x * x;
	assert im1[7] == 49;
	ghost var im2 := imap x : int | x%2 == 0 :: x * x;
	assert im2[6] == 36;
	assert 7 !in im2;
}

// Ejemplo de mapa infinito con eventos temporales
type structure = imap<nat, set<string>>

method test() {
	var sigma: structure;
	sigma := imap[0:={"p"}, 1:={"q"}];
}

predicate wellFormedStructure(sigma: structure)
{
	forall i: nat :: i in sigma.Keys
}

function suffix(sigma: structure, n: nat): (sigma': structure)
	requires wellFormedStructure(sigma)
	ensures wellFormedStructure(sigma')
{
	imap i: nat :: sigma[i+n]
}

lemma suffixSum_Lemma(sigma: structure, n: nat, m: nat)
	requires wellFormedStructure(sigma)
	ensures suffix(suffix(sigma, n), m) == suffix(sigma, n+m)
{
}

// Ejemplo contains
method contains_Value<T, U(==)>(m: map<T, U>, val: U) returns (b: bool)
	ensures b <==> val in m.Values
{
	var m' := m;
	while m' != map[]
		invariant m'.Keys <= m.Keys
		// invariant forall v :: v in m'.Values ==> v in m.Values
		// Este solo funciona sin el return false
		// Se conserva, pero no sirve para probar la val !in m.Values
		invariant forall k :: k in m'.Keys ==> m'[k] == m[k]
		invariant val in m.Values ==> val in m'.Values
		decreases m' // |m'| no lo prueba
	{
		var k :| k in m';
		if m'[k] == val {
			return true; // No equivalente a b:=true porque termina
			// assume b <==> val in m.Values;
		}
		m' := map k' | k' in m' && k' != k :: m'[k'];
	}
	assert val !in m.Values;
	assert false <==> val in m.Values;
	return false; // b:= false
	assert b <==> val in m.Values;
}


// Ejemplo Inyectiva
predicate mapInyectiva<U, V> (m:map<U,V>)
{
	forall a,b :: a in m && b in m && a != b ==> m[a] != m[b]
}

// Ejercicio definir el predicado
predicate mapsAreInverse<U, V>(m: map<U,V>, m': map<V,U>)
{
	(forall k :: k in m.Keys ==> m[k] in m'.Keys && m'[m[k]] == k) &&
	(forall k :: k in m'.Keys ==> m'[k] in m.Keys && m[m'[k]] == k)
	// El de arriba es más preciso
	// forall a :: a in m.Keys ==> exists b :: b in m'.Keys && m[a] == b && m'[b] == a
	// forall b :: b in m'.Keys ==> exists a :: a in m.Keys && m'[b] == a && m[a] == b
}

function union<U(!new), V>(m: map<U,V>, m': map<U,V>): (u: map<U,V>)
	// (!new) dice que un tipo de datos no usa memoria dinámica
	requires m !! m'
	ensures forall i :: i in u <==> i in m || i in m'
	ensures forall i :: i in m ==> u[i] == m[i]
	ensures forall i :: i in m' ==> u[i] == m'[i]
{
	map k | k in m.Keys + m'.Keys :: if k in m.Keys then m[k] else m'[k]
}

// Ejercicio terminar el metodo
method invertMap<U, V(==)>(m: map<U, V>) returns (m': map<V, U>)
	requires mapInyectiva(m)
	ensures	mapsAreInverse(m, m')
{
	var R := m;
	ghost var S: map<U,V> := map[];
	var I: map<V, U> := map[];
	while R != map[]
		invariant mapsAreInverse(S, I)
		invariant S !! R
		invariant m == union(S, R)
		decreases R
	{
		// Ejercicio hacer asserts intermedios
		// assert forall a :: a in R ==> mapsAreInverse(S[a := R[a]], I[R[a] := a]);
		var a :| a in R;
		// assert mapsAreInverse(S[a := R[a]], I[R[a] := a]);
		I := I[R[a] := a];
		// assert mapsAreInverse(S[a := R[a]], I);
		S := S[a := R[a]];
		R := map k | k in R && k != a :: R[k];
		// assert mapsAreInverse(S, I);
	}
	// assert mapsAreInverse(m, I);
	m' := I;
	// assert mapsAreInverse(m, m');
}

// Ejemplo composición
function composeMaps<U,V,W>(m: map<U,V>, m': map<V,W>): map<U,W>
{
	map k | k in m.Keys && m[k] in m'.Keys :: m'[m[k]]
}

lemma compose_assoc_Lemma<T,U,V,W>(m1: map<T,U>, m2: map<U,V>, m3: map<V,W>)
	ensures composeMaps(m1, composeMaps(m2,m3)) == composeMaps(composeMaps(m1, m2), m3)
{}

// Prueba por contraposición
lemma empty_map_Lemma<U,V,W>(m: map<U,V>, m': map<V,W>)
	requires composeMaps(m, m') == map[]
	ensures forall k :: k in m.Keys ==> m[k] !in m'
{
	if !(forall k :: k in m.Keys ==> m[k] !in m') {
		// assert exists k :: k in m.Keys ==> m[k] in m';
		var i :| i in m.Keys && m[i] in m';
		assert composeMaps(m, m')[i] == m'[m[i]];
		assert m'[m[i]] in composeMaps(m,m').Values;
		assert composeMaps(m,m') != map[];
	}
}

// Prueba directa
lemma map_size_Lemma<U,V>(m: map<U,V>, k1: U)
	requires |m| >= 1 && k1 in m
	ensures var m' := map k | k in m && k != k1 :: m[k];
		|m'| == |m| - 1
{
	var v := m[k1];
	var m' := map k | k in m && k != k1 :: m[k];
	assert m == m'[k1 := v];
	assert |m'| == |m| - 1;
}

// Ejercicio prueba directa
lemma disjoint_values_Lemma<U,V>(m: map<U,V>, k1: U)
	requires |m| >= 1 && k1 in m && mapInyectiva(m)
	ensures var m' := map k | k in m && k != k1 :: m[k];
		{m[k1]} !! m'.Values && m.Values == {m[k1]} + m'.Values
{
	var m' := map k | k in m && k != k1 :: m[k];
	// Opcion 1
	assert m == m'[k1 := m[k1]];
	// Opcion 2
	assert forall k :: k in m.Keys ==> k == k1 || k in m'.Keys;
	// assert {m[k1]} !! m'.Values && m.Values == {m[k1]} + m'.Values;
}

// Ejercicio prueba contradictiva
lemma disjoint_values_Lemma2<U,V>(m: map<U,V>, k1: U)
	requires |m| >= 1 && k1 in m && mapInyectiva(m)
	ensures var m' := map k | k in m && k != k1 :: m[k];
		{m[k1]} !! m'.Values && m.Values == {m[k1]} + m'.Values
{
	var m' := map k | k in m && k != k1 :: m[k];
	if !({m[k1]} !! m'.Values && m.Values == {m[k1]} + m'.Values) {
		// assert !({m[k1]} !! m'.Values) || !(m.Values == {m[k1]} + m'.Values);
		assert m[k1] in m'.Values || exists i :: i in m'.Keys && m[i] !in m'.Values;
		assert !mapInyectiva(m);
		assert mapInyectiva(m');
		assert false;
	}
}

// Ejercicio prueba por inducción
lemma inject_size_Lemma<U,V>(m:map<U,V>)
	requires mapInyectiva(m)
	ensures |m.Values| == |m.Keys|
{
	if |m.Keys| != 0 {
	var key :| key in m.Keys;
	var MminusKey := map k | k in m && k != key :: m[k];
	calc {
		|m.Values|;
		{
			disjoint_values_Lemma(m, key);
			// assert {m[key]} !! MminusKey.Values && m.Values == {m[key]} + MminusKey.Values;
		}
		|MminusKey.Values| + 1;
		{
			inject_size_Lemma(MminusKey);
			// assert |MminusKey.Values| == |MminusKey.Keys|;
		}
		|MminusKey.Keys| + 1;
		{
			map_size_Lemma(m, key);
			// assert |MminusKey| == |m| - 1;
		}
		|m.Keys|;
		}
	}
	// Se puede resumir la prueba solo a las llamadas
	/*if |m.Keys| != 0 {
		var key :| key in m.Keys;
		var MminusKey := map k | k in m && k != key :: m[k];
		disjoint_values_Lemma(m, key);
		inject_size_Lemma(MminusKey);
		map_size_Lemma(m, key);
	}*/
}

// Ejercicios

// 1. Prueba por inducción en s
lemma sets_car_Lemma<T>(s:set<T>, u:set<T>)
	requires s <= u
	ensures |s| <= |u|

// 2.
function min(a: int, b: int): int
{
	if a <= b then a else b
}

function zip<S,R>(s: seq<S>, r: seq<R>): seq<(S,R)>
{
	if s == [] || r == [] then []
	else [(s[0], r[0])] + zip(s[1..], r[1..])
}

method test2()
{
	assert zip([1,2,3], ["a","b","c"]) == [(1,"a"), (2,"b"), (3,"c")];
}

// Prueba por induccion en s con calc
lemma {:induction false} zip_Length_Lemma<S,R> (s:seq<S>, r:seq<R>)
	ensures |zip(s,r)| == min(|s|, |r|)
{
	if s != [] && r != [] {
		calc {
			|zip(s,r)|;
			|[(s[0], r[0])] + zip(s[1..], r[1..])|;
			|[(s[0], r[0])]| + |zip(s[1..], r[1..])|;
			1 + |zip(s[1..], r[1..])|;
			{
				zip_Length_Lemma(s[1..], r[1..]);
				// assert |zip(s[1..],r[1..])| == min(|s[1..]|, |r[1..]|);
			}
			1 + min(|s[1..]|, |r[1..]|);
			min(|s|, |r|);
		}
	}
}

// para no tener que burcarla
function composeMaps2<U,V,W>(m: map<U,V>, m': map<V,W>): map<U,W>
{
	map k | k in m.Keys && m[k] in m'.Keys :: m'[m[k]]
}

// 3. Prueba directa, se puede usar map_size_Lemma
lemma size_compose_Lemma<U,V,W>(m: map<U,V>, m': map<V,W>)
	ensures |composeMaps(m, m')| <= |m|