//EJERCICIO 1

function factorial (n:nat):nat
{
	if n == 0 then 1 else n * factorial(n-1)
}

function factSeq (n:nat):seq<nat>
{
	if n == 0 then [1] else factSeq(n-1) + [n * factorial(n-1)]
}

method compute_Fact_Seq (n: nat) returns (facts: seq<nat>)
	ensures facts == factSeq(n)									  
{
	// assert 0 <= 0 <= n && 1 == factorial(0) && [1] == factSeq(0);
	var i, f := 0, 1;
	// assert 0 <= i <= n && f == factorial(i) && [1] == factSeq(i);
	facts := [1];
	// assert 0 <= i <= n && f == factorial(i) && facts == factSeq(i);
	while i < n
		// Poner los invariantes y activar la post
		invariant 0 <= i <= n
		invariant f == factorial(i)
		invariant facts == factSeq(i)
	{
		// assert 0 <= i <= n && f*(i+1) == factorial(i+1) && facts + [f*(i+1)] == factSeq(i+1);
		f, i := f*(i+1), i+1;
		// assert 0 <= i <= n && f == factorial(i) && facts + [f] == factSeq(i);
		facts := facts + [f];
		// assert 0 <= i <= n && f == factorial(i) && facts == factSeq(i);
	}
}

method VCG_compute_Fact_Seq()
{
// Escribe aquí las tres condiciones de verificación que
// hacen que el método compute_Fact_Seq sea verificado

// VC1: el invariante se cumple al entrar
assert forall n: nat :: 0 <= 0 <= n && 1 == factorial(0) && [1] == factSeq(0);

// VC2: el invariante se conserva
assert forall i, n: nat, f, facts :: 0 <= i <= n && f == factorial(i) && facts == factSeq(i) && i < n
	==> 0 <= i <= n && f*(i+1) == factorial(i+1) && facts + [f*(i+1)] == factSeq(i+1);

// VC3: el invariante garantiza la post
assert forall i, n: nat, f, facts :: 0 <= i <= n && f == factorial(i) && facts == factSeq(i) && i >= n
	==> facts == factSeq(n);
}

// EJERCICIO 2

function min(a:int, b:int):int
{
	if a <= b then a else b
}

function zip<T,S>(r:seq<T>, s:seq<S>): seq<(T,S)>
	ensures |zip(r,s)| == min(|r|,|s|) 
{
	if r == [] || s == []  then []
	else [(r[0],s[0])] + zip(r[1..],s[1..])
}

function unzip<T,S> (z:seq<(T,S)>):(seq<T>,seq<S>)
{
	if z == []  then ([],[])
	else ( [z[0].0] + unzip(z[1..]).0, [z[0].1] + unzip(z[1..]).1 )
}

// Demostrar este lema por inducción 
lemma unzip_zip_Lemma<T,S>(r:seq<T>, s:seq<S>)
	requires |r| == |s|
	ensures unzip(zip(r,s)) == (r,s)
{
	if r != [] {
		calc {
			unzip(zip(r,s));
			unzip([(r[0],s[0])] + zip(r[1..],s[1..]));
			{
				unzip_zip_Lemma(r[1..], s[1..]);
				// assert unzip(zip(r[1..],s[1..])) == (r[1..],s[1..]);
			}
			([r[0]] + r[1..], [s[0]] + s[1..]);
			{
				assert r == [r[0]] + r[1..];
				assert s == [s[0]] + s[1..];
			}
			(r,s);
		}
	}
}


// EJERCICIO 3

//No demostrar, solo usar más abajo, si necesario
lemma sets_size_Lemma<T>(s: set<T>, u: set<T> )
	requires s < u 
	ensures |s| < |u|

//Demostrar este lemma mediante una prueba directa
lemma set_Lemma_Directa<T> (s1:set<T>,s2:set<T>, n:nat)
	requires s1 < s2 && |s2| <= n 
	ensures |s1 * s2| < n
{
	assert s1 * s2 <= s2;
	sets_size_Lemma(s1 * s2, s2);
	assert |s1 * s2| < |s2|;
	assert |s1 * s2| < n;
}

//Demostrar el mismo lemma, pero ahora con una prueba por contradicción/contraposición
lemma set_Lemma_Contr<T> (s1:set<T>,s2:set<T>, n:nat)
	requires s1 < s2 && |s2| <= n
	ensures |s1 * s2| < n
{
	if |s1 * s2| >= n {
		assert s1 * s2 <= s2;
		sets_size_Lemma(s1 * s2, s2);
		assert |s1 * s2| <= |s2|;
		assert |s1| >= |s2|;
		assert s1 >= s2;
		assert false;
	}
}

// EJERCICIO 4

predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> a != b ==> m[a] != m[b]
}

//No demostrar, solo usar más abajo, si necesario
lemma sets_card_Lemma<T>(s:set<T>,u:set<T>)
	requires s <= u
	ensures |s| <= |u|


// Demostrar este lemma por el método que se elija.
/*lemma trivial_inject_Lemma<U,V>(m: map<U,V>)
	requires |m| <= 1
	ensures mapInjective(m)
{
	if !mapInjective(m) {
		var m' := map k | k in m :: m[k];
		assert exists a,b :: a in m && b in m ==> a != b ==> m[a] == m[b];
		var a, b :| a in m && b in m ==> a != b ==> m[a] == m[b];
		sets_card_Lemma(m.Keys, m'.Keys);
		assert |m.Keys| <= |m'.Keys|;
		//assert |m| == 2;
	}
}*/


// EJERCICIO 5

//Esta función puede hacerte falta para completar el ejercicio
function union<U(!new), V>(m: map<U,V>, m': map<U,V>): map<U,V>
	requires m !! m' 
{
	map i | i in (m.Keys + m'.Keys) :: if i in m then m[i] else m'[i]
}

function composeMaps<U,V,W>(m:map<U,V>,m':map<V,W>): map<U,W>
{
	map k | k in m && m[k] in m' :: m'[m[k]]
}

method compute_composeMaps<U,V,W>(m:map<U,V>,m':map<V,W>) returns (C:map<U,W>)
	ensures C == composeMaps(m,m')
{
	ghost var T: map<U,W> := map[];
	assert T == composeMaps(map[], m');
	C := map[];
	assert C == composeMaps(map[], m');
	var M := m;
	ghost var S: map<U, V> := map[];
	assert C == composeMaps(S, m');
	while M != map[] 
		decreases M
		// Poner los invariantes y activar la post
		// Indicación: usar una variable ghost
		invariant C == composeMaps(S, m')
		invariant S !! M
		invariant m == union(S, M)
	{
		assert forall k :: k in M ==> (m[k] in m' && C[k := m'[m[k]]] == composeMaps(S[k := M[k]], m')) || 
		(m[k] !in m' && C == composeMaps(S[k := M[k]], m'));
		var k :| k in M;
		assert (m[k] in m' && C[k := m'[m[k]]] == composeMaps(S[k := M[k]], m')) || 
		(m[k] !in m' && C == composeMaps(S[k := M[k]], m'));
		if m[k] in m' {
			assert C[k := m'[m[k]]] == composeMaps(S[k := M[k]], m');
			C := C[k := m'[m[k]]]; 
		}
		assert C == composeMaps(S[k := M[k]], m');
		S := S[k := M[k]];
		M := map i | i in M && i != k :: M[i];
		assert C == composeMaps(S, m');
	}
}

method VCG_compute_comp_maps<U,V,W>()
{
// Escribe aquí las tres condiciones de verificación que
// hacen que el método compute_comp_maps sea verificado

// VC1: el invariante se cumple al entrar
assert forall m: map<U,W>, m':map<V,W> :: m == map[] ==> m == composeMaps(map[], m');

// VC2: el invariante se conserva
assert forall C:map<U,W>, S: map<U, V>, m':map<V,W>, k:U, M:map<U,V>, m:map<U,V> :: 
	(C == composeMaps(S, m') && S !! M && m == union(S, M) && M != map[]) ==> 
	(forall k :: k in M ==> (m[k] in m' && C[k := m'[m[k]]] == composeMaps(S[k := M[k]], m')) || 
	(m[k] !in m' && C == composeMaps(S[k := M[k]], m')));

// VC3: el invariante garantiza la post
assert forall C:map<U,W>, S: map<U, V>, m':map<V,W>, k:U, M:map<U,V>, m:map<U,V> :: 
	(C == composeMaps(S, m') && S !! M && m == union(S, M) && M == map[]) ==> 
	(C == composeMaps(m, m'));
}