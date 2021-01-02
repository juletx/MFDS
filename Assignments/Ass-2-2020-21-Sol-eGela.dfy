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
    var i, f := 0, 1;
    facts := [1];
        while i < n 
            invariant  0 <= i <= n                               
            invariant  f == factorial(i) 	
            invariant facts == factSeq(i)
        {
            f, i := f*(i+1), i+1;   
            facts := facts + [f];
        }
}

method VCG_compute_Fact()
{
    assert forall n:nat :: 0 <= n && 1 == factorial(0) && [1] == factSeq(0);
    assert forall n,i,f, facts ::
        (0 <= i <= n && f == factorial(i) && facts == factSeq(i) && i < n) ==>
        (0 <= i+1 <= n && f*(i+1) == factorial(i+1) && facts + [f*(i+1)] == factSeq(i+1));			  

    assert forall i,n,f, facts ::
        (0 <= i <= n && f == factorial(i) && facts == factSeq(i) && i >= n) ==>
        facts == factSeq(n);
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

lemma unzip_zip_Lemma<T,S>(r:seq<T>, s:seq<S>)
    requires |r| == |s|
    ensures unzip(zip(r,s)) == (r,s) 
{
    if r == [] && s == [] { }
    else {
        assert r == [r[0]] + r[1..];
        assert s == [s[0]] + s[1..];
        unzip_zip_Lemma(r[1..], s[1..]);
        //assert unzip(zip(r[1..], s[1..])) == (r[1..], s[1..]); //HI
        assert unzip(zip([r[0]] + r[1..],[s[0]] + s[1..])) == unzip(zip(r,s)) == (r,s);
    }
}

// EJERCICIO 3

lemma sets_size_Lemma<T>(s: set<T>, u: set<T> )
    requires s < u 
    ensures |s| < |u|
    //solo usar, no probar

lemma set_Lemma_Directa<T> (s1:set<T>,s2:set<T>, n:nat)
    requires s1 < s2 && |s2| <= n // s1 est� contenido en s2 y s2 tiene a lo sumo n elementos
    ensures |s1 * s2| < n  // la intersecci�n de s1 y s2 tiene menos de n elementos
{//prueba directa
    assert s1 * s2 == s1;
    sets_size_Lemma(s1,s2);
    assert |s1| < |s2| <= n;
}

lemma set_Lemma_Contr<T> (s1:set<T>,s2:set<T>, n:nat)
    requires s1 < s2 && |s2| <= n // s1 est� contenido en s2 y s2 tiene a lo sumo n elementos
    ensures |s1 * s2| < n  // la intersecci�n de s1 y s2 tiene menos de n elementos
{//prueba por contradicci�n/ contraposici�n
    if |s1 * s2| >= n
    {
        assert |s1 * s2| >= |s2|;
        assert s1 * s2 == s1;
        assert |s1| >= |s2|;
        sets_size_Lemma(s1,s2);
        assert !(s1 < s2);
    }
}


// EJERCICIO 4

predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> a != b ==> m[a] != m[b]
}

lemma sets_card_Lemma<T>(s:set<T>,u:set<T>)
    requires s <= u
    ensures |s| <= |u|
    // No demostrar, s�lo usar

lemma trivial_inject_Lemma<U,V>(m: map<U,V>)
    requires |m| <= 1
    ensures mapInjective(m)
{ // Contraposici�n/ Contradicci�n
    if !mapInjective(m) {
        //assert exists  a,b :: a in m && b in m && a != b && m[a] == m[b];
        var k1, k2 :| k1 in m && k2 in m && k1 != k2 && m[k1] == m[k2];
        assert {k1, k2} <= m.Keys;
        sets_card_Lemma({k1, k2}, m.Keys);
        //assert 2 <= |m.Keys|;
        //assert |m| >= 2;
    }
}


// EJERCICIO 5

function union<U(!new), V>(m: map<U,V>, m': map<U,V>): map<U,V>
	requires m !! m' // disjoint
{
    map i | i in (m.Keys + m'.Keys) :: if i in m then m[i] else m'[i]
}

function composeMaps<U,V,W>(m:map<U,V>,m':map<V,W>): map<U,W>
{
    map k | k in m && m[k] in m' :: m'[m[k]]
}

method compute_comp_maps<U,V,W>(m:map<U,V>,m':map<V,W>) returns (C:map<U,W>)
    ensures C == composeMaps(m,m')
{
    ghost var A:map<U,W> := map[]; //para evitar los problemas de tipos del assert de abajo
    assert m !! map[] && m == union(map[],m) && A == composeMaps(map[],m');
    C := map[];
    var M := m;
    ghost var N:map<U,V> := map[];
    while M != map[] 
        decreases M
        invariant M !! N
        invariant m == union(N,M)
        invariant C == composeMaps(N,m');
        {
            assert forall k :: k in M ==>
                    ( m[k] in m' && (map i | i in M && i != k :: M[i]) !! N[k := m[k]] &&  
                    m == union(N[k := m[k]],map i | i in M && i != k :: M[i]) && 
                    C[k := m'[m[k]]] == composeMaps(N[k := m[k]],m')) 
                    ||
                    (m[k] !in m' && (map i | i in M && i != k :: M[i]) !! N[k := m[k]] &&  
                    m == union(N[k := m[k]],map i | i in M && i != k :: M[i]) && 
                    C == composeMaps(N[k := m[k]],m'));
            var k :| k in M;
            assert ( m[k] in m' && (map i | i in M && i != k :: M[i]) !! N[k := m[k]] &&  
                    m == union(N[k := m[k]],map i | i in M && i != k :: M[i]) && 
                    C[k := m'[m[k]]] == composeMaps(N[k := m[k]],m')) 
                    ||
                    (m[k] !in m' && (map i | i in M && i != k :: M[i]) !! N[k := m[k]] &&  
                    m == union(N[k := m[k]],map i | i in M && i != k :: M[i]) && 
                    C == composeMaps(N[k := m[k]],m'));
            if m[k] in m' { C := C[k := m'[m[k]]]; }
            assert (map i | i in M && i != k :: M[i]) !! N[k := m[k]] &&  
                    m == union(N[k := m[k]],map i | i in M && i != k :: M[i]) && 
                    C == composeMaps(N[k := m[k]],m');
            M := map i | i in M && i != k :: M[i];
            assert M !! N[k := m[k]] &&  m == union(N[k := m[k]],M) && C == composeMaps(N[k := m[k]],m');
            N := N[k := m[k]];
            assert M !! N &&  m == union(N,M) && C == composeMaps(N,m');
        }
}