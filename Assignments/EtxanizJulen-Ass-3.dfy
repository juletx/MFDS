datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate isSubList<T> (xs:List, ys:List)
//[3,5] es sublista [1,2,3,4,5], pero no lo es [5,3]
{
	xs == Nil || 
	(ys != Nil && ((xs.head == ys.head && isSubList(xs.tail,ys.tail)) ||
				   (xs.head != ys.head && isSubList(xs,ys.tail))))
}

//ESTE LEMMA, QUE SE DEMUESTRA AUTOMÁTICAMENTE, ES PARA USAR, SI LO NECESITAS
lemma Refl_isSubList_Lemma<T>(xs:List)
	ensures isSubList(xs,xs)
{} 

//EJERCICIO 1

//(a) DEMOSTRAR EL SIGUIENTE LEMMA (POR EL MÉTODO QUE SE ELIJA)
lemma cons_append_Lemma<T>(xs:List<T>)
	ensures forall x:T :: isSubList(xs,Cons(x,xs))
{
	forall x: T
		ensures isSubList(xs,Cons(x,xs))
	{
		match xs {
			case Nil => 
			case Cons(h, t) => {
				calc {
					Cons(x,xs) != Nil;
					{
						Refl_isSubList_Lemma(xs);
						// assert isSubList(xs, xs);
					}
					if h == Cons(x,xs).head then isSubList(t, Cons(x, xs).tail) else isSubList(xs, Cons(x, xs).tail);
					isSubList(xs, Cons(x,xs));
				}
			}
		}
	}
}

//(b) DEMOSTRAR EL SIGUIENTE LEMMA POR INDUCCIÓN EN xs.tail
lemma {:induction false} tail_SubList_Lemma<T>(xs:List,ys:List)
	requires xs.Cons? && isSubList(xs,ys) 
	ensures isSubList(xs.tail,ys)
/*{
	match xs
		case Nil =>
		case Cons(h, t) => {
			if t.Cons? && ys.Cons? && isSubList(t,ys) {
				tail_SubList_Lemma(t, ys);
				assert isSubList(t.tail,ys);
			}
		}
}*/


//(c) DEMOSTRAR EL SIGUIENTE LEMMA POR INDUCCIÓN EN xs
//    INDICACIÓN: UTILIZAR LE LEMMA tail_SubList_Lemma.
lemma isSubList_Trans_Lemma<T>(xs:List,ys:List,zs:List)
	requires isSubList(xs,ys) && isSubList(ys,zs)
	ensures isSubList(xs,zs)
{
	match xs {
		case Nil =>
		case Cons(h, t) => {
			if t != Nil && ys != Nil {
				assert isSubList(xs,ys);
				tail_SubList_Lemma(xs, ys);
				assert isSubList(t, ys);
				assert isSubList(ys, zs);
				isSubList_Trans_Lemma(t, ys, zs);
				assert isSubList(t, zs);
			}
		}
	}
}

// EJERCICIO 2
// DEMOSTRAR EL LEMA filterTreeSubsec_Lemma
datatype Tree<T> = Leaf(T) | Node(left:Tree<T>, root:T, right:Tree<T>)

function mset_list<T>(xs:List):multiset<T>
{
	match xs
		case Nil => multiset{}
		case Cons(h,t) => multiset{h} + mset_list(t)
}

function append<T> (xs:List,ys:List):List
	ensures mset_list(append(xs,ys)) == mset_list(xs) + mset_list(ys) 
// ACTIVAR SI LO NECESITAS
{
	if xs.Nil? then ys else Cons(xs.head,append(xs.tail,ys))
}

function aplanar<T>(t:Tree<T>):List<T>
{
	match t
		case Leaf(x) => Cons(x,Nil)
		case Node(ti,r,td) => append(aplanar(ti),Cons(r,aplanar(td)))
}

function filterTree<V>(p:V->bool,t:Tree<V>):List<V>
{
	match t
		case Leaf(x) => if p(x) then Cons(x,Nil) else Nil
		case Node(ti,r,td) => if p(r) then append(filterTree(p,ti),Cons(r,filterTree(p,td)))
								  else append(filterTree(p,ti),filterTree(p,td))
}

// DEMOSTRAR EL SIGUIENTE LEMA POR INDUCCION EN t:Tree
lemma filterTreeSubsec_Lemma<T>(p:T -> bool, t:Tree<T>)
	ensures isSubList(filterTree(p,t),aplanar(t))
/*{
	match t 
		case Leaf(x) =>
		case Node(l, m, r) => {
			if l.Node? {
				filterTreeSubsec_Lemma(p, l);
				assert isSubList(filterTree(p,l),aplanar(l));
			}
			if r.Node? {
				filterTreeSubsec_Lemma(p, r);
				assert isSubList(filterTree(p,r),aplanar(r));
			}
		}
}*/

// EJERCICIO 3
// Diseñar un método verificado que satisfaga el siguiente contrato:
method part_array_in_sets (p:int -> bool, a:array<int>) returns (s1:set<int>,s2:set<int>)
	ensures s1 == (set i | 0 <= i < a.Length && p(a[i]) :: a[i] )
	ensures s2 == (set i | 0 <= i < a.Length && !p(a[i]) :: a[i] )
{
	var k := 0;
	s1, s2 := {}, {};
	while k < a.Length
		invariant 0 <= k <= a.Length
		invariant s1 == (set i | 0 <= i < k && p(a[i]) :: a[i] )
		invariant s2 == (set i | 0 <= i < k && !p(a[i]) :: a[i] )
	{
		if p(a[k]) {
			s1 := s1 + {a[k]};
		}
		else {
			s2 := s2 + {a[k]};
		}
		k := k + 1;
	}
}

// EJERCICIO 4
// Usando el método de la bandera holandesa, 
// diseñar un método que tome como argumento un array de ENTEROS y una función p: nat -> bool (o predicado),
// y clasifique los elementos del array en tres clases: 
//			1.- los enteros negativos, 
//          2.- los naturales que cumplen p y 
//          3.- los naturales que no cumplen p. 
// El orden relativo entre las tres clases, y la posición relativa de los elementos sin tratar, 
// se puede elegir libremente.

predicate ord(x:int, y:int, p: nat->bool)
{
	x < 0 || (x >= 0 && p(x) && y >= 0 && p(y)) || (y >= 0 && !p(y))
}

/*predicate ord(x:int, y:int, p: nat->bool)
{
	(x < 0 && y < 0) ||
	(x < 0 && y >= 0 && p(y)) || 
	(x >= 0 && p(x) && y >= 0 && p(y)) || 
	(x >= 0 && p(x) && y >= 0 && !p(y)) || 
	(x >= 0 && !p(x) && y >= 0 && !p(y))
}*/

predicate perm<T>(s:seq<T>,r:seq<T>)
{
	multiset(s) == multiset(r)
}

method DutchFlag(a: array<int>, p: nat->bool)
	modifies a
	ensures perm(a[..], old(a[..]))
	ensures forall i,j :: 0 <= i < j < a.Length ==> ord(a[i], a[j], p)
{
	var x, y, z := 0, 0, a.Length;
	while x < y
		invariant 0 <= x <= y <= z <= a.Length
		invariant forall i :: 0 <= i < x ==> a[i] < 0
		invariant forall i :: x <= i < y ==> a[i] >= 0 && p(a[i])
		invariant forall i :: z <= i < a.Length ==> a[i] >= 0 && !p(a[i])
		invariant perm(a[..], old(a[..]))
	{
		if a[x] < 0 {
			a[x], a[y] := a[y], a[x];
			x, y := x + 1, y + 1;
		}
		if a[x] >= 0 && p(a[x]) {
			y := y + 1;
		}
		if a[x] >= 0 && !p(a[x]) {
			a[x], a[z-1] := a[z-1], a[x];
			z := z - 1;
		}
	}
}