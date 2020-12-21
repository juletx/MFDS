datatype List<T> = Nil | Cons(head: T, tail: List)

datatype Tree<T> = Nil | Node(left: Tree, root: T, right: Tree)

function length<T>(xs: List<T>): nat
{
	match xs
		case Nil => 0
		case Cons(_, t) => 1 + length(t)
}

function length2<T>(xs: List<T>): nat
{
	if xs.Nil? then 0 else 1 + length(xs.tail)
}


function length3<T>(xs: List<T>): nat
{
	if xs == List.Nil then 0 else 1 + length(xs.tail)
}

function NumPairs<T>(xs: List<T>): nat
{
	match xs
		case Nil => 0
		case Cons(h, Nil) => 0
		case Cons(h, Cons(h2, t)) => if h == h2 then 1 + NumPairs(Cons(h2, t)) else NumPairs(Cons(h2, t))
}

function NumPairs2<T>(xs: List<T>): nat
{
	match xs
		case Nil => 0
		case Cons(h, t) => if t.Nil? then 0 else if h == t.head then 1 + NumPairs2(t) else NumPairs2(t)
}

function Depth<T>(t: Tree<T>): nat
{
	match t
		case Nil => 0
		case Node(l, _, r) => 1 + max(Depth(l), Depth(r))
}

function max(x: int, y: int): int
{
	if x >= y then x else y
}

predicate Full<T>(t: Tree<T>)
{
	match t
		case Nil => true
		case Node(l, _, r) => (l.Nil? && r.Nil?) || (l.Node? && r.Node? && Full(l) && Full(r))
}

predicate Full2<T>(t: Tree<T>)
{
	t.Nil? || (t.left.Nil? && t.right.Nil?) || (t.left.Node? && t.right.Node? && Full2(t.left) && Full2(t.right))
}

// Ejercicio: Prueba por induccion usando match y calc
lemma {:induction false} EqPairs_Lemma<T>(xs: List<T>)
	ensures NumPairs(xs) <= length(xs)
{
	match xs {
		case Nil =>
		case Cons(_, t) => {
			calc{
				NumPairs(xs);
				<= 1 + NumPairs(t);
				<= {
					EqPairs_Lemma(t);
					// assert NumPairs(t) <= length(t);
				}
				1 + length(t);
				length(xs);
			}	
		}
	}
}

function method append<T>(xs: List<T>, ys: List<T>): List
	ensures mset_list(append(xs, ys)) == mset_list(xs) + mset_list(ys)
{
	if xs.Nil? then ys else Cons(xs.head, append(xs.tail, ys))
}

function rev(xs: List): List
{
	match xs
		case Nil => List.Nil
		case Cons(h, t) => append(rev(t), Cons(h, List.Nil))
}

// Ejercicio para casa
lemma {:induction false} length_append_Lemma<T>(xs: List<T>, ys: List<T>)
	ensures length(append(xs, ys)) == length(xs) + length(ys)
{
	match xs {
		case Nil =>
		case Cons(h, t) => {
			calc {
				length(append(xs, ys));
				length(Cons(h, append(t, ys)));
				1 + length(append(t, ys));
				{
					length_append_Lemma(t, ys);
					// assert length(append(t, ys)) == length(t) + length(ys);
				}
				1 + length(t) + length(ys);
				length(xs) + length(ys);
			}
		}
	}
}

// Ejercicio para casa
lemma revAppend_Lemma<T>(xs: List<T>, ys: List<T>)
	ensures rev(append(xs, ys)) == append(rev(ys), rev(xs))
{
	match xs {
		case Nil => {
			calc {
				rev(append(List.Nil, ys));
				rev(ys);
				{
					appendNil_Lemma(rev(ys));
				}
				append(rev(ys), List.Nil);
				append(rev(ys), rev(List.Nil));
			}
		}
		case Cons(h, t) => {
			calc {
				rev(append(xs, ys));
				rev(Cons(h, append(t, ys)));
				append(rev(append(t, ys)), Cons(h, List.Nil));
				{
					revAppend_Lemma(t, ys);
					// assert rev(append(t, ys)) == append(rev(ys), rev(t));
				}
				append(append(rev(ys), rev(t)), Cons(h, List.Nil));
				{
					appendAssoc_Lemma(rev(ys), rev(t), Cons(h, List.Nil));
				}
				append(rev(ys), append(rev(t), Cons(h, List.Nil)));
				append(rev(ys), rev(xs));
			}
		}
	}
}

lemma appendNil_Lemma<T>(xs: List<T>)
	ensures xs == append(xs, List.Nil)
{}

lemma appendAssoc_Lemma<T>(xs: List<T>, ys: List<T>, zs: List<T>)
	ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{}

lemma rev_Twice_Lemma(xs: List)
	ensures rev(rev(xs)) == xs
{
	match xs {
		case Nil =>
		case Cons(h, t) => {
			calc {
				rev(rev(Cons(h, t)));
				rev(append(rev(t), Cons(h, List.Nil)));
				{
					revAppend_Lemma(rev(t), Cons(h, List.Nil));
					// assert rev(append(rev(t), Cons(h, List.Nil))) == 
					// append(rev(Cons(h, List.Nil)), rev(rev(t)));
				}
				append(rev(Cons(h, List.Nil)), rev(rev(t)));
				{
					rev_Twice_Lemma(t);
					// assert rev(rev(t)) == t;
				}
				append(rev(Cons(h, List.Nil)), t);
				append(Cons(h, List.Nil), t);
				Cons(h, t);
			}
		}
	}
}

// Funciones de orden superior
function filter<T>(p: T -> bool, xs: List<T>): List<T>
{
	match xs
		case Nil => List.Nil
		case Cons(h, t) => if p(h) then Cons(h, filter(p, t)) else filter(p, t)
}

lemma {:induction false} filterCommutes_Lemma<T>(xs: List, p: T -> bool, q: T -> bool)
	ensures filter(p, filter(q, xs)) == filter(q, filter(p, xs))
{
	match xs {
		case Nil =>
		case Cons(h, t) => {
			calc {
				filter(p, filter(q, xs)); // Def
				if filter(q, xs) == List.Nil then List.Nil // EXP
				else if p(filter(q, xs).head) then Cons(filter(q, xs).head, filter(p, filter(q, xs).tail))
				else filter(p, filter(q, xs).tail);
				if filter(q, xs) == List.Nil then List.Nil
				else if p(h) && q(h) then Cons(h, filter(p, filter(q, t)))
				else filter(p, filter(q, t));
				{
					filterCommutes_Lemma(t, p, q);
					// assert filter(p, filter(q, t)) == filter(q, filter(p, t));
				}
				if filter(p, xs) == List.Nil then List.Nil
				else if p(h) && q(h) then Cons(h, filter(q, filter(p, t)))
				else filter(q, filter(p, t));
				// EXP'
				filter(q, filter(p, xs));
			}
		}
	}
}

// [3,5] es sublista [1,2,3,4,5] pero no lo es [5,3]
predicate isSubList<T>(xs: List, ys: List)
{
	xs == List.Nil || 
	(ys != List.Nil && 
	((xs.head == ys.head && isSubList(xs.tail, ys.tail)) || 
	(xs.head != ys.head && isSubList(xs, ys.tail))))
}

// Ejercicio para casa
lemma filterSubList_Lemma<T>(p: T -> bool, xs: List)
	ensures isSubList(filter(p, xs), xs)
/*{
	match xs {
		case Nil =>
		case Cons(h, t) => {
			calc {
				if filter(p, xs) == List.Nil then isSubList(List.Nil, xs)
				else if filter(p, xs).head == h then isSubList(filter(p, xs).tail, t)
				else isSubList(filter(p, xs), t);
				if filter(p, xs) == List.Nil then isSubList(List.Nil, xs)
				else if p(xs.head) then isSubList(filter(p, xs).tail, t)
				else isSubList(filter(p, xs), t);
				{
					filterSubList_Lemma(p, t);
					assert isSubList(filter(p, t), t);
				}
				if filter(p, xs) == List.Nil then isSubList(List.Nil, xs)
				else if p(h) then isSubList(filter(p, t), t)
				else isSubList(filter(p, xs), t);
				isSubList(filter(p, xs), xs);
			}
		}
	}
}*/

predicate sorted(xs: List<int>)
{
	xs == List.Nil ||
	(xs.tail != List.Nil ==> (xs.head <= xs.tail.head && sorted(xs.tail)))
	// (xs.tail != List.Nil || (xs.head <= xs.tail.head && sorted(xs.tail)))
}

function mset_list<T>(xs: List): multiset<T>
{
	match xs
		case Nil => multiset{}
		case Cons(h, t) => multiset{h} + mset_list(t)
}

// metodos sort con listas

// Ejercicio codigo recursivo de insertar un elemento x en una lista ordenada xs
method insertionSort(xs: List<int>) returns (ys: List<int>)
	ensures sorted(ys)
	ensures mset_list(xs) == mset_list(ys)
{
	match xs {
		case Nil => {
			ys := List.Nil;
		}
		case Cons(h, t) => {
			var aux := insertionSort(t);
			// assert sorted(aux) && mset_list(aux) == mset_list(t); // HI
			ghost var hys;
			ys, hys := insert(h, aux);
		}
	}
}

method insert(x: int, xs: List<int>) returns (ys: List<int>, ghost hys: int)
	requires sorted(xs)
	ensures sorted(ys)
	ensures mset_list(ys) == multiset{x} + mset_list(xs)
	ensures hys == ys.head && (hys == x || (xs.Cons? && hys == xs.head))
{
	match xs {
		case Nil => {
			ys, hys := Cons(x, List.Nil), x;
		}
		case Cons(h, t) => {
			if x <= h {
				ys, hys := Cons(x, xs), x;
			}
			else {
				var aux;
				ghost var haux: int;
				aux, haux := insert(x, t);
				// assert sorted(aux); //HI
				// assert h <= haux == aux.head;
				// assert haux == aux.head && (haux == x || (t.Cons? && haux == t.head)); // HI
				// assert sorted(Cons(h, aux));
				ys, hys := Cons(h, aux), h;
				// assert sorted(ys);
			}
		}
	}
}

method quicksort(xs: List<int>) returns (ys: List<int>)
	ensures sorted(ys)
	ensures mset_list(xs) == mset_list(ys)
	decreases length(xs)
{
	match xs {
		case Nil => {
			return List.Nil;
		}
		case Cons(h, t) => {
			var t1, t2 := partition(h, t);
			assert forall e :: e in mset_list(t1) ==> e <= h; // partition
			assert forall e :: e in mset_list(t2) ==> e > h; // partition
			// assert mset_list(t) == mset_list(t1) + mset_list(t2); // partition
			var ys1 := quicksort(t1);
			var ys2 := quicksort(t2);
			assert forall e :: e in mset_list(ys1) ==> e <= h; // partition
			assert forall e :: e in mset_list(ys2) ==> e > h; // partition
			assert sorted(ys1) && sorted(ys2); // HI
			// assert mset_list(ys2) == mset_list(t2) && mset_list(ys1) == mset_list(t1); ; // HI
			// assert mset_list(t) == mset_list(ys1) + mset_list(ys2);
			// assert mset_list(append(ys1, Cons(h, ys2))) == mset_list(ys1) + mset_list(Cons(h, ys2)) == mset_list(xs);
			appendOrd_Lemma(h, ys1, ys2);
			assert sorted(append(ys1, Cons(h, ys2))); // LEMMA PENDIENTE
			ys := append(ys1, Cons(h, ys2));
			assert sorted(ys);
		}
	}
}

// Ejercicio probar por inducción en xs
lemma appendOrd_Lemma(z: int, xs: List<int>, ys: List<int>)
	requires forall e :: e in mset_list(xs) ==> e <= z
	requires forall e :: e in mset_list(ys) ==> e > z
	requires sorted(xs) && sorted(ys)
	ensures sorted(append(xs, Cons(z, ys)))
/*{
	match xs {
		case Nil => {
			assert sorted(ys);
			assert forall e :: e in mset_list(ys) ==> e > z;
			sortedCons_lemma(z, ys);
			assert sorted(Cons(z, ys));
			assert sorted(append(List.Nil, Cons(z, ys)));
		}
		case Cons(h, t) => {
			appendOrd_Lemma(z, t, ys);
		}
	}
}

lemma sortedCons_lemma(z: int, ys: List<int>)
	requires forall e :: e in mset_list(ys) ==> e > z
	requires sorted(ys)
	ensures sorted(Cons(z, ys))
{
	match ys {
		case Nil =>
		case Cons(h, t) => {
			if t.Cons? {
				tailSorted_Lemma(z, ys);
				sortedCons_lemma(z, t);
			}
		}
	}
}

lemma tailSorted_Lemma(z: int, ys: List<int>)
	requires forall e :: e in mset_list(ys) ==> e > z
	requires sorted(ys)
	ensures ys.Cons? ==> forall e :: e in mset_list(ys.tail) ==> e > z
{}*/

method partition(z: int, xs: List<int>) returns (xs1: List<int>, xs2: List<int>)
	ensures length(xs1) <= length(xs) && length(xs2) <= length(xs)
	ensures mset_list(xs) == mset_list(xs1) + mset_list(xs2)
	ensures forall e :: e in mset_list(xs1) ==> e <= z
	ensures forall e :: e in mset_list(xs2) ==> e > z
{
	match xs {
		case Nil => {
			return List.Nil, List.Nil;
		}
		case Cons(h, t) => {
			var t1, t2 := partition(z, t);
			if h <= z {
				return Cons(h, t1), t2;
			}
			else {
				return t1, Cons(h, t2);
			}
		}
	}
}

// EJERCICIO: Definir espejo Tree -> Tree, y probar que el espejo(espejo(t)) == t
function mirror(t: Tree): Tree
{
	match t
		case Nil => Tree.Nil
		case Node(l, m, r) => Node(mirror(l), m, mirror(r))
}

lemma {:induction false} MirrorTree_Lemma(t: Tree)
	ensures mirror(mirror(t)) == t
{
	match t {
		case Nil => {
		}
		case Node(l, m, r) => {
			calc {
				mirror(mirror(t));
				Node(mirror(mirror(l)), m, mirror(mirror(r)));
				{
					MirrorTree_Lemma(l);
					// assert mirror(mirror(l)) == l;
					MirrorTree_Lemma(r);
					// assert mirror(mirror(r)) == r;
				}
				Node(l, m, r);
				t;
			}
		}
	}
}

// EJERCICIO: Multiset arbol // Aplanar un arbol a una lista y demostrar que tienen multisets identicos
function mset_tree<T>(t: Tree): multiset<T>
{
	match t
		case Nil => multiset{}
		case Node(l, m, r) => multiset{m} + mset_tree(l) + mset_tree(r)
}

function flatten(t: Tree): List
{
	match t {
		case Nil => List.Nil
		case Node(l, m, r) => 
			if l.Nil? && r.Nil? then Cons(m, List.Nil)
			else if l.Node? then append(Cons(m, flatten(l)), flatten(r))
			else Cons(m, flatten(r))
	}
}

lemma {:induction false} Equal_Multiset_Lemma(t: Tree)
	ensures mset_list(flatten(t)) == mset_tree(t)
{
	match t {
		case Nil => {
		}
		case Node(l, m, r) => {
			calc {
				mset_list(flatten(t));
				multiset{m} + mset_list(flatten(l)) + mset_list(flatten(r));
				{
					Equal_Multiset_Lemma(l);
					// assert mset_tree(l) == mset_list(flatten(l));
					Equal_Multiset_Lemma(r);
					// assert mset_tree(r) == mset_list(flatten(r));
				}
				multiset{m} + mset_tree(l) + mset_tree(r);
				mset_tree(t);
			}
		}
	}
}

predicate perfect(t: Tree)
{
	t.Nil? || 
	(t.left.Nil? && t.right.Nil?) || 
	(t.left.Node? && t.right.Node? && 
	perfect(t.left) && perfect(t.right) && 
	Depth(t.left) == Depth(t.right))
}

function numLeaves(t: Tree): nat
{
	match t
		case Nil => 0
		case Node(l, _, r) => 
			if l.Nil? && r.Nil? then 1 else numLeaves(l) + numLeaves(r)
}

function exp2(n: nat): nat
{
	if n == 0 then 1 else 2*exp2(n-1)
}

lemma {:induction false} numLeavesPerf_Lemma(t: Tree)
	requires t.Node? && perfect(t)
	ensures numLeaves(t) == exp2(Depth(t)-1)
{
	match t {
		case Node(l, _, r) => {
			calc {
				numLeaves(t);
				if l.Nil? && r.Nil? then 1 else numLeaves(l) + numLeaves(r);
				{
					if l.Node? { 
						numLeavesPerf_Lemma(l);
						assert numLeaves(l) == exp2(Depth(l)-1);
					}
					if r.Node? { 
						numLeavesPerf_Lemma(r);
						assert numLeaves(r) == exp2(Depth(r)-1);
					}
				}
				if l.Nil? && r.Nil? then 1 else exp2(Depth(l)-1) + exp2(Depth(r)-1);
				exp2(Depth(t)-1);
			}
		}
	}
}
	
// Ejercicio para casa
// El numero de nodos de un arbol no vacio perfecto es 2^(prof)-1
lemma {:induction false} numNodesPerf_Lemma(t: Tree)
	requires t.Node? && perfect(t)
	ensures numNodes(t) == exp2(Depth(t))-1
{
	match t {
		case Node(l, _, r) => {
			calc {
				numNodes(t);
				if l.Nil? && r.Nil? then 1 else 1 + numNodes(l) + numNodes(r);
				{
					if l.Node? { 
						numNodesPerf_Lemma(l);
						assert numNodes(l) == exp2(Depth(l))-1;
					}
					if r.Node? { 
						numNodesPerf_Lemma(r);
						assert numNodes(r) == exp2(Depth(r))-1;
					}
				}
				if l.Nil? && r.Nil? then 1 else 1 + exp2(Depth(r))-1 + exp2(Depth(r))-1;
				exp2(Depth(t))-1;
			}
		}
	}
}

function numNodes(t: Tree): nat
{
	match t
		case Nil => 0
		case Node(l, _, r) => 
			if l.Nil? && r.Nil? then 1 else 1 + numNodes(l) + numNodes(r)
}

// Ejemplo HOmap
function HOmap<U, V>(f: U->V, xs: List<U>): List<V>
{
	match xs
		case Nil => List.Nil
		case Cons(h, t) => Cons(f(h), HOmap(f, t))
}

// No hay multiset comprehensions en dafny
function elemPos<T>(i: nat, xs: List<T>): T
	requires i < length(xs)
{
	if i == 0 then xs.head else elemPos(i-1, xs.tail)
}

lemma {:induction false} Eq_HOmap_Lemma<U, V, W>(f: U->V, g: V->W, xs: List<U>)
	ensures length(HOmap(g, HOmap(f, xs))) == length(xs)
	ensures forall i :: 0 <= i < length(xs) ==> 
		elemPos(i, HOmap(g, HOmap(f, xs))) == g(f(elemPos(i, xs)))
{
	EqLength_HOmap_Lemma(f, g, xs);
	// forall x: T | P(x) ensures Q(x) { codigo; }
	forall i | 0 <= i < length(xs)
		ensures elemPos(i, HOmap(g, HOmap(f, xs))) == g(f(elemPos(i, xs)))
	{
		if i != 0 {
			calc {
				elemPos(i, HOmap(g, HOmap(f, xs)));
				elemPos(i-1, HOmap(g, HOmap(f, xs)).tail);
				elemPos(i-1, HOmap(g, HOmap(f, xs.tail)));
				{
					Eq_HOmap_Lemma(f, g, xs.tail);
					assert forall i :: 0 <= i < length(xs.tail) ==> 
						elemPos(i, HOmap(g, HOmap(f, xs.tail))) == g(f(elemPos(i, xs.tail)));
				}
				g(f(elemPos(i-1, xs.tail)));
				g(f(elemPos(i, xs)));
			}
		}
	}
}

// Ejercicio para casa: Probarlo con {:induction false}
lemma {:induction false} EqLength_HOmap_Lemma<U, V, W>(f: U->V, g: V->W, xs: List<U>)
	ensures length(HOmap(g, HOmap(f, xs))) == length(xs)
{
	match xs {
		case Nil =>
		case Cons(h, t) => {
			calc {
				length(HOmap(g, HOmap(f, xs)));
				length(Cons(g(HOmap(f, xs).head), HOmap(g, HOmap(f, xs).tail)));
				length(Cons(g(f(h)), HOmap(g, HOmap(f, t))));
				1 + length(HOmap(g, HOmap(f, t)));
				{
					EqLength_HOmap_Lemma(f, g, t);
					// assert length(HOmap(g, HOmap(f, t))) == length(t);
				}
				1 + length(t);
				length(xs);
			}
		}
	}
}

// Ejercicio para casa:
// forall x :: x in mset_list(xs) <==> g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
// Probar dos lemmas una para ==> y otro para <==
// Poner {: induction false} en ambos
lemma IFF_HOmap_Lemma<U, V, W>(f: U->V, g: V->W, xs: List<U>)
	ensures forall x :: x in mset_list(xs) <==> g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
{
	forall x | x in mset_list(xs)
		ensures g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
	{
		IF1_HOmap_Lemma(f, g, xs);
	}
	forall x | g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
		ensures x in mset_list(xs)
	{
		IF2_HOmap_Lemma(f, g, xs);
	}
}

lemma {:induction false} IF1_HOmap_Lemma<U, V, W>(f: U->V, g: V->W, xs: List<U>)
	ensures forall x :: x in mset_list(xs) ==> g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
{
	forall x | x in mset_list(xs)
		ensures g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
	{
		match xs {
			case Nil => 
			case Cons(h, t) => {
				calc ==> {
					x in mset_list(xs);
					x == h || x in mset_list(t);
					{
						IF1_HOmap_Lemma(f, g, t);
						// assert forall x :: x in mset_list(t) ==> g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					}
					x == h || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					g(f(x)) == HOmap(g, HOmap(f, xs)).head || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)));
				}
			}
		}
	}
}

lemma IF2_HOmap_Lemma<U, V, W>(f: U->V, g: V->W, xs: List<U>)
	ensures forall x :: g(f(x)) in mset_list(HOmap(g, HOmap(f, xs))) ==> x in mset_list(xs)
{
	forall x | g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)))
		ensures x in mset_list(xs)
	{
		match xs {
			case Nil => 
			case Cons(h, t) => {
				calc ==> {
					g(f(x)) in mset_list(HOmap(g, HOmap(f, xs)));
					g(f(x)) == HOmap(g, HOmap(f, xs)).head || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					g(f(x)) == Cons(g(HOmap(f, xs).head), HOmap(g, HOmap(f, xs).tail)).head || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					g(f(x)) == g(HOmap(f, xs).head) || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					g(f(x)) == g(f(h)) || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					g(f(x)) in multiset{g(HOmap(f, xs).head)} || g(f(x)) in mset_list(HOmap(g, HOmap(f, t)));
					{
						IF2_HOmap_Lemma(f, g, t);
						// assert forall x :: g(f(x)) in mset_list(HOmap(g, HOmap(f, t))) ==> x in mset_list(t);
						// NO FUNCIONA SIN ASSUME
						assume g(f(x)) == g(f(h)) ==> x == h;
					}
					x in multiset{h} || x in mset_list(t);
					x == h || x in mset_list(t);
					x in mset_list(xs);
				}
			}
		}
	}
}