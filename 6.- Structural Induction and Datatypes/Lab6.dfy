datatype List<T> = Nil | Cons(head:T, tail:List)

datatype Tree<T> = Nil | Node(left:Tree, root:T, right:Tree)

function length<T> (xs:List<T>):nat
decreases xs
{
match xs 
    case Nil => 0
	case Cons(_,t) => 1 + length(t)
//if xs.Nil? then 0 else 1 + length(xs.tail)
//if xs == List.Nil then 0 else 1 + length(xs.tail)
}

function EqPairs (xs:List):nat
{
match xs
	case Nil => 0
/*	case Cons(h, Nil) => 0
	case Cons(h1,Cons(h2,t)) => if h1 == h2 then 1 + EqPairs(Cons(h2,t))
	                                        else EqPairs(Cons(h2,t))  */
	case Cons(h,t) => if t.Nil? then 0
	                  else if h == t.head then 1 + EqPairs(t)
					  else EqPairs(t)
}

function max (x:int,y:int):int
{
if x >= y then x else y
}

function depth<T> (t:Tree):nat
{
match t
case Nil => 0
case Node(l,_,r) => 1 + max(depth(l),depth(r))
}

predicate full<T> (t:Tree)
{
/*match t
case Nil => true
case Node(l,_,r) => (l.Nil? && r.Nil?) || 
                    (l.Node? && r.Node? && full(t.left) && full(t.right))
*/
t.Nil? || 
(t.left.Nil? && t.right.Nil?) || 
(t.left.Node? && t.right.Node? && full(t.left) && full(t.right))
}

lemma {:induction false} EqPairs_Lemma (xs:List)
ensures EqPairs(xs) <= length(xs)
{
match xs {
case Nil => 
case Cons(_,t) => { //EqPairs_Lemma(t); // assert EqPairs(t) <= length(t);
                   calc {
				        EqPairs(xs); 
						<= 1 + EqPairs(t);
						<=	{
							EqPairs_Lemma(t);
							//assert EqPairs(t) <= length(t); //HI
							}
						1 + length(t);
						== length(xs);
				  }
                  }
}
}

function append<T> (xs:List,ys:List):List
{
if xs.Nil? then ys else Cons(xs.head,append(xs.tail,ys))
}

function rev(xs:List):List
{
match xs
case Nil => List.Nil
case Cons(h,t) => append(rev(t), Cons(h,List.Nil))
}

lemma {:induction false} length_append_Lemma<T>(xs:List,ys:List)
ensures length(append(xs,ys)) == length(xs) + length(ys)
// EJERCICIO PARA CASA

lemma revAppend_Lemma<T> (xs:List,ys:List)
ensures rev(append(xs,ys)) == append(rev(ys),rev(xs))
//EJERCICIO PARA CASA

lemma rev_twice_Lemma<T> (xs:List)
ensures rev(rev(xs)) == xs
{
match xs
case Nil =>
case Cons(h,t) => {
					 calc {
					       rev(rev(Cons(h,t))); //def. rev
						   rev(append(rev(t), Cons(h,List.Nil)));
							   {
							   revAppend_Lemma(rev(t),Cons(h,List.Nil));
							   }
						   append(rev(Cons(h,List.Nil)),rev(rev(t)));
						      {
							  rev_twice_Lemma(t);
					          //assert rev(rev(t)) == t; //HI
							  }
                          append(rev(Cons(h,List.Nil)),t);
						  Cons(h,t);
					 }
                  }
}

/// FUNCIONES DE ORDEN SUPERIOR

function filter<T> (p:T -> bool,xs:List<T>):List<T>
{
match xs
case Nil => List.Nil
case Cons(h,t) => if p(h) then Cons(h,filter(p,t)) else filter(p,t)
}

lemma {:induction false} filterConmutes_Lemma<T> (xs:List, p:T->bool, q:T->bool)
ensures filter(p,filter(q,xs)) == filter(q,filter(p,xs))
{
match xs
case Nil => 
case Cons(h,t) => {
                    calc{
					filter(p,filter(q,xs)); //def. filter
					if filter(q,xs) == List.Nil then List.Nil  //EXP
					else if p(filter(q,xs).head) 
					     then Cons(filter(q,xs).head, filter(p,filter(q,xs).tail))
						 else filter(p,filter(q,xs).tail);  
                    if filter(q,xs) == List.Nil then List.Nil 
					else if p(h) && q(h)
					     then Cons(h, filter(p,filter(q,t)))
						 else filter(p,filter(q,t));
                      {
					  filterConmutes_Lemma(t,p,q);
					  //assert filter(p,filter(q,t)) == filter(q,filter(p,t)); //HI
					  }
					if filter(p,xs) == List.Nil then List.Nil 
					else if p(h) && q(h)
					     then Cons(h, filter(q,filter(p,t)))
						 else filter(q,filter(p,t));
					//EXP'
					filter(q,filter(p,xs));
					}
                   }
}

predicate isSubList<T> (xs:List, ys:List)
//[3,5] es sublista [1,2,3,4,5], pero no lo es [5,3]
{
xs == List.Nil || 
(ys != List.Nil && ((xs.head == ys.head && isSubList(xs.tail,ys.tail))
                    ||
                   (xs.head != ys.head && isSubList(xs,ys.tail))))
}

lemma filterSubList_Lemma<T>(p:T->bool, xs:List)
ensures isSubList(filter(p,xs),xs)
//EJERCICIO PARA CASA

// METODOS SORT CON LISTAS

predicate sorted (xs:List<int>)
{
xs == List.Nil ||
(xs.tail != List.Nil ==> (xs.head <= xs.tail.head && sorted(xs.tail)))
//(xs.tail == List.Nil || (xs.head <= xs.tail.head && sorted(xs.tail)))
}

function mset_list<T>(xs:List):multiset<T>
{
match xs
case Nil => multiset{}
case Cons(h,t) => multiset{h} + mset_list(t)
}

method insertionSort(xs:List<int>) returns (ys:List<int>)
//ensures sorted(ys)
//ensures mset_list(ys) == mset_list(xs)
{
match xs
case Nil => { ys := List.Nil;}
case Cons(h,t) => {
                    var aux := insertionSort(t);
					//assert sorted(aux) && mset_list(aux) == mset_list(t);//HI
					//ys := insert(h,aux); 
					//EJERCICIO PARA CASA: código (recursivo) de insertar un elemento x
					//en una lista ordenada xs.
                  }
}