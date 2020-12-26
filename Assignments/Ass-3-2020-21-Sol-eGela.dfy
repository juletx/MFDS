datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate isSubList<T> (xs:List, ys:List)
{
xs == Nil || 
(ys != Nil && ((xs.head == ys.head && isSubList(xs.tail,ys.tail)) ||
               (xs.head != ys.head && isSubList(xs,ys.tail))))
}

lemma Refl_isSubList_Lemma<T>(xs:List)
ensures isSubList(xs,xs)
{} //NO DEMOSTRAR, SÓLO USAR

//EJERCICIO 1
//EJERCICIO 1(a)
lemma cons_append_Lemma<T>(xs:List<T>)
ensures forall x:T :: isSubList(xs,Cons(x,xs))
{ //POR INDUCCIÓN
forall x:T 
   ensures isSubList(xs,Cons(x,xs))
		{
		//assert Cons(x,xs).head == x;
		//assert Cons(x,xs).tail == xs;
		//assert xs.Cons? ==> isSubList(xs.tail,xs);
		if xs.Cons? { cons_append_Lemma(xs.tail); }
		//assert isSubList(xs,xs);
		Refl_isSubList_Lemma(xs);
		//assert xs == Nil ||  (((xs.head == x && isSubList(xs.tail,xs)) || (xs.head != x && isSubList(xs,xs))));
		}
}


//EJERCICIO 1(b)
//DEMOSTRAR EL SIGUIENTE LEMMA POR INDUCCIÓN EN xs.tail
lemma  {:induction false} tail_SubList_Lemma<T>(xs:List,ys:List)
requires xs.Cons? && isSubList(xs,ys) 
ensures isSubList(xs.tail,ys) 
{ //Por contradicción
    if !isSubList(xs.tail,ys) {
        //assert xs.tail != Nil;
        //assert ys != Nil;
        
        if xs.head != ys.head {
		    //assert isSubList(xs,ys.tail);
		    tail_SubList_Lemma(xs,ys.tail); 
		    //assert isSubList(xs.tail,ys.tail); //HI	
		    right_tail_SubList_Lemma(xs.tail,ys);
			//assert isSubList(xs.tail,ys);
			assert false;
        }else{ //assert isSubList(xs.tail, ys.tail);
		     if xs.tail.Cons? { tail_SubList_Lemma(xs.tail, ys.tail); 
								//assert isSubList(xs.tail.tail,ys.tail); //HI
								//assert isSubList(xs.tail,ys);
								assert false;
							  }
        }
    }
}

lemma right_tail_SubList_Lemma(us:List,vs:List)
requires vs.Cons? && isSubList(us,vs.tail) 
ensures isSubList(us,vs)
{ //Por contradicción
if vs.Cons? && !isSubList(us,vs) {
                      //assert us.Cons?;
                      //assert (us.head != vs.head && !isSubList(us,vs.tail)) || 
					  //       (us.head == vs.head && !isSubList(us.tail,vs.tail));
					  if us.head == vs.head { if !isSubList(us.tail,vs.tail)
												{ //Otra contradicción
												tail_SubList_Lemma(us,vs.tail);
												//assert !isSubList(us,vs.tail);										
											    }
					                        }
					  assert !isSubList(us,vs.tail);
                      }
}

//EJERCICIO 1(c)
lemma {:induction false} isSubList_Trans_Lemma<T>(xs:List,ys:List,zs:List)
requires isSubList(xs,ys) && isSubList(ys,zs)
ensures isSubList(xs,zs)
{
if !xs.Nil?  {
    //assert ys != Nil && zs != Nil;
    //assert (xs.head == ys.head && isSubList(xs.tail,ys.tail)) ||
    //       (xs.head != ys.head && isSubList(xs,ys.tail));
	//assert (ys.head == zs.head && isSubList(ys.tail,zs.tail)) ||
    //       (ys.head != zs.head && isSubList(ys,zs.tail));
	if xs.head == zs.head 
	  { if xs.head == ys.head 
	        { isSubList_Trans_Lemma(xs.tail,ys.tail,zs.tail); }
	   else { 
	        //assert xs.head != ys.head && ys.head != zs.head && xs.head == zs.head;
			//assert isSubList(xs,ys.tail) && isSubList(ys,zs.tail);
			tail_SubList_Lemma(ys,zs.tail);
			//assert isSubList(ys.tail,zs.tail);
			tail_SubList_Lemma(xs,ys.tail);
			//assert isSubList(xs.tail,ys.tail);
	        isSubList_Trans_Lemma(xs.tail,ys.tail,zs.tail);
			}
		//assert isSubList(xs.tail,zs.tail);
	  }
	else { 
	     //assert xs.head != zs.head;
		 if ys.head == zs.head { 
		                       //assert isSubList(xs,ys.tail) && isSubList(ys.tail,zs.tail);
	                           isSubList_Trans_Lemma(xs,ys.tail,zs.tail);
							   }
		 else {
			   //assert isSubList(xs,ys.tail) && isSubList(ys,zs.tail);
			   isSubList_Trans_Lemma(xs,ys,zs.tail);
			   }
		 //assert isSubList(xs,zs.tail);
		 }
    //assert (xs.head == zs.head && isSubList(xs.tail,zs.tail)) ||
    //       (xs.head != zs.head && isSubList(xs,zs.tail));
    }
}


//EJERCICIO 2
datatype Tree<T> = Leaf(T) | Node(left:Tree<T>, root:T, right:Tree<T>)

function mset_list<T>(xs:List):multiset<T>
{
match xs
case Nil => multiset{}
case Cons(h,t) => multiset{h} + mset_list(t)
}

function append<T> (xs:List,ys:List):List
ensures mset_list(append(xs,ys)) == mset_list(xs) + mset_list(ys)
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

lemma filterTreeSubsec_Lemma<T> (p:T -> bool, t:Tree<T>)
ensures isSubList(filterTree(p,t),aplanar(t))
{
assert isSubList(Cons(3,Cons(5,Nil)),Cons(1,Cons(2,Cons(3,Cons(4,Cons(5,Nil))))));
//assert isSubList(Cons(5,Cons(3,Nil)),Cons(1,Cons(2,Cons(3,Cons(4,Cons(5,Nil))))));
match t
case Leaf(x) => {}
case Node(ti,r,td) => {
                       filterTreeSubsec_Lemma(p,ti);
					   //assert isSubList(filterTree(p,ti),aplanar(ti)); //HI
					   filterTreeSubsec_Lemma(p,td);
					   //assert isSubList(filterTree(p,td),aplanar(td)); //HI
					   if p(r) {isSubList_append_Lemma(filterTree(p,ti),aplanar(ti),Cons(r,filterTree(p,td)),Cons(r,aplanar(td)));
					            //Abajo
					            //assert isSubList(append(filterTree(p,ti),Cons(r,filterTree(p,td))), 
					            //                  append(aplanar(ti),Cons(r,aplanar(td))));
								}
						else { cons_append_Lemma(aplanar(td));
							   isSubList_Trans_Lemma(filterTree(p,td),aplanar(td),Cons(r,aplanar(td)));
						       isSubList_append_Lemma(filterTree(p,ti),aplanar(ti),filterTree(p,td),Cons(r,aplanar(td))); //Abajo
						       //assert isSubList(append(filterTree(p,ti),filterTree(p,td)), 
					           //                  append(aplanar(ti),Cons(r,aplanar(td))));
							 }
}
}

//Lemma auxiliar 
lemma isSubList_append_Lemma<T> (xs:List<T>,vs:List<T>,ys:List<T>,us:List<T>)
requires isSubList(xs,vs) && isSubList(ys,us) 
ensures isSubList(append(xs,ys),append(vs,us))
{
if xs == Nil   {//assert isSubList(ys,us);
			   append_subList_Lemma(us,vs);  //Abajo
			   //assert isSubList(us,append(vs,us));
			   isSubList_Trans_Lemma(ys,us, append(vs,us));
			   //assert isSubList(ys,append(vs,us));
               }
else { 
     //assert append(xs,ys) == Cons(xs.head,append(xs.tail,ys));
	 if xs.head == vs.head { isSubList_append_Lemma(xs.tail,vs.tail,ys,us); }
	                  else { isSubList_append_Lemma(xs,vs.tail,ys,us);}
     }
}

//Lema auxiliar
lemma append_subList_Lemma<T> (ys:List<T>, zs:List<T>)
ensures isSubList(ys,append(zs,ys))
{
if zs == Nil {//assert append(zs,ys) == ys;
			   Refl_isSubList_Lemma(ys);
               //assert isSubList(ys,ys);
             }
else {
     append_subList_Lemma(ys,zs.tail);
	 //assert isSubList(ys,append(zs.tail,ys)); //HI
	 cons_append_Lemma(append(zs.tail,ys));
     //assert forall x:T :: isSubList(append(zs.tail,ys),Cons(x,append(zs.tail,ys)));
	 //assert isSubList(append(zs.tail,ys),Cons(zs.head,append(zs.tail,ys)));
	 isSubList_Trans_Lemma(ys, append(zs.tail,ys),Cons(zs.head,append(zs.tail,ys)));
     //assert isSubList(ys,Cons(zs.head,append(zs.tail,ys)));
     }
}


//EJERCICIO 3

//Diseñar un método verificado que satisfaga el siguiente contrato:
method part_array_in_sets (p:int -> bool, a:array<int>) returns (s1:set<int>,s2:set<int>)
ensures s1 == (set i | 0 <= i < a.Length && p(a[i]) :: a[i] )
ensures s2 == (set i | 0 <= i < a.Length && !p(a[i]) :: a[i] )
{
var k := 0;
s1, s2 := {},{};
while k < a.Length
    invariant 0 <= k <= a.Length
	invariant s1 == (set i | 0 <= i < k && p(a[i]) :: a[i] ) 
	invariant s2 == (set i | 0 <= i < k && !p(a[i]) :: a[i] )
	{
	if p(a[k]) { s1 := s1 + {a[k]}; }
	      else { s2 := s2 + {a[k]}; }
	k := k+1;
	}
}

//EJERCICIO 4
//Usando el método de la bandera holandesa, 
//diseñar un método que tome como argumento un array de ENTEROS y una función p: nat -> bool (o predicado),
//y clasifique los elementos del array en tres clases: los enteros negativos, los naturales que cumplen p
//y los naturales que no cumplen p. El orden relativo entre las tres clases y la posición relativa de 
//los elementos sin tratar se puede elegir libremente.

predicate LEQT(p:nat -> bool, x:int, y:int)
{
x < 0  || (x >= 0 && y >= 0 && (p(x) || (p(x) <==> p(y)) || !p(y))) 
}

predicate perm<T>(s:seq<T>,r:seq<T>)
{
multiset(s) == multiset(r)
}

method DutchFlag(p:nat->bool, a:array<int>)
	modifies a
	ensures forall i, j :: 0 <= i < j < a.Length ==> LEQT(p,a[i],a[j])
	ensures perm(a[..],old(a[..]))
{
var neg,cp,notp := 0, a.Length, a.Length;
while neg < cp
	invariant 0 <= neg <= cp <= notp <= a.Length
	invariant forall i :: 0 <= i < neg ==> a[i] < 0
	invariant forall i :: cp <= i < notp ==> (a[i] >= 0 && p(a[i])) 
	invariant forall i :: notp <= i < a.Length ==> (a[i] >= 0 && !p(a[i]))
	invariant perm(a[..],old(a[..]))
	{
	if a[neg] < 0  { 
	               neg := neg + 1; 
				   }
	else if p(a[neg]) { 
	                   a[neg],a[cp-1] := a[cp-1],a[neg]; 
					   cp := cp-1;
					   }
	else { 
	      a[neg],a[cp-1] := a[cp-1],a[neg]; 
	      a[cp-1],a[notp-1] := a[notp-1],a[cp-1]; 
	      cp,notp := cp-1,notp-1;
		  }
	}
}
