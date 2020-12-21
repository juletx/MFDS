// Ejercicio 1

/*
method rootApprox (x:int)  returns (r:int)
	requires x >= 0
	ensures r*r <= x < (r+1)*(r+1) 
{
//assert 0*0 <= x; //= wp(P, psi) = wp(P1;P2, psi)
r := 0; //P1
//assert r*r <= x; //Inv
while (r+1)*(r+1) <= x //P2
	invariant r*r <= x
	{
	assert (r+1)*(r+1) <= x;
	r := r+1; //P3
	assert r*r <= x;
	}
}
*/

method VC_for_rootApprox ()
{
//vc1: phi ==> wp(P,psi) : x>=0 ==> wp(P,r*r <= x < (r+1)*(r+1))
//assert forall x :: x >= 0 ==> 1*1 <= x; //Inicializacion no establece el Inv.
assert forall x :: x >= 0 ==> 0*0 <= x;
//vc2: (Inv && b) ==> wp(P3,Inv)
//wp(P3,Inv) = (r+1)*(r+1) <= x;              
assert forall x,r :: ( r*r <= x  &&  (r+1)*(r+1) <= x ) ==> (r+1)*(r+1) <= x ;
//vc3: (Inv && !b) ==> psi
assert forall x,r :: ( r*r <= x  &&  !((r+1)*(r+1) <= x)) ==> r*r <= x < (r+1)*(r+1) ;
}


//Ejercicio 2: method VC_for_compute_Fact1

function factorial (n:int):int
requires n >= 0
{
if n == 0 then 1 else n*factorial(n-1)
}

/*
method compute_Fact1 (n:int) returns (f:int)
requires n >= 0                 //phi
ensures f == factorial(n)       //psi
{
//assert 0 <= n <= n && 1 * factorial(n) == factorial(n); // wp(P1,Inv)
var x := n;
//assert 0 <= x <= n && 1 * factorial(x) == factorial(n);
f := 1;
//assert 0 <= x <= n && f * factorial(x) == factorial(n);
while x > 0
	invariant 0 <= x <= n
	invariant f * factorial(x) == factorial(n)
	//decreases x
	{
	//assert 0 <= x-1 <= n && f*x * factorial(x-1) == factorial(n);
	f, x := f*x, x-1; //P3
	//assert 0 <= x <= n && f * factorial(x) == factorial(n);
	}
}
*/

/*
method VC_for_compute_Fact1()
{
//VC1 : phi => wp(P1;P2, psi) = wp(P1, wp(while ...,psi)) = Wp(P1,Inv)
// P1 = x :=n, f:=1; // P2 = while ....
//phi ==> wp(P1,Inv) // P1 = x :=n, f:=1;
assert forall n :: n >= 0 ==> (0 <= n <= n  && 1 * factorial(n) == factorial(n));
//VC2 : Inv && b ==> wp(P3, Inv)
// wp(P3, Inv) = 0 <= x-1 <= n && f*x * factorial(x-1) == factorial(n);
assert forall x, n, f :: (0 <= x <= n && f * factorial(x) == factorial(n) && x > 0)
                          ==> (0 <= (x-1) <= n && f * x * factorial(x-1) == factorial(n));
//VC3 : Inv && !b ==> psi
assert forall x, n, f :: (0 <= x <= n && f * factorial(x) == factorial(n) && !(x > 0)) 
                          ==> f == factorial(n);
}
*/

//Ejercicio 2': Otra versión del factorial
/*
method compute_Fact2 (n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
var x := 0;
f := 1;
//assert 0 <= x <= n && f == factorial(x);
while x  < n
	invariant 0 <= x <= n
	invariant f == factorial(x)
	{
	x, f := x+1, f*(x+1);
	}
}
*/

method VC_for_compute_Fact2()
{
// VC1: el invariante se cumple al entrar: phi ==> wp(P1,Inv) // P1= x:=0, f:=1
assert forall n :: n >= 0 ==> (0 <= 0 <= n && 1 == factorial(0));
// VC2: el invariante se conserva: Inv && b ==> wp(P3,Inv)
assert forall x, n, f :: (0 <= x <= n && f == factorial(x) && x < n) 
                          ==> (0 <= x+1 <= n && f * (x+1) == factorial(x+1));
// VC3: el invariante garantiza la post: Inv && !b ==> psi
assert forall x, n, f :: (0 <= x <= n && f == factorial(x) && !(x < n)) 
                          ==> f == factorial(n);
}

// Ejercicio 3: method VC_for_computeSumPowers

function power2(e:nat):nat		
{
if e == 0 then 1 else 2*power2(e-1)
}

function sumPowers(n:nat):int
	requires n >= 1
// sumPowers(n) = 2^0 + 2^1 + ... + 2^(n-1) == 2^n -1
{
if n == 1 then 1 else sumPowers(n-1) + power2(n-1)
}

/*
method computeSumPowers(n:int) returns (r:int)  
	requires n >= 1
	ensures r == power2(n) - 1 // 2^n - 1 == sumPowers(n)
{
var k, p;
//assert 1 <= 1 <= n &&  1 == 1 * 2 - 1 == power2(1) - 1;
k, r, p:= 1, 1, 1;
//assert 1 <= k <= n &&  r == p * 2 - 1 == power2(k) - 1;
while k < n
		invariant 1 <= k <= n
		invariant r == p * 2 - 1 == power2(k) - 1 
		//invariant p == power2(k-1)
		{
		//assert 1 <= k+1 <= n &&  r+(2*p) == (2*p)*2 - 1 == power2(k+1) - 1; //wp(P,Inv)
		// donde P = p:=2*p; r, k := r + p, k+1;
    	p := 2 * p;
		//assert 1 <= k+1 <= n &&  r+p == p * 2 - 1 == power2(k+1) - 1;
		r, k := r + p, k+1;
		//assert 1 <= k <= n &&  r == p * 2 - 1 == power2(k) - 1;
		}
}
*/
method VC_for_computeSumPowers ()
{
// VC1: el invariante se cumple al entrar
assert forall n :: n >= 1 ==> (1 <= 1 <= n &&  1 == 1 * 2 - 1 == power2(1) - 1);
// VC2: el invariante se conserva: Inv && b ==> wp(P,Inv)
assert forall n, r, p, k :: (1 <= k <= n &&  r == p * 2 - 1 == power2(k) - 1 && k < n)
                        ==> 1 <= k+1 <= n &&  r + (2*p) == (2*p)*2 - 1 == power2(k+1) - 1;
	   // r == power2(k) - 1
	   // p == power2(k-1) ==> (2*p)*2 == power2(k+1)
	   // r + (2*p) == power2(k+1) - 1
// VC3: el invariante garantiza la post
assert forall n, r, p, k :: (1 <= k <= n &&  r == p * 2 - 1 == power2(k) - 1 && !(k < n))
                            ==> r == power2(n) - 1;
}

method prueba (x:int, y:int) returns (m:int)
ensures m >= x && m >= y
//ensures m == x || m == y
{
if x >= y {return x;} else {return y;}
}

method usar_prueba ()
{
var z := prueba(5,7);
assert z >= 5 && z >= 7;
//assert z == 5 || z == 7;
//assert z == 7;
}


// Ejercicio 4: method VC_computeFactTuring

method computeFactTuring (n:int) returns (u:int)
requires n >= 1
ensures u == factorial(n)
{
var r := 1;
u := 1;
while r < n
	invariant 1 <= r <= n
	invariant u == factorial(r)
{
assert 1 <= r+1 <= n && r >= 1 && u == factorial(r); //wp(P,Inv)
u := sig_fact(r,u);
assert 1 <= r+1 <= n && u == factorial(r+1);
r := r+1;
assert 1 <= r <= n && u == factorial(r);
}
}

//{r >= 1 && u == factorial(r)} u := sig_fact(r,u); {u == factorial(r+1)}
// wp(u := sig_fact(r,u), u == factorial(r+1)) == r >= 1 && u == factorial(r)

method VC_for_computeFactTuring ()
{
// VC1: el invariante se cumple al entrar
//EJERCICIO CASA
// VC2: el invariante se conserva Inv && b ==> wp(P,Inv)
assert forall r, n, u :: (1 <= r <= n && u == factorial(r) && r < n)
                          ==> (1 <= r+1 <= n && r >= 1 && u == factorial(r));
// VC3: el invariante garantiza la post
//EJERCICIO CASA
}

method sig_fact(r:int,u:int) returns (v:int)
requires r >= 1 && u == factorial(r)
ensures v == factorial(r+1)
{
//assert r >= 1 && u == factorial(r) && 1 <= 1 <= r+1 && u == 1 * factorial(r);
var s := 1;
v := u;
//assert r >= 1 && u == factorial(r) && 1 <= s <= r+1 && v == s * factorial(r);
while s < r+1
   invariant r >= 1 && u == factorial(r) 
   invariant 1 <= s <= r+1
   invariant v == s * factorial(r)
   {
   assert r >= 1 && u == factorial(r) && 1 <= s+1 <= r+1 && v+u == (s+1) * factorial(r);
   //wp(P,Inv)
   s, v := s+1, v+u; //P
   assert r >= 1 && u == factorial(r) && 1 <= s <= r+1 && v == s * factorial(r);
   }
}

method VC_for_sig_fact()
{
// VC1: el invariante se cumple al entrar phi ==> wp(Init, Inv)
assert forall r, u :: (r >= 1 && u == factorial(r)) ==>
       (r >= 1 && u == factorial(r) && 1 <= 1 <= r+1 && u == 1 * factorial(r));
// VC2: el invariante se conserva: Inv && b ==> wp(P,Inv)
assert forall r,u,s,v ::
       (r >= 1 && u == factorial(r) && 1 <= s <= r+1 && v == s * factorial(r) && s < r+1)
        ==> (r >= 1 && u == factorial(r) && 1 <= s+1 <= r+1 && v+u == (s+1) * factorial(r));
// VC3: el invariante garantiza la post
assert forall r,u,s,v ::
       (r >= 1 && u == factorial(r) && 1 <= s <= r+1 && v == s * factorial(r) && !(s < r+1))
	   // s == r+1 && v == s * factorial(r)
	   ==> v == factorial(r+1);
}

// Ejercicio 5

predicate noDivU(x:int, t:int)
{
forall z :: ( 1 < z < t ==> x % z != 0) 
}

predicate prime(x:int)
{ 
x >= 2  && noDivU(x,x) 
}

predicate noPrimesIn(a:int, b:int)
{
forall z :: a < z < b ==> !prime(z)
}

method next_prime (x:int) returns (p:int)
	requires prime(x)
	ensures p > x && prime(p) && noPrimesIn(x,p) //post1
	decreases *
{
//assert x+1 > x >= 2 && noPrimesIn(x,x+1) && (false ==> (p == x+1 && prime(x+1))); 
var next, isPrime := x+1, false; //Init
//assert next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> (p == next && prime(next))); //INV1
while !isPrime					//b1
    invariant next > x >= 2
    invariant noPrimesIn(x,next)          
	invariant isPrime ==> (p == next && prime(next))    //INV1   
	decreases *
	{ //P1
//	assert 2 <= 2 <= next && noDivU(next,2); 
	var d := 2;
//	assert 2 <= d <= next && noDivU(next,d);         //INV2
	while next % d != 0        //b2
		invariant 2 <= d <= next
		invariant noDivU(next,d)          //INV2
		//invariant next > x >= 2
        //invariant noPrimesIn(x,next)
		decreases next-d
		{ 
		//assert 2 <= d+1 <= next && noDivU(next,d+1);
		d := d+1; //P2
		//assert 2 <= d <= next && noDivU(next,d);
		}
    assert ((d == next) && next > x >= 2 && noPrimesIn(x,next) 
	         && ((d == next) ==> (next == next && prime(next)))) 
	        || (!(d == next) && next+1 > x >= 2 && noPrimesIn(x,next+1) 
	         && ((d == next) ==> (p == next+1 && prime(next+1)))) ;
	// wp(while b2 ..., post2) = INV2
	// post2 = wp(P3, Inv1)
	isPrime := (d == next); 
	assert (isPrime && next > x >= 2 && noPrimesIn(x,next) 
	         && (isPrime ==> (next == next && prime(next)))) 
	        || (!isPrime && next+1 > x >= 2 && noPrimesIn(x,next+1) 
	         && (isPrime ==> (p == next+1 && prime(next+1)))) ;
	//assert (isPrime && wp(p := next, alpha)) || (!isPrime && wp(next := next+1,alpha))
	//next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> (p == next && prime(next))); //alpha
	if isPrime { p := next; } else { next := next+1; } 
	assert next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> (p == next && prime(next)));
	} //fin P1
}


method VC_for_next_prime ()
{
//vc1 : pre ==> wp(Init,inv1)
assert forall x,p :: prime(x) 
       ==> x+1 > x >= 2 && noPrimesIn(x,x+1) && (false ==> (p == x+1 && prime(x+1)));
//vc2 : inv1 && b1 ==> wp(P1,inv1) // wp(P1,inv1) == wp(d:=2,inv2)
assert forall x, p, next, isPrime ::
       (next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> (p == next && prime(next))) 
       && !isPrime) ==> (2 <= 2 <= next && noDivU(next,2));
//vc3 : inv1 && ~b1 ==> post1
assert forall x, p, next, isPrime ::
       (next > x >= 2 && noPrimesIn(x,next) && (isPrime ==> (p == next && prime(next))) 
       && !!isPrime) ==> (p > x && prime(p) && noPrimesIn(x,p));
//vc4 :  inv2 && b2 ==> wp(P2,inv2)
assert forall d, next :: (2 <= d <= next && noDivU(next,d) && next % d != 0) 
       ==> (2 <= d+1 <= next && noDivU(next,d+1));
//vc5 : inv2 && ~b2 ==> post2 
//invariantes ocultos:  next > x >= 2 && noPrimesIn(x,next)
assert forall x, d, next, p:: 
       (2 <= d <= next && noDivU(next,d) && next > x >= 2 && noPrimesIn(x,next)
	   && !(next % d != 0)) 
	    ==>
       ((d == next) && next > x >= 2 && noPrimesIn(x,next) 
	       && ((d == next) ==> (next == next && prime(next)))) || 
		(!(d == next) && next+1 > x >= 2 && noPrimesIn(x,next+1) 
	         && ((d == next) ==> (p == next+1 && prime(next+1)))) ; 
}

//EJERCICIOS PARA CASA

method wp_prueba (y:int) returns (x:int)
//requires phi
//ensures x == y
{
// assert phi
x := y + 1;
if (y > 0) { 
           x := x + y;
		   }
else { 
      x := y + 100; 
	 }
x := x + y;
//assert  x == y;
}

// EN EL LABORATORIO 3 HAY ALGUNOS PROGRAMAS PARA LOS QUE PODEIS CALCULAR
// LAS VC, ALGUNOS YA LOS HEMOS HECHO AQUÍ.

// TAMBIÉN PODEIS PRACTICAR CON PROGRAMAS CREADOS POR VOSOTROS MISMOS 
// 0 QUE TENGAIS A MANO (POR EJEMPLO DE LA ASIG. METODOLOGÍA DE LA PROGRAMACIÓN)
// QUE UTILIZEN SOLO TIPOS BÁSICOS (ENTEROS, BOOLEANOS, CARÁCTERES)