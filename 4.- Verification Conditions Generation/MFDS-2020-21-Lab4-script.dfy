// Ejercicio 1

method rootApprox (x:int)  returns (r:int)
	requires x >= 0
	ensures r*r <= x < (r+1)*(r+1) 
{
r := 0;  
while (r+1)*(r+1) <= x
	invariant r*r <= x
	{
	r := r+1;
	}
}

method VC_for_rootApprox ()
{
assert forall x :: x >= 0 ==> 0*0 <= x;
assert forall x,r :: ( r*r <= x  &&  (r+1)*(r+1) <= x ) ==> (r+1)*(r+1) <= x ;
assert forall x,r :: ( r*r <= x  &&  !((r+1)*(r+1) <= x) )==> r*r <= x < (r+1)*(r+1) ;
}

//Ejercicio 2: method VC_for_compute_Fact1

function factorial (n:int):int
requires n >= 0
{
if n == 0 then 1 else n*factorial(n-1)
}

method compute_Fact1 (n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
var x := n;
f := 1;
while x > 0
	invariant 0 <= x <= n
	invariant f * factorial(x) == factorial(n)
	//decreases x
	{
	f, x := f* x, x-1;
	}
}

method VC_for_compute_Fact1()
{}

// EJERCICIO PARA CASA: method VC_for_compute_Fact2
method compute_Fact2 (n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
var x := 0;
f := 1;
while x  < n
	invariant 0 <= x <= n
	invariant f == factorial(x)
	{
	x, f := x+1, f*(x+1);
	}
}

method VC_for_compute_Fact2()
{
// VC1: el invariante se cumple al entrar
// VC2: el invariante se conserva
// VC3: el invariante garantiza la post
}

// Ejercicio 3: method VC_for_computeSumPowers

function power2(e:nat):nat		
{
if e == 0 then 1 else 2*power2(e-1)
}

function sumPowers(n:nat):int
	requires n >= 1
{
if n == 1 then 1 else sumPowers(n-1) + power2(n-1)
}

method computeSumPowers(n:int) returns (r:int)  
	requires n >= 1
	ensures r == power2(n) - 1 
{
var k, p;
k, r, p:= 1, 1, 1;
while k < n
		invariant 1 <= k <= n
		invariant r == p * 2 - 1 == power2(k) - 1
		{
		p := 2 * p;
		r, k := r + p, k+1;
		}
}

method VC_for_computeSumPowers ()
{
// VC1: el invariante se cumple al entrar
// VC2: el invariante se conserva
// VC3: el invariante garantiza la post
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
u := sig_fact(r,u);
r := r+1;
}
}

method VC_for_computeFactTuring ()
{
// VC1: el invariante se cumple al entrar
// VC2: el invariante se conserva
// VC3: el invariante garantiza la post
}

method sig_fact(r:int,u:int) returns (v:int)
requires r >= 1 && u == factorial(r)
ensures v == factorial(r+1)
{
assert r >= 1 && u == factorial(r) &&  1 <= 1 <= r+1
       && u == 1 * factorial(r);
var s := 1;
v := u;
while s < r+1
   invariant r >= 1 && u == factorial(r) 
   invariant 1 <= s <= r+1
   invariant v == s * factorial(r)
   {
   s, v := s+1, v+u;
   }
}

method VC_for_sig_fact()
{
// VC1: el invariante se cumple al entrar
// VC2: el invariante se conserva
// VC3: el invariante garantiza la post
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
	ensures p > x && prime(p) && noPrimesIn(x,p)
	decreases *
{
var next, isPrime := x+1, false;
while !isPrime					
    invariant next > x >= 2
    invariant noPrimesIn(x,next)          
	invariant isPrime ==> (p == next && prime(next))       
	decreases *
	{
	var d := 2;
	while next % d != 0 
		invariant 2 <= d <= next
		invariant noDivU(next,d) 
		decreases next-d
		{ 
		d := d+1; 
		}
	isPrime := (d == next);
	if isPrime { p := next; } else { next := next+1; }
	}
}


method VC_for_next_prime ()
{
//vc1 : pre ==> inv1
//vc2 : inv1 && b1 ==> wp(P1,inv1)
//vc3 : inv1 && ~b1 ==> post1
//vc4 :  inv2 && b2 ==> wp(P2,inv2)
//vc5 : inv2 && ~b2 ==> post2
}
