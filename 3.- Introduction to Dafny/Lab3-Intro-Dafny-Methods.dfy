method MultipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
//ensures more + less == 2*x 
//ensures more - less == 2*y
ensures less < x < more

{
//assert forall a, b :: b > 0 ==> a - b < a < a + b;
assert x - y < x < x + y;
more := x + y;
//assert more == x+y;
//assert more > x;
assert x - y < x < more;
less := x - y;
//assert less == x-y;
//assert more == x+y;
//assert x > less;
assert less < x < more;
}

function factorial (n:int): int
requires n >= 0
{
if n == 0 then 1 else n * factorial(n-1)
}

method ComputeFact (n: int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
//assert 1 * factorial(n) == factorial(n);
var x := n;
//assert 1 * factorial(x) == factorial(n);
f := 1;
//assert f * factorial(x) == factorial(n);
while // Punto al que se asocia el invariante
      x > 0
  //invariant 0 <= x <= n
  invariant f * factorial(x) == factorial(n)
// decreases x; // In this case Dafny guesses it.
{
assert f * (x * factorial (x-1)) == factorial (n);
f, x := f * x, x-1;
assert f * factorial(x) == factorial(n);
}
//assert x <= 0 && 0 <= x <=n && f * factorial(x) == factorial(n);
//assert x == 0 && f == factorial(n);
}

method compute_Fact2 (n:int) returns (f:int)
requires n >= 0
ensures f == factorial(n)
{
//assert 1 == factorial(0);
var x := 0;
//assert 1 == factorial(x);
f := 1;
assert f == factorial(x);
while // El invariante se asocia a este punto del cómputo
         x < n 
		 invariant 0 <= x <= n 
		 invariant f == factorial(x)
{
//x := x + 1; // Ejercicio: Hacer las aserciones con las dos asign. secuenciales
//f := f * x;
//assert  f * (x+1) == factorial(x+1);
x, f := x + 1, f * (x+1);
//assert f == factorial(x);
}
//assert 0 <= x <= n && f == factorial(x) && x >= n;
//assert x == n && f == factorial(x);
//assert f == factorial(n);
}

// n>=1 ==> 1 + 3 + 5 + ... + (2*n -1) == n*n
//  1 + 3 + 5 + ... + (2*n -1) + (2*(n+1)-1)== (n+1)*(n+1)

method Square (a:int) returns (x:int)
requires a >= 1
ensures x == a*a
{
x := 1;
var y := 1;
while y < a
     invariant 1 <= y <= a
	 invariant x == y*y

	{
	//assert y*y + 2*(y+1) - 1 == (y+1)*(y+1);
	//assert x + 2*(y+1) - 1 == (y+1)*(y+1);
	//y := y + 1;
	//assert x + 2*y - 1 == y*y;
	//x := x + 2*y - 1;
	//assert x == y*y;
	assert x + 2*y + 1 == (y+1)*(y+1);
	y, x := y + 1, x + 2*y + 1; 
	assert x == y*y;
	}
}

function sumSerie(n:int):int
requires n >= 1
{
if n == 1 then 1 else sumSerie(n-1) + 2*n - 1
}

method Square2 (a:int) returns (x:int)
requires a >= 1
ensures x == a*a
{
x := 1;
var y := 1;
while y < a
     invariant 1 <= y <= a
	 invariant x == sumSerie(y)

	{
	y := y + 1;
	x := x + 2*y - 1;
	}
assert 1 <= y <= a && x == sumSerie(y) && y >= a;
assert x == sumSerie(a) ; // Puede probar según el invariante
sumSerieProp_Lemma(a);
assert x == a*a; // No lo prueba automáticamente
}

lemma sumSerieProp_Lemma (n:int)
requires n >= 1
ensures sumSerie(n) == n*n
{}

function power(b:int, e:nat):int
{
if e == 0 then 1 else b * power(b,e-1)
}

method compute_power (b:int, e:nat) returns (p:int)
ensures p == power(b,e)
{
var t , x := e, b;
p := 1;
while t > 0
     invariant  0 <= t <= e
	 invariant p * power(x,t) == power(b,e)  
    {
	if t % 2 == 0 {
	              assume p * power(x*x,t/2) == power(b,e);
	              x, t := x*x, t/2;
				  assume p * power(x,t) == power(b,e);
	              }
	else {
	      p, t := p*x, t-1;
		  //assume p * power(x,t) == power(b,e);
	      }
	}
}

lemma even_Lemma (b:int, e:nat)
requires e%2 == 0
ensures power(b,e) == power(b*b,e/2)
// Ejercicio: demostrarlo por inducción y poner la llamada que permite eliminar los assume de arriba.
