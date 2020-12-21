method MultipleReturns(x: int ,y: int ) returns (more: int , less: int)
	ensures more + less == 2*x
	ensures more - less == 2*y
{
	more := x + y;
	assert more == x + y;
	less := x - y;
	assert less == x - y;
}

method MultipleReturns2(x: int ,y: int ) returns (more: int, less: int)
	requires 0 < y
	ensures less < x < more
{
	more := x + y;
	assert more > x;
	less := x - y;
	assert x > less;
}

method MultipleReturns3(x: int ,y: int ) returns (more: int, less: int)
	requires 0 < y
	ensures less < x < more
{
	// assert forall a, b :: b > 0 ==> a - b < a < a + b;
	assert x - y < x < x + y;
	more := x + y;
	assert x - y < x < more;
	less := x - y;
	assert less < x < more;
}

// Example: A method computing absolute value
function abs(x: int): int
{
	if x < 0 then -x else x
}

method ComputeAbs(x: int) returns (y: int)
	ensures y == abs(x)
{
	if x < 0 { 
		return -x; 
	}
	else { 
		return x; 
	}
}

// Every even number greater than 2 is the sum of two primes.
// Even numbers, at least, until 4*10^18, have passed the test.
predicate isPrime(x: nat)
{
	x > 1 && forall y :: 1 < y < x ==> x % y != 0
}

predicate isEven(x: nat )
{
	x % 2 == 0
}

lemma Goldbach()
	ensures forall x :: (x > 2 && isEven (x)) ==> 
	exists y1: nat, y2: nat :: isPrime(y1) && isPrime(y2) && x == y1 + y2

// Example: A method for computing (in f) the factorial (of n)
function factorial(n: int ): int
	requires n >= 0
{
	if n == 0 then 1 else n * factorial(n -1)
}

method ComputeFact (n: int) returns (f: int)
requires n >= 0
ensures f == factorial (n)
{
	// assert 1 * factorial(n) == factorial(n);
	var x := n;
	// assert 1 * factorial(x) == factorial(n);
	f := 1;
	// assert f * factorial(x) == factorial(n);
	while x > 0
		// invariant 0 <= x <= n
		invariant f * factorial(x) == factorial(n);
		// decreases x; // In this case Dafny guesses it.
	{
		// assert f * x * factorial (x -1) == factorial (n);
		f := f * x;
		// assert f * factorial (x -1) == factorial (n);
		x := x - 1;
		// assert f * factorial(x) == factorial(n);
		// f, x := f * x, x - 1; // asignación simúltanea (equivalente)
	}
	// assert x <= 0 && 0 <= x <= n && f * factorial(x) == factorial(n);
	// assert x == 0 && f == factorial(n);
}

// Ejemplo
method compute_Fact2(n: int) returns (f: int)
	requires n >= 0
	ensures f == factorial(n)
{
	// assert 1 == factorial(0);
	var x := 0;
	// assert 1 == factorial(x);
	f := 1;
	// assert f == factorial(x);
	while x < n 
		invariant 0 <= x <= n
		invariant f == factorial(x);
	{
		// assert f * (x + 1) == factorial(x + 1);
		x := x + 1;
		// assert f * x == factorial(x);
		f := f * x;
		// assert f == factorial(x);
		// x, f := x + 1, f * x; // asignación simúltanea (no equivalente)
		// assert f * (x + 1) == factorial(x + 1);
		// x, f := x + 1, f * (x + 1); // asignación simúltanea (equivalente)
	}
	// assert 0 <= x <= n && f == factorial(x) && x >= n;
	// assert x == n && f == factorial(x);
	// assert f == factorial(n);
}

// Ejercicio: 1 + 3 + 5 + .... + 2*n - 1 == n*n

method Square (a: int) returns (x: int)
	requires a >= 1
	ensures x == a * a
{
	// assert 1 == 1*1;
	x := 1;
	// assert x == 1*1;
	var y := 1;
	// assert x == y*y;
	while y < a
		invariant 1 <= y <= a
		invariant x == y*y
	{
		// assert x == y * y;
		// assert x == y*y + 2*y + 1 - 2*y - 2 + 1;
		// assert x + 2*(y+1) - 1 == (y+1)*(y+1);
		y := y + 1;
		// assert x + 2*y - 1 == y * y;
		x := x + 2*y - 1;
		// assert x == y * y;
		// y, x := y+1, x + 2*y + 1;
		// assert x == y * y;
	}
	// assert 1 <= y <= a && x == y*y && y >= a;
	// assert y == a && x == y*y;
	// assert x == a * a;
}

method Square2 (a: int) returns (x: int)
	requires a >= 1
	ensures x == a * a
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
	assert y == a && x == sumSerie(y);
	assert x == sumSerie(a);
	sumSerie_Lemma(a);
	assert x == a * a;
}

function sumSerie (n: int): int
	requires n >= 1
{
	if n == 1 then 1 else sumSerie(n-1) + 2*n - 1
}

lemma sumSerie_Lemma(n: int)
	requires n >= 1
	ensures sumSerie(n) == n*n
{}

function power(b: int, e: nat): int
{
	if e == 0 then 1 else b* power(b, e-1)
}

method compute_power(b: int, e: nat) returns (p: int)
	ensures p == power(b, e)
{
	// assert 0 <= e <= e && power(b, e) == power(b, e);
	var t, x := e, b;
	// assert 0 <= t <= e && power(x, t) == power(b, e);
	p := 1;
	// assert 0 <= t <= e && p * power(x, t) == power(b, e);
	while t > 0
		invariant 0 <= t <= e
		invariant p * power(x, t) == power(b, e)
	{
		if t % 2 == 0 {
			even_Lemma(x, t);
			// assert 0 <= t/2 <= e && p * power(x*x, t/2) == power(b, e);
			x, t := x*x, t/2;
			// assert 0 <= t <= e && p * power(x, t) == power(b, e);
		}
		else {
			// assert 0 <= t-1 <= e && p*x * power(x, t-1) == power(b, e);
			p, t := p*x, t-1;
			// assert 0 <= t <= e && p * power(x, t) == power(b, e);
		}
	}
	// assert t <= 0 && 0 <= t <= e && p * power(x, t) == power(b, e);
	// assert t == 0 && p * power(x, t) == power(b, e);
	// assert p == power(b, e);
}

// Ejercicio: demostrarlo por inducción y poner la llamada que permite eliminar los assume de arriba.
lemma even_Lemma (b: int, e: nat)
	requires e % 2 == 0
	ensures power(b, e) == power(b*b, e/2)
{
	if e > 0 {
		even_Lemma(b, e-2);
		// assert power(b, e-2) == power(b*b, (e-2)/2) == power(b*b, (e/2-1);
		assert power(b, e) == b*b * power(b, e-2) == b*b * power(b*b, (e/2-1)) == power(b*b, e/2);
	}
}