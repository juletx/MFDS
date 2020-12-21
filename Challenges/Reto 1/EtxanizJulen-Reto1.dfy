//RETO: Demostrar el siguiente lemma (por contradicción):
lemma noExistsz_Lemma(x: int, y: int)
	requires x % 2 == 1 && y % 2 == 1
	ensures !exists z: int :: x*x + y*y == z*z
{
	if exists z: int :: x*x + y*y == z*z {
		var k: int :| x*x + y*y == k*k;
		assert x % 2 == 1 && y % 2 == 1;
		var a := (x-1)/2;
		// assert x == 2*a + 1;
		var b := (y-1)/2;
		// assert y == 2*b + 1;
		assert k*k == (2*a+1)*(2*a+1) + (2*b+1)*(2*b+1) == 
			4*a*a + 4*a + 1 + 4*b*b + 4*b + 1 == 
			2*(2*a*a + 2*a + 2*b*b + 2*b + 1);
		assert k*k % 2 == 0;
		Cuadr1_Lemma(k);
		assert k % 2 == 0;
		var c := k/2;
		// assert k == 2*c;
		assert (2*c)*(2*c) == 2*(2*a*a + 2*a + 2*b*b + 2*b + 1);
		assert 2*(2*c*c) == 2*(2*a*a + 2*a + 2*b*b + 2*b + 1);
		assert 2*c*c == 2*a*a + 2*a + 2*b*b + 2*b + 1;
		assert 2*(c*c) == 2*(a*a + a + b*b + b) + 1;
		assert false;
	}
}

// Prueba contrapositiva
lemma Cuadr1_Lemma(n: int)
	requires (n*n) % 2 == 0
	ensures n % 2 == 0
{
	if n % 2 != 0 {
		// assert n % 2 == 1;
		var k := (n-1)/2;
		// assert n == 2*k + 1;
		assert n*n == (2*k + 1)*(2*k + 1) == 4*k*k + 4*k + 1 == 2*(2*k*k + 2*k) + 1;
		// assert (n*n) % 2 != 0;
	}
}