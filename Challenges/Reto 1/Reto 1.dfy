//RETO: Demostrar el siguiente lemma (por contradicción):
lemma noExistsz_Lemma(x: int, y: int)
	requires x % 2 == 1 && y % 2 == 1
	ensures !exists z: int :: x*x + y*y == z*z
{
	if exists z: int :: x*x + y*y == z*z {
		var k: int :| x*x + y*y == k*k;
		if k % 2 == 0 {
			var a := k/2;
			//assert k == 2*a;
			assert x*x + y*y == 2*a*2*a == 2*(2*a*a);
			assert (x*x % 2 == 0 && y*y % 2 == 0) || (x*x % 2 == 1 && y*y % 2 == 1);
			IFF_Lemma(x);
			IFF_Lemma(y);
			assert (x % 2 == 0 && y % 2 == 0) || (x % 2 == 1 && y % 2 == 1);
			assume x % 2 == 0 || y % 2 == 0;
		}
		if k % 2 == 1 {
			IFF_Lemma(k);
			assert k*k % 2 == 1;
			// var a := (k-1)/2;
			// assert k == 2*a+1;
			// assert x*x + y*y == (2*a+1)*(2*a+1) == 4*a*a + 4*a + 1 == 2*(2*a*a + 2*a) + 1;
			assert (x*x % 2 == 0 && y*y % 2 == 1) || (x*x % 2 == 1 && y*y % 2 == 0);
			IFF_Lemma(x);
			IFF_Lemma(y);
			assert (x % 2 == 0 && y % 2 == 1) || (x % 2 == 1 && y % 2 == 0);
			assert x % 2 == 0 || y % 2 == 0;
		}
	}
}

lemma IFF_Lemma(n: int)
	ensures (n*n) % 2 == 0 <==> n % 2 == 0
{
	if (n*n) % 2 == 0 {
		Cuadr1_Lemma(n); //izq -> dcha
	}
	if n % 2 == 0 {
		Cuadr2_Lemma(n); //dcha -> izq
	}
}

// Prueba contrapositiva
lemma Cuadr1_Lemma(n: int)
	requires (n*n) % 2 == 0 //P
	ensures n % 2 == 0 // Q
{
	if n % 2 != 0 { // ¬Q
		// assert n % 2 == 1;
		var k := (n-1)/2;
		// assert n == 2*k + 1;
		assert n*n == (2*k + 1)*(2*k + 1) == 4*k*k + 4*k + 1 == 2*(2*k*k + 2*k) + 1;
		// assert (n*n) % 2 != 0; // ¬P
	}
}

// Prueba directa
lemma Cuadr2_Lemma(n: int)
	requires n % 2 == 0
	ensures (n*n) % 2 == 0
{
	var k := n/2;
	assert n*n == 4*k*k == 2*(2*k*k);
}