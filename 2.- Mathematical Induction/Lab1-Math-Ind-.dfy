function exp (x:int, e:int): int
requires e >= 0
decreases e
{
if e == 0 then 1 else x * exp(x,e-1)
}

lemma {:induction false} Ind1_Lemma (n: int)
	requires n >= 1
	ensures (exp(3,n) - 1) % 2 == 0
{
/*
if n == 1 {
            //assert (exp(3,1)-1)%2 == 0;
            }
else {
       Ind1_Lemma(n-1);
	   //assert (exp(3,n-1) - 1) % 2 == 0; // HI
       assert exp(3,n) - 1 == 3*exp(3,n-1) -1 == 2*exp(3,n-1) + exp(3,n-1) - 1;
      }
*/
if n > 1 {
       Ind1_Lemma(n-1);
	   //assert (exp(3,n-1) - 1) % 2 == 0; // HI
       //assert exp(3,n) - 1 == 3*exp(3,n-1) -1 == 2*exp(3,n-1) + exp(3,n-1) - 1;
      }
}

lemma {:induction false} Ind2_Lemma ()
ensures forall n :: n >= 1 ==> (exp(3,n) - 1)%2 == 0
{
forall n | n>=1 { Ind1_Lemma(n); }
}

lemma {:induction false} cuatroN_Lemma (n:int)
	requires n>=6
	ensures 4*n < (n*n) - 7
{
/*
if n == 6 {
          assert 4*6 < (6*6) -7;
          }
else{
     cuatroN_Lemma(n-1);
	 //assert 4*(n-1) < (n-1)*(n-1) - 7; //HI
	 assert 4*n < (n*n - 7) + (5 - 2*n);
	 assert 2*n >= 5;
    }
*/
//if n > 6 { cuatroN_Lemma(n-1); }
assert (n*n) - 7 >= (6*n) -7 == 6*(n-1) -1 >= 5*n -1 > 4*n;
}

lemma mod8_Lemma (n:int)
requires n >= 1
ensures (exp(3,2*n) - 1)%8 == 0
{
/*
if n==1 {
          //assert exp(3,2*1) - 1 == 8;
         }
else{
      //assert n > 1;
      mod8_Lemma(n-1);
	  //assert (exp(3,2*(n-1)) - 1)%8 == (exp(3,2*n-2) - 1)%8  == 0;
	  //assert exp(3,2*n) - 1 == 3 * exp(3, 2*n-1) - 1== 9*exp(3,2*n-2) -1
	  //       == 8*exp(3,2*n-2) + exp(3,2*n-2) - 1;
}
*/
if n > 1 { mod8_Lemma(n-1); }
}

lemma mod8Forall_Lemma ()
ensures forall n :: n >= 1 ==> (exp(3,2*n) - 1)%8 == 0
{
forall n | n >= 1 { mod8_Lemma(n); }
}

function sumOdds (n:int):int
requires n >= 1
{
if n == 1 then 1 else sumOdds(n-1) + 2*n - 1
}

lemma {:induction false} sumOdds_Lemma (n:int)
requires n >= 1
ensures sumOdds(n) == n*n
{
if n == 1 { assert sumOdds(1) == 1; }
else {
      sumOdds_Lemma(n-1);
	  //assert sumOdds(n-1) == (n-1) * (n-1); //HI
	  assert sumOdds(n) == sumOdds(n-1)+ 2*n - 1 == ((n-1) * (n-1)) + 2*n -1 ==
	          (n*n - 2*n + 1) + 2*n -1 == n*n;
      }
}

function fact (n:int):int
requires n >= 0
//ensures fact(n) >= 1 //Se cargaría como parte de la definición en cada llamada a fact(?)
{
if n == 0 then 1 else n * fact(n-1)
}

//
lemma factExp_Lemma (n:int)
requires n >= 1
ensures fact(n) <= exp(n,n)
{
if n > 1 {
           factExp_Lemma(n-1); 
		   //assert fact(n-1) <= exp(n-1,n-1); //HI
		   aux_Lemma(n-1,n,n-1);
		   assert fact(n) == n*fact(n-1) <= n*exp(n-1,n-1) <= n*exp(n,n-1) == exp(n,n);
}
}

lemma aux_Lemma (x:int, y:int, e:int)
requires e >= 0
requires 1 <= x <= y
ensures exp(x,e) <= exp(y,e)
{
if e > 0 {
           aux_Lemma(x,y,e-1);
		   //assert exp(x,e-1) <= exp(y,e-1); //HI
		   assert forall x,e :: (x >= 1 && e >= 0) ==> exp(x,e) >= 1; //Lema local
		   //Ejercicio: Probar el lema local como un lema con parámetros x, e
		   // poniendo {:induction false} y haciendo todos los detalles.
		   assert exp(x,e) == x*exp(x,e-1) <= x*exp(y,e-1) <= y*exp(y,e-1) == exp(y,e);
}
}
function sumD (x:int):int
requires x >= 0
{
if x <= 9 then x else x%10 + sumD(x/10)
}

lemma sumDigMult11_Lemma (x:int)
requires x >= 11 && x%11 == 0
ensures sumD(x) % 2 == 0
// Este lema es falso
// Contraejemplo: 11.19 = 209 y sumD(209) = 11 y 11%2 != 0
{
if x > 11 {
           var n := x/11;
		   //assert 11*(n-1) >= 11;
		   sumDigMult11_Lemma(11*(n-1));
		   //assert sumD(11*(n-1)) % 2 == 0; //HI
		   //assert forall x, y :: (x >= 0 && y >= 0) ==> sumD(x+y) == sumD(x) + sumD(y);
		   // Lemma local no se prueba (en este caso, porque es falso)
		   sumDDist_Lemma(11*(n-1),11); 
		   assert sumD(x) == sumD(11*n) == sumD(11*(n-1) + 11)
		          == sumD(11*(n-1)) + sumD(11) == sumD(11*(n-1)) + 2;
}
}

predicate even (x:int)
{
x >= 0 && x % 2 == 0
}

lemma sumDigMult11'_Lemma (n:int)
requires n >= 1
ensures even(sumD(11*n))
{
if n > 1 {
           sumDigMult11'_Lemma(n-1); 
		   //assert 11*(n-1) >= 0;
		   //assert even(sumD(11*(n-1))); H.I.
		   sumDDist_Lemma(11*(n-1), 11);
		    assert sumD(11*n) == sumD(11*(n-1) + 11)
		          == sumD(11*(n-1)) + sumD(11) == sumD(11*(n-1)) + 2;
}
}


lemma sumDDist_Lemma (x:int, y:int)
requires x >= 0 && y >= 0
ensures sumD(x+y) == sumD(x) + sumD(y)
// Eete lema es falso.
// Contraejemplo: sumD(11*18+11) = 11 != 20 = 18 + 2 = sumD(11*18) + sumD(11)


lemma fact_Lemma (n:int)
requires n >= 7
ensures exp(3,n) < fact(n)
{
if n == 7 {
           // assert exp(3,7) < fact(7);
            }
else {
      fact_Lemma(n-1);
	  //assert exp(3,n-1) < fact(n-1); //HI
	  assert forall n :: n>=0 ==> fact(n) >= 1; //Lema local
	  assert forall x:int,y:int,z:int :: (1 <= x < y && z >= 1) ==> x*z < y*z; //Lema local
	  // (1 <= 3 < n && fact(n-1) >= 1) ==> 3*fact(n-1) < n * fact(n-1)
	  //prod_Lemma(3,n,fact(n-1));                // Llamada al lemma
	  assert exp(3,n) 
	         == 3*exp(3,n-1) // Def. exp
			 < 3* fact(n-1) // HI
			 < n * fact(n-1) // Lemmas auxiliares
			 == fact(n);    // Def. fact
      }
}

lemma prod_Lemma (x:int, y:int, z:int)
requires 1 <= x < y && z >= 1
ensures x*z < y*z
{}

function Fib(n:nat):nat
{
if n < 2 then n else Fib(n-2) + Fib(n-1)
}

lemma {:induction false} FibGET5_Lemma (n:nat)
requires n >= 5
ensures Fib(n) >= n
{
if n > 5 {
           FibGET5_Lemma(n-1);
		   //assert Fib(n-1) >= n-1; //HI
		   assert Fib(n) 
		          == Fib(n-1) + Fib(n-2) //Def. Fib
				  >= n-1 + Fib(n-2) // HI
				  >= n;             // pq Fib(n-2) >= 1 para todo n>5
}
}

lemma Cuadrado_y_Mitad_Lemma (b:int,e:nat)
requires e > 0 && e % 2 == 0
ensures  exp(b*b,e/2) == exp(b,e);
{
if e == 2 {
          assert exp(b,2) == exp(b*b,1);
          }
else {
      assert exp(b*b,e/2) == b*b*exp(b*b,(e/2)-1) //Def. exp
	                      //== b*b*b*b*exp(b*b,(e/2)-2) //Def. exp //No hace falta
						  == b*b*exp(b*b,(e-2)/2);
     Cuadrado_y_Mitad_Lemma(b,e-2);
	 //assert exp(b*b,(e-2)/2) == exp(b,e-2); //HI
	 //assert b*b*exp(b*b,(e-2)/2) ==  b*b* exp(b,e-2) == exp(b,e);
}
}

lemma fact2n_Lemma (n:int)
requires n >= 1
ensures fact(2*n) < exp(2,2*n)*fact(n)*fact(n)
{
if n > 1 {
      calc{ fact(2*n);
	        == 2*n*(2*n-1)*fact(2*n-2);
			== 4*n*n*fact(2*n-2) - 2*n*fact(2*n-2);
			< { 
			  fact2n_Lemma(n-1);
			  //assert fact(2*(n-1)) < exp(2,2*(n-1))*fact(n-1)*fact(n-1); //H.I.
			  assert fact(2*n-2) < exp(2,2*n-2)*fact(n-1)*fact(n-1); 
			  }
			4*n*n*exp(2,2*n-2)*fact(n-1)*fact(n-1) - 2*n*fact(2*n-2);
			== exp(2,2*n)*fact(n)*fact(n) - 2*n*fact(2*n-2);
			< {
			  //assume forall n :: n>1 ==> 2*n*fact(2*n-2) >= 1; //Ejercicio
			  assert forall n:nat :: fact(n) >= 1; //Lemma local
			  }
			exp(2,2*n)*fact(n)*fact(n);
		   }
}
}

function ack (m:nat, n:nat):nat
{
if m == 0 then n+1
else if n == 0 then ack(m-1,1)
else ack(m-1,ack(m,n-1))
}

lemma ack3n_Lemma (n:nat)
ensures ack(3,n) == 8*exp(2,n) - 3
{
if n == 0 { /*
            assert ack(1,1) == 3; //Ejercicio de comprobación
			assert ack(1,2) == 4; //Ejercicio de comprobación
            assert ack(3,0) == ack(2,1) == ack(1,ack(2,0)) 
			                            == ack(1,ack(1,1)) 
										== ack(1,3) 
										== ack(0,ack(1,2)) 
										== ack(0,4) 
										== 5
										== 8*exp(2,0) - 3;
           */}
else {
       //ack3n_Lemma(n-1);
	   //assert ack(3,n-1) == 8*exp(2,n-1) - 3 //HI
	   calc {    ack(3,n);
	          == ack(2,ack(3,n-1)); // Def. ack.
			  == {
			     ack2n_Lemma(ack(3,n-1));
				 }
			     2*ack(3,n-1) + 3;
			  == {
			     ack3n_Lemma(n-1);
				 }
	             2*(8*exp(2,n-1) - 3) + 3;
			  == 8*2*exp(2,n-1) - 6 + 3;
			  == 8*exp(2,n) - 3;
	   }             
}
}

lemma ack2n_Lemma (n:nat)
ensures ack(2,n) == 2*n + 3
//Ejercicio: Demostrar este lemma usando el lema ack1n_Lemma

lemma ack1n_Lemma (n:nat) 
ensures ack(1,n) == n+2
{}
//Ejercicio poniéndole {:induction false}