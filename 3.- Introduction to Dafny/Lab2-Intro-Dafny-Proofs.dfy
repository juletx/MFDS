function method fact (n:nat):nat
{
if n == 0 then 1 else n*fact(n-1)
}

predicate method even (n:nat)
{
n % 2 == 0
}

method llamar_a_fact (n:nat) returns ()
{
var y := fact(5);
assert y == 120;

assert forall n :: n>=5 ==> fact(n) >= 120;
if even(n) { y := fact(n); } else { y := fact(n-1); }
}

// Example of direct proof
lemma factPlus3_Lemma(n:nat)
ensures fact(n+3) == (n+3)*(n+2)*(n+1)*fact(n)
{
assert fact(n+3) == (n+3)*fact(n+2) == (n+3)*(n+2)*fact(n+1) == (n+3)*(n+2)*(n+1)*fact(n);
}

lemma Odd_Sum_Lemma (a:nat, b:nat)
requires a == b+1
ensures (a+b)%2 == 1
// Ejercicio: Prueba directa y contrapositiva/contradicción
{
//Direct Proof
// assert (a+b)%2 == ((b+1)+b)%2 == (2*b+1)%2 == 1; //DP-1
/*calc {
     (a+b)%2;
	 ((b+1)+b)%2;
	 (2*b+1)%2;
	 1;   
}*/     //DP-2

calc  {
          (a+b)%2 == 1;
	 <==> ((b+1)+b)%2 == 1;
	 <== (2*b+1)%2 == 1;   
}

/*
if  (a+b)%2 != 1  
    {
    calc ==> {
	          (a+b)%2 == 0;
			  b != a+1;        //¬P //contrapositiva
			  false;           // Contradiccción o reducción al absurdo
	}
    }
*/
}

//Direct Proof by cases

predicate div2 (n:int)
{
n%2 == 0
}

lemma CuadEven_Lemma (x:int)
ensures div2(3*x*x + x + 14)
{
if div2(x) {
             var k := x/2;
			 //assert x == 2*k;
			 assert 3*x*x + x + 14 == 2*(6*k*k + k + 7); 
			     //Ejercicio poner las expr. intermedias
            }
else {
      var k := (x-1)/2;
      //assert x == 2*k+1;
	  assert 3*x*x + x + 14 == 2*(6*k*k + 7*k + 9);
	  //Ejercicio poner las expr. intermedias
      }
}

predicate div3 (n:int)
{
n%3 == 0
}

/*
lemma notDiv3_Lemma (x:int)
ensures !div3(2*x*x + x + 1)
{
if div3(x) {
             var k := x/3;
			 //assert x == 3*k;
            }
else if x%3 == 1 {
                 var k := (x-1)/3;
				 //assert x == 3*k+1;
                 }
else {
     //assert x%3 == 2;
      }
}
Ejercicio completar la demostración usando calc con todos los detalles.
*/

function exp (x:int, e:nat):int
{
if e == 0 then 1 else x * exp(x,e-1)
}

// Prueba inducción + Contradicción
lemma indContr_Lemma (n:int)
requires n >= 3
ensures exp(n+1,n) < exp(n,n+1)
{
if n == 3 {
           assert exp(4,3) < exp(3,4);
           }
else {
     if exp(n+1,n) >= exp(n,n+1) {
	 calc {
	       exp(n+1,n) >= exp(n,n+1);
		   ==> {
		       indContr_Lemma(n-1);
			   //assert exp(n,n-1) < exp(n-1,n); //HI
			   //assert exp(n-1,n) > exp(n,n-1); //HI
			   assert forall a,b,c,d :: (a >= b >= 1 && c > d >= 1) ==> a*c > b *d;
			   //assume forall x, e :: exp(x,e) >= 1;
			   forall x:int, e:nat | x>=1 { expGT1_Lemma(x,e); }
		       }
		   exp(n+1,n) * exp(n-1,n) > exp(n,n+1) * exp(n,n-1);
		   ==> {
		        assert forall b, e1:nat, e2:nat :: exp(b,e1)* exp(b,e2) == exp(b,e1+e2);
				//assume forall b1, b2, e:nat :: exp(b1,e)*exp(b2,e) == exp(b1*b2,e);
				igBase_lemma(n+1, n-1, n);
		       }
			exp((n+1)*(n-1), n) > exp(n,2*n);
			==> {
			    //assume exp(n,2*n) == exp(n*n,n);
				assert forall x,e:nat :: exp(x,2*e) == exp(x*x,e); //Lema local
				//Ejercicio: forall x,e1:nat,e2:nat:: exp(x,e1*e2) == exp(exp(x,e1),e2); 
			    }
			exp(n*n-1, n) > exp(n*n,n);
			==> {
			    //assume forall b1,b2,e:nat :: 1 <= b1 < b2 ==> exp(b1,e) <= exp(b2,e);
				expMon_Lemma(n*n-1, n*n, n);
			    }
			false;
	 }
	 }
     }
}

// Lemmas auxiliares del anterior
lemma expGT1_Lemma (x:int, e:nat)
requires x >= 1
ensures exp(x,e) >= 1
// Ejercicio por inducción en e

lemma igBase_lemma (b1:int, b2:int, e:nat)
ensures exp(b1,e)*exp(b2,e) == exp(b1*b2,e)
{}

lemma expMon_Lemma (b1:int,b2:int,e:nat)
requires 1 <= b1 < b2 
ensures exp(b1,e) <= exp(b2,e);
// Ejercicio por inducción en e
///////////////////////////////////////////////

lemma RA_Lemma (n:nat)
requires (1+exp(-1,n))/2 != 0
ensures n%2 == 0
{
if n%2 != 0 {
             assert n%2 == 1;
			 var k := (n-1)/2;
			 assert n == 2*k+1;
			 assume forall k:nat :: exp(-1,2*k+1) == -1;
			 //Ejercicio: Quitar este assume y sustituirlo por una llamada al lemma expodd_Lemma
			 assert 1+exp(-1,2*k+1) == 1 + (-1) == 0;
			//assert false;
            }
}

lemma expodd_Lemma (k:nat)
ensures exp(-1,2*k+1) == -1
// Ejercicio por inducción en k

// Prueba de existencial por casos
lemma nodiv3_Lemma (x:int)
requires x%3 != 0
ensures exists k:int :: x*x == 3*k + 1;
{
if x%3 == 1 {
              var y := (x-1)/3;
			  //assert x == 3*y + 1;
			  assert x*x 
			         //== (3*y + 1)*(3*y + 1) 
					 //== 9*y*y + 6*y + 1 
					 == 3*(3*y*y + 2*y) + 1; //Pista: k == 3*y*y + 2*y
}
else {
     //assert x%3 == 2;
	 var y := (x-2)/3;
	 // assert x == 3*y + 2;
	 assert x*x == 3*(3*y*y+4*y+1) + 1; //Pista: k == 3*y*y+4*y+1
}
}

function abs(x:real):real
{
if x >= 0.0 then x else -x 
}

// Prueba directa por casos
lemma cases_Lemma (x:real)
ensures -5.0 <= abs(x+2.0) - abs(x-3.0) <= 5.0
{
if x <= -2.0 {
             assert abs(x+2.0) - abs(x-3.0) == -(x+2.0)-(-(x-3.0)) == -2.0-3.0 == -5.0;
             }
else if -2.0 < x < 3.0 {
                        assert abs(x+2.0) - abs(x-3.0) == x+2.0-(-(x-3.0)) == 2.0*x-1.0;
						assert -5.0 <= 2.0*x-1.0 <= 5.0;
                        }
else {
     //assert x >= -3.0;
	 assert abs(x+2.0) - abs(x-3.0) == x+2.0 -(x-3.0) == 5.0;
     }
}

// Ejemplo inducción doble

function s (n:nat):int
requires n >= 1
{
if n == 1 then 5 else if n == 2 then 13 else 5*s(n-1) - 6*s(n-2)
}

lemma {:induction false} serie_Lemma (n:nat)
requires n >= 1
ensures s(n) == exp(2,n) + exp(3,n)
{
if n > 2 {
           calc {
		         s(n);
				 5*s(n-1) - 6*s(n-2);
				 {
				 serie_Lemma(n-1);
				 //assert s(n-1) == exp(2,n-1) + exp(3,n-1); //HI1
				 serie_Lemma(n-2);
				 //assert s(n-2) == exp(2,n-2) + exp(3,n-2); //HI2
				 }
				 5*(exp(2,n-1) + exp(3,n-1)) - (6*(exp(2,n-2) + exp(3,n-2)));
				 5*exp(2,n-1) + 5*exp(3,n-1) - 6*exp(2,n-2) - 6* exp(3,n-2);
				 10*exp(2,n-2) + 15*exp(3,n-2) - 6*exp(2,n-2) - 6* exp(3,n-2);
				 4*exp(2,n-2) + 9*exp(3,n-2);
				 exp(2,n) + exp(3,n);
		         }
}
}

// Probar IFF

lemma IFF_Lemma (n:int)
ensures (n*n)%2 == 0 <==> n%2 == 0
{
if (n*n)%2 == 0 { Cuadr1_Lemma(n); } // izq -> dcha
if n%2 == 0  { Cuadr2_Lemma(n); }    // dcha -> izda
}

//Prueba Contrapositiva
lemma Cuadr1_Lemma (n:int)
requires (n*n)%2 == 0  //P
ensures n%2 == 0       //Q
{
if n%2 != 0 //¬Q
	{
	var k := (n-1)/2;
	//assert n == 2*k + 1;
	assert n*n == (2*k + 1)*(2*k + 1) 
			   == 4*k*k + 4*k + 1
			   == 2*(2*k*k + 2*k) + 1;
	//assert (n*n)%2 != 0;  //¬P
	}
}

// Prueba directa
lemma Cuadr2_Lemma (n:int)
requires n%2 == 0 
ensures (n*n)%2 == 0  
{
var k := n/2;
assert n*n == 4*k*k == 2*(2*k*k);
}

// Ejemplo de prueba de un no-existencial (expr. let-such-that)

lemma noExistsk_Lemma (x:int)
ensures !exists k:int :: 4*k + 3 == x*x
{ // Prueba por contradicción
if exists k:int :: 4*k + 3 == x*x 
 {
   var z:int :| 4*z + 3 == x*x;
   assert x*x == 2*(2*z+1) + 1;
   //assert (x*x)%2 != 0;
   IFF_Lemma(x);
   //assert x%2 != 0;
   assert x%2 == 1;
   var a := (x-1)/2;
   assert 4*z + 3 == (2*a + 1)*(2*a + 1) == 4*a*a + 4*a + 1;
   assert 2 == 3 - 1 == 4*a*a + 4*a - 4*z;
   assert 1 == 2*a*a + 2*a - 2*z == 2*(a*a + a - z);
   //assert false;
  }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////
//RETO: Demostrar el siguiente lemma (por contradicción):
lemma noExistsz_Lemma (x:int,y:int)
requires x%2 == 1 && y%2 == 1
ensures !exists z:int :: x*x + y*y == z*z
//Si lo consigues, envíame un fichero .dfy con el lema probado y las definiciones y lemas auxiliares
//estrictamente necesarias.
//////////////////////////////////////////////////////////////////////////////////////////////////////////

//Ejemplo: código como prueba, el código calcula los valores que la postcondición dice que existen.

function MultAdd(a:nat, b:nat, c:nat):nat //Función auxiliar que permite generar triggers para r.
{                                         //(abstrae la operación suma que no está permitida en los triggers)
a*b + c
}

lemma DivModExists_Lemma (x:nat, y:nat)
requires y != 0
ensures exists q:nat, r:nat :: x == MultAdd(y,q,r) && r < y
{
/*var q:nat, r:nat := 0, x;
while r >= y 
         invariant x == MultAdd(y,q,r)
		{
		q := q + 1;
		r := r - y;
		}
//assert x == y*q + r && r < y;*/

// Los valores que se computan pueden tener nombre diferente a los del exists,
// de hecho los testigos del exists podrían ser expresiones en función de las variables computadas.

var coc:nat, res:nat := 0, x;
while res >= y 
         invariant x == MultAdd(y,coc,res)
		{
		coc := coc + 1;
		res := res - y;
		}
//assert x == y*coc + res && res < y;
}
//PENDIENTE: Demostrar que q y r son únicos.