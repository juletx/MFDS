// C: control
// I: input
// T0: valor inicial de T
// T: output
method Flip_Flop(C: bool, I: bool, T0: bool) returns (T: bool)
	ensures T == ((C && I) || (!C && T0))
{
	var X, Y, Z := false, false, true; // S1
	if C { // S2
		if I {
			X := true;
		}
		else {
			Y := true;
		}
	}
	if !X { // S3
		if !T0 {
			Z := false;
		}
	}
	if !Y { // S4
		if Z {
			T := true;
		}
		else {
			T := false;
		}	
	}
	else {
		T := false;
	}
	// Calcular la postcondición
	// Valores de X, Y, Z
	assert X == (C && I);
	assert Y == (C && !I);
	assert Z == !(!X && !T0) == X || T0;
	// Valor de T
	assert T == (!Y && Z);
	// Sustituir
	assert T == (!(C && !I) && ((C && I) || T0));
	// Simplificar
	assert T == ((!C || I) && ((C && I) || T0));
	// Simplificar
	assert T == ((C && I) || (!C && T0));
}

// C0: control 0
// I0: input 0
// C1: control 1
// I1: input 1
// T0: valor inicial de T
// T: output
method Flip_Flop_2(C0: bool, I0: bool, C1: bool, I1: bool, T0: bool) returns (T: bool)
	requires C0 // P
	// También podemos usar la precondición más débil
	// requires C0 || C1 || T0 == I0 // WP(S, Q)
	ensures (!C1 ==> T == I0) && (C1 ==> T == I1) // Q
{
	// S == Flip_Flop(C0, I0, T); Flip_Flop(C1, I1, T)
	// {P} S {Q}
	// {WP(S, Q)} S {Q}
	// La precondición implica la precondición más débil
	// P ==> WP(S, Q)
	assert C0 ==> C0 || C1 || T0 == I0;
	T := T0;
	assert C0 ==> C0 || C1 || T == I0;
	// Precondición más débil de S es más débil que P
	// WP(S, Q) == WP(Flip_Flop(C0, I0, T), WP(Flip_Flop(C1, I1, T), Q))
	// WP(S, Q) == WP(Flip_Flop(C0, I0, T), R)
	assert C0 || C1 || T == I0;
	// Simplificar hacia arriba
	assert C0 || C1 || (T && I0) || (!T && !I0);
	// Simplificar hacia arriba: (A && B) || (!A && B) == B
	assert C1 || (I0 && C0) || (I0 && T) || (!I0 && C0) || (!I0 && !T);
	// Simplificar hacia arriba: dividir ||
	assert C1 || (I0 && (C0 || T)) || (!I0 && (C0 || !T));
	// Simplificar hacia arriba: quitar expresiones redundantes
	assert C1 || (I0 && ((C0 && I0) || (!C0 && T))) 
		|| (!I0 && !((C0 && I0) || (!C0 && T)));
	// Sustituir hacia arriba el valor de T
	// T == ((C0 && I0) || (!C0 && T));
	T := Flip_Flop(C0, I0, T);
	// Precondición más débil del segundo Flip_Flop
	// R == WP(Flip_Flop(C1, I1, T), Q)
	assert C1 || (I0 && T) || (!I0 && !T);
	// Simplificar hacia arriba: (A && B) || (A && !B) == A
	assert (C1 && I1) 
		|| (C1 && !I1) 
		|| (!C1 && I0 && T)
		|| (!C1 && !I0 && !T);
	// Simplificar hacia arriba: quitar expresiones redundantes
	assert (C1 && I1 && ((C1 && I1) || (!C1 && T))) 
		|| (C1 && !I1 && !((C1 && I1) || (!C1 && T))) 
		|| (!C1 && I0 && ((C1 && I1) || (!C1 && T))) 
		|| (!C1 && !I0 && !((C1 && I1) || (!C1 && T)));
	// Sustituir hacia arriba el valor de T
	// T == ((C1 && I1) || (!C1 && T));
	T := Flip_Flop(C1, I1, T);
	assert (C1 && I1 && T) || (C1 && !I1 && !T) || 
		(!C1 && I0 && T) || (!C1 && !I0 && !T);
	// Simplificar hacia arriba: escribir todas las opciones para quitar ==
	assert (C1 || T == I0) && (!C1 || T == I1);
	// Simplificar hacia arriba: A ==> B == !A || B
	assert (!C1 ==> T == I0) && (C1 ==> T == I1); // Q
}