method Flip_Flop(C: bool, I: bool, T0: bool) returns (T: bool)
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
	assert !Y ==> !T && Y ==> T || !T;
}

method Flip_Flop_2(C0: bool, I0: bool, C1: bool, I1: bool) returns (T: bool)
	requires C0
	ensures (!C1 ==> T == I0) || (C1 ==> T == I1)
{
	assert C0 || C1 || T == I1;
	T := Flip_Flop(C0, I0, T);
	assert I0 ==> !T && !I0 ==> !T;
	//assert (C1 || T || !I0) && (!T || C1 || I0);
	T := Flip_Flop(C1, I1, T);
	assert (!C1 ==> T == I0) || (C1 ==> T == I1);
}

method VC_Flip_Flop_2() {
	// P ==> WP(S, Q)
	// WP(S, Q) == WP(Flip_Flop(C0, I0, T), WP(Flip_Flop(C1, I1, T), Q))
	// R == WP(Flip_Flop(C1, I1, T), Q)
	// R == (C1 || T || !I0) && (!T || C1 || I0)
	assert forall C0, C1, T: bool, I1 :: C0 ==> C0 || C1 || T == I1;
}