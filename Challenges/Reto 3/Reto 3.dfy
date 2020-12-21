predicate IsSubsequence(s1: seq<int>, s2:seq<int>)
{
	|s1| >= |s2| && forall i :: i in s2 ==> i in s1
}

predicate IsUpsequence(s: seq<int>)
{
	forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

method Longest_Upsequence(A: seq<int>) returns (l: int)
	requires |A| >= 1
	// ensures exists s :: |s| == l && IsSubsequence(A, s) && IsUpsequence(s)
	// ensures !exists s :: |s| > l && IsSubsequence(A, s) && IsUpsequence(s)
{
	var n, k, N := 1, 1, |A|;
	var i, j := 1, 1;
	var h;
	var a := new int[N+1];
	var m: seq<int> := a[..];
	m := m[1 := A[0]];
	while n < N
		// P1
		invariant 1 <= n <= N
		// invariant exists s :: |s| == k && IsSubsequence(A[..n], s) && IsUpsequence(s)
		// invariant !exists s :: |s| > k && IsSubsequence(A[..n], s) && IsUpsequence(s)
		// P2
		// invariant forall j :: 1 <= j <= k ==> 
		// (exists s :: |s| == j && s[j-1] == m[j] && IsSubsequence(A[..n], s) && IsUpsequence(s)) && 
		// (!exists s :: |s| == j && s[j-1] < m[j] && IsSubsequence(A[..n], s) && IsUpsequence(s))
	{
		//assume k < |m| - 1;
		if m[k] <= A[n] {
			k := k + 1;
			m := m[k := A[n]];
		}
		if A[n] < m[1] {
			m := m[1 := A[n]];
		}
		if m[1] <= A[n] < m[k] {
			assert m[1] <= A[n] < m[k];
			i := 1; j := k;
			while i < j - 1
				invariant 1 <= i < j <= k
				invariant m[i] <= A[n] < m[j]
			{
				h := (i + j) / 2;
				assert i < h < j;
				if m[h] <= A[n] {
					i := h;
				}
				if A[n] < m[h] {
					j := h;
				}
			}
			assert m[j-1] <= A[n] < m[j];
			m := m[j := A[n]];
		}
		n := n + 1;
	}
	l := k;
}