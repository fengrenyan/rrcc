
:- module(supp, [supp/3]).

%Supp: eliminat the atoms which will be forgten from the result of kforget.
%Supp(P,C∨KD1∨…∨KDn∨BE1∨….∨BEr )=C∨K(Supp(P,D1))∨…∨K(Supp(P,Dn))∨B(Supp(P,E1))∨…∨B(Supp(P,Er))
%Supp(P,Ei )={Supp(P,X)|X∈Ei}

supp([], _, []) :- !.
supp(A, [], A) :- !.
supp([X|L], LP, L1) :- supp_one(X, LP, NewC, Flag), 
	Flag == true, supp(L, LP, L1).
supp([X|L], LP, [NewC|L1]) :- supp_one(X, LP, NewC, Flag), 
	Flag == false, supp(L, LP, L1).



supp_one(X, [], X, false) :- !.
supp_one(X, [P|LP], Y, Flag) :- supp_oneA(X, P, NewC, Flag1), 
	(Flag1 == true, (Flag = true, Y = NewC); supp_one(NewC, LP, Y, Flag)), !.

supp_oneA(C, P, _, true) :- C = kclause(Cclause, KT, BT), 
	(member(P, Cclause); member(-P, Cclause)), !.
supp_oneA(C, P, NewC, Flag) :- C = kclause(Cclause, KT, BT), 
	suppKT(KT, P, NewKT, Flag1), suppBT(BT, P, NewBT, Flag2),
	NewC = kclause(Cclause, NewKT, NewBT),
	((Flag1 = false, Flag2 = false), Flag = false; Flag = true), !.

suppKT([], _, [], Flag) :- Flag = false, !.
suppKT(KT, P, KT, Flag) :- \+ findPTerm(KT, P, X), \+ findPTerm(KT, -P, Y), Flag = false.
suppKT(KT, P, [], Flag) :- (findPTerm(KT, P, X); findPTerm(KT, -P, Y)), Flag = true.


suppBT([], _, [], Flag) :- Flag = false, !.
suppBT(BT, P, BT, Flag) :- \+ findPTerm(BT, P, X), \+ findPTerm(BT, -P, Y), Flag = false.
suppBT(BT, P, NewBT, Flag) :- findPTerm(BT, P, X), delete_X(X, P, F1), 
	(F1 = [], (Flag = true, NewBT = []); 
	delete(BT, X, NewBT1), append([F1], NewBT1, NewBT2), suppBT(NewBT2, P, NewBT, Flag)).
suppBT(BT, P, NewBT, Flag) :- findPTerm(BT, -P, X), delete_X(X, -P, F1), 
	(F1 = [], (Flag = true, NewBT = []); 
	delete(BT, X, NewBT1), append([F1], NewBT1, NewBT2), suppBT(NewBT2, P, NewBT, Flag)).


delete_X([], _, []) :- !.
delete_X([X|L1], P, L) :- (member(P, X); member(-P, X)), delete_X(L1, P, L).
delete_X([X|L1], P, [X|L2]) :- \+ member(P, X), \+ member(-P, X), delete_X(L1, P, L2).

%----------------------------end----add------------------------