
:- module(resolution,  [resolution/4, resolutionKB_circle/4, resolutionKK_circle/4, resolutionK/4, resolutionB/3, resolutionKBF/2]).

/*:- module(resolution,  [resolution/4]).
%:- module(resolution,  [resolutionKB/4]).
:- module(resolution,  [resolutionKB_circle/4]).
:- module(resolution,  [resolutionKK_circle/4]).
:- module(resolution,  [resolutionK/4]).
:- module(resolution,  [resolutionB/3]).
:- module(resolution,  [resolutionKBF/2]).

:- module(resolution,  [fact_circle/2]).
:- module(resolution,  [fact/2]).*/




equall(P, P) :- prop(P), !.
equall(-P, -P) :- prop(P), !.
equall(-(-P), P) :- prop(P), !.




%classical rule
resolution(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1),   
	C2 = kclause(Cclause2, KT2, BT2), 
	Cclause1 = [Cclause11], Cclause2 = [Cclause21], unionC(Cclause11, Cclause21, P, X), 
	append(KT1, KT2, KT), append(BT1, BT2, BT),
	R = kclause([X], KT, BT).

unionC(C1, C2, P, X) :- equall(P, F1), delete(C1, F1, X1), equall(-P, F2), delete(C2, F2, X2), append(X1, X2, X).


%---------------------
%rule KB
resolutionKB(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2), 
	(find_p_resolve(KT1, BT2, P, KX, BX, NewB), (append(KX, KT2, KT), append([NewB], BX, InterB), append(InterB, BT1, BT)) ; 
	find_p_resolve(KT2, BT1, -P, KX, BX, NewB), (append(KX, KT1, KT), append([NewB], BX, InterB), append(InterB, BT2, BT))),
	append(Cclause1, Cclause2, Cclause),
	R = kclause(Cclause, KT, BT).
	
find_p_resolve(KT, BT, P, K, B, R) :- equall(P, F), findPTerm(KT, F, X), equall(-P, F1), findPTerm(BT, F1, Y), 
	delete(KT, X, K), delete(BT, Y, B),
	X = [X1], Y = [Y1],
	unionC(X1, Y1, F, R1),
	append([R1], Y, R).
---------------------

/*equall(-(-P), P) :- prop(P).
equall(-P, -P) :- prop(P).
equall(P, P) :- prop(P).*/




findPTerm([], _, _) :- fail.
findPTerm([Y|KT], P, H) :- equall(P, F), (findPTerm_list(Y, Y, F, X), (H = X, !); findPTerm(KT, P, H)).

findPTerm_list([], _, _, _) :- fail.
findPTerm_list([X|L], O, P, Y) :- equall(P, F), (member(F, X), Y = O; findPTerm_list(L, O, P, Y)).


%the rule-KB
resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),  
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	refind_p_resolve(KT1, KT1, BT2, P, L), L \= [],
	reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, L, R), !.

resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),  
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	refind_p_resolve(KT2, KT2, BT1, -P, L), L \= [],
	reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, L, R), !.

%the rule-KK for forgetKK
resolutionKB_circle(_,_,_,[]) :- !.
resolutionKK_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	append(BT1, BT2, BT),
	refind_p_resolveKK(KT1, KT1, KT2, P, L), L \= [], reunionKK(Cclause, BT, L, R), !.
resolutionKK_circle(_,_,_,[]) :- !.

%the rule-K
resolutionK(C1, C2, P, H) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(BT1, BT2, BT), 
	equall(P, F),
	(member(F, Cclause11), 
	(resolutionK_list(Cclause11, KT2, KT2, F, L), L \= [], reunionK(Cclause21, KT1, BT, F, L, H));
	member(F, Cclause21), resolutionK_list(Cclause21, KT1, KT1, F, L), L \= [], reunionK(Cclause11, KT2, BT, F, L, H)).
resolutionK(C1, C2, P, H) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(BT1, BT2, BT),
	equall(-P, F),
	(member(F, Cclause11),
	(resolutionK_list(Cclause11, KT2, KT2, F, L), L \= [], reunionK(Cclause21, KT1, BT, F, L, H));
	member(F, Cclause21), resolutionK_list(Cclause21, KT1, KT1, F, L), L \= [], reunionK(Cclause11, KT2, BT, F, L, H)).
resolutionK(_, _, _, []) :- !.  %if the "Kterm" does not contain complementary trem of atom P.


%the rule-B
resolutionB(C, P, NewCL) :- C = kclause(Cclause, KT, BT), 
	resolutionB_list(BT, BT, P, L), unionB(Cclause, KT, L, NewCL).
resolutionB(C, P, C) :- !.





%the rule-KBF: eliminate the term which is false
resolutionKBF(C, C1) :- C = kclause(Cclause, KT, BT), 
	find_falseSolvK(KT, NKT),
	find_falseSolvB(BT, NBT),
	C1 = kclause(Cclause, NKT, NBT).

find_falseSolvK([], []) :- !. 
find_falseSolvK([X|KT], [X|L]) :- \+ ([] == X),  find_falseSolvK(KT, L).  
find_falseSolvK([X|KT], L) :- [] == X,  find_falseSolvK(KT, L).  %if [] == X, then X is false

find_falseSolvB([], []) :- !.
find_falseSolvB([X|KT], [X|L]) :- \+ member([], X),  find_falseSolvB(KT, L).
find_falseSolvB([X|KT], L) :- member([], X),  find_falseSolvB(KT, L). %if member([], X), then X is false


reunionKK(Cclause, _, [], []) :- !.
reunionKK(Cclause, BT, [X|L1], [R|L2]) :- X = [K1, K2, NewK], 
	append(K1, K2, KTT),
	append([NewK], KTT, KT),
	R = kclause(Cclause, KT, BT),
	reunionKK(Cclause, BT, L1, L2).

reunionKB_pos(_, _, _, _, _, [], []) :- !.	
reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, [R|L1], [C|L2]) :- R = [KX, BX, NewB], 
	append(KX, KT2, KT), append([NewB], BX, InterB), append(InterB, BT1, BT), 
	C = kclause(Cclause, KT, BT),
	reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, L1, L2).

reunionKB_neg(_, _, _, _, _, [], []) :- !.
reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, [R|L1], [C|L2]) :- R = [KX, BX, NewB], 
	append(KX, KT1, KT), append([NewB], BX, InterB), append(InterB, BT2, BT),
	C = kclause(Cclause, KT, BT),
	reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, L1, L2).

reunionK(_, _, _, _, [], []) :- !. 
reunionK(Cclause, KT1, BT, P, [X|L], [C|H]) :-  X = [K1, NewC1],
	append(K1, KT1, KT),
	unionC(NewC1, Cclause, P, NewC),
	C = kclause([NewC], KT, BT),
	reunionK(Cclause, KT1, BT, P,L, H).

unionB(_, _, [], []) :- !.
unionB(Cclause, KT, [X|L], [NewC|L2]) :-  NewC = kclause(Cclause, KT, X), 
	unionB(Cclause, KT, L, L2).
%-----------------------------------------------------------------------------------

%find the Kterm which contain p and Bterm which contain -P, then compute all the possible resolution and return the consquences.
% e.g: given KT = [[[c, -b]]],  BT= [[[b,a]], [[c,b]]], 
% then the result by resolution "b" is [[[], [[[c, b]]], [[c, a], [b, a]]], [[], [[[b, a]]], [[c, c], [c, b]]]]
refind_p_resolve([], KT, BT, P, []) :- !.
refind_p_resolve(KT1, KT, [], P, []) :- !.
refind_p_resolve([X|L1], KT, BT, P, L) :-  refindPResListKB(X, KT, BT, BT, P, R),
	refind_p_resolve(L1, KT, BT, P, L2),
	append(R, L2, L).

refindPResListKB(_, _, _, [], _, []) :- !.
refindPResListKB(K, KT, BT, NewB, P, []) :- equall(P, F), K = [K1], \+ member(F, K1), !.
refindPResListKB(K, KT, BT, NewB, P, []) :- equall(-P, F1), \+ findPTerm(NewB, F1, Y), !.
refindPResListKB(K, KT, BT, NewB, P, L) :- equall(P, F), K = [K1], member(F, K1), 
	equall(-P, F1), !, findPTerm(NewB, F1, Y), !,
	delete(NewB, Y, NewB1),
	resolveK(KT, BT, K, Y, P, R), !,
	refindPResListKB(K, KT, BT, NewB1, P, L1),
	append(R, L1, L).


%compute all the resolution between a Kterm X(which contain P or -P) and subterm Y(which contain -P or P) in a Bterm
resolveK(KT, BT, X, Y, P, R) :- delete(KT, X, K), delete(BT, Y, B),
	equall(P, F),
	unionKB(X, Y, F, L), %write(L), nl,
	append_list(L, K, B, Y, R).
	
unionKB(K, [], _, []).
unionKB(K, [B|L1], P, [R|L2]) :- equall(-P, F), K = [X1], member(F, B), unionC(X1, B, P, R), unionKB(K, L1, P, L2).
unionKB(K, [B|L1], P, L2) :- equall(-P, F), K = [X1], \+ member(F, B), unionKB(K, L1, P, L2).

append_list([], _, _, _, []).
append_list([X|L1], K, B, Y, [R|L2]) :-  append([X], Y, R1), R = [K, B, R1], append_list(L1, K, B, Y, L2).



refind_p_resolveKK([], KT1, KT2, P, []) :- !.
refind_p_resolveKK(KT1, KT1, [], P, []) :- !.
refind_p_resolveKK([X|L1], KT1, KT2, P, L) :-  refindPResList(X, KT1, KT2, KT2, P, R),
	refind_p_resolveKK(L1, KT1, KT2, P, L2),
	append(R, L2, L).

refindPResList(_, _, _, [], _, []) :- !.
refindPResList(K, KT1, KT2, NewK, P, []) :- equall(P, F), K = [K1], \+ member(F, K1), !.
refindPResList(K, KT1, KT2, NewK, P, []) :- equall(-P, F1), \+ findPTerm(NewK, F1, Y), !.
refindPResList(K, KT1, KT2, NewK, P, [R|L]) :- equall(P, F), K = [K1], member(F, K1), 
	equall(-P, F1), !, findPTerm(NewK, F1, Y), !,
	delete(NewK, Y, NewK1),
	resolveKK(KT1, KT2, K, Y, P, R), !,
	refindPResList(K, KT1, KT2, NewK1, P, L).


resolveKK(KT1, KT2, X, Y, P, R) :- delete(KT1, X, K1), delete(KT2, Y, K2),
	X = [X1], Y = [Y1],
	unionC(X1, Y1, P, NewK),
	R = [K1, K2, [NewK]].


resolutionK_list(Cclause, KT, [], P, []) :- !.
resolutionK_list(Cclause, KT, NewK, P, []) :- equall(-P, F), \+ findPTerm(NewK, F, Y), !.
resolutionK_list(Cclause, KT, NewK, P, [R|L]) :- equall(-P, F), findPTerm(NewK, F, Y), 
	delete(NewK, Y, NewK1), delete(KT, Y, K1),
	Y = [Y1],
	unionC(Cclause, Y1, P, NewC),
	R = [K1, NewC],
	resolutionK_list(Cclause, KT, NewK1, P, L).

resolutionB_list(_, [], _, []) :- !.
resolutionB_list(BT, [X|L1], P, L) :- resolutionB_list_one(BT, X, P, L2), 
	resolutionB_list(BT, L1, P, L3),
	append(L2, L3, L).
	

gainNewBT(_, _, [], []) :- !.
gainNewBT(BT, X, [Y|L], [NewBT|L1]) :- delete(BT, X, BT1),  
	append([Y], X, B), append([B], BT1, NewBT),
	gainNewBT(BT, X, L, L1).

resolutionB_list_one(_, [], _, []) :- !.
resolutionB_list_one( BT, L, P, L1) :- splitINP(L, P, LP, LN),
	resolB(LP, LN, P, L2), 
	gainNewBT(BT, L, L2, L1).

%gain all the possible NewB
resolB([], _, _, []) :- !.
resolB(_, [], _, []) :- !.
resolB([X|LP], LN, P, L) :- resolB_list(X, LN, P, L1), resolB(LP, LN, P, L2), append(L1, L2, L).

resolB_list(X, [], _, []) :- !.
resolB_list(X, [Y|L1], P, [NewC| L2]) :- unionC(X, Y, P, NewC), resolB_list(X, L1, P, L2).

%split L to two list L1 and L2
%L1: contain P
%L2: contain -P
splitINP([], _, [], []) :- !.
splitINP([X|L], P, [X|LP], LN) :- member(P, X), splitINP(L, P, LP, LN).
splitINP([X|L], P, LP, [X|LN]) :- member(-P, X), splitINP(L, P, LP, LN).
splitINP([X|L], P, LP, LN) :- splitINP(L, P, LP, LN).


%----------------------------------end-----------------------------