
%:- module(kforget, [kForget/3, difference_list/3]).



%----------------------------kForget----------------------------------------
%knowledge forget under S5
kForget(F,[],F) :- !.
kForget(F, LP, NEW) :- mcnf2list(F, List), write("List"),write(List),nl, find_P1(List, LP, List1),
	difference_list(List1, List, List2),
	kforget(List2, LP, NEW1), 
	supp(NEW1, LP, NEW2), 
	append(NEW2, List1, NEWK), kcnf2Kwff(NEWK, NEW).
kForget(F, LP, NEW) :- mcnf2list(F, List), supp(List, LP, NEWK), kcnf2Kwff(NEWK, NEW).

%compute the result of forget some atoms(P) from formula with MDNF
kforget([],_, []) :- !.
kforget(A,[],A) :- !.
kforget(L, [P|LP], F) :-  kforget_one(L, P, F1),
	eliminate_subsum(F1, F1, F2), kforget(F1, LP, F), !. 

kforget_one([], _, _) :- !.
kforget_one(L, P, R) :-  fact_circle(L, NL), sort(NL, NewL),
	forget_all(NewL, P, F), 
	(F \= NewL, kforget_one(F, P, R); R = F), !.


%find all the clause which doesn't include atoms in P.  
find_P1(L, [], L) :- !.
find_P1([], _, []) :- !.
find_P1(L, [P|PL], NewL) :- split_p(L, P, L1, L2, L3, L4, L5, L6),
	find_P1(L6, PL, NewL).


forget_all([], _, []) :- !.
forget_all(L, P, F) :- split_p(L, P, L1, L2, L3, L4, L5, L6), 
	forget(L1, L2, P, F1), 
	forgetKB(L3, L4, P, F2), 
	forgetKB(L3, L5, P, F3), 
	forgetKB(L5, L4, P, F4),
	forgetK(L3, L2, P, F5),
	forgetK(L1, L4, P, F6),
	forgetK(L5, L2, P, F7),
	forgetK(L1, L5, P, F8),
	forgetKK(L3, L5, P, F9),
	forgetKK(L5, L4, P, F10),
	forgetKK(L3, L4, P, F11),
	forgetB(L5, P, F12),
	delete_list(L, L1, L11),
	delete_list(L11, L2, L22),
	appendAll([F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, L22], OF),
	circle_false(OF, OF1),
	fact_circle(OF1, OF2),
	sort(OF2, F).

delete_list([], _, []) :- !.
delete_list(L, [], L) :- !.
delete_list(L1, [X|L2], L) :- delete(L1, X, L3), delete_list(L3, L2, L).

circle_false([], []) :- !.
circle_false([C|OF], [C1|NF]) :- resolutionKBF(C, C1), circle_false(OF, NF).

appendAll([], []) :- !.
appendAll([X], X) :- !.
appendAll([X,Y|L1], NewL) :- append(X, Y, R), appendAll(L1, L), append(R, L, NewL).

forget([], _, P, []) :- !. %classical rule
forget(_, [], _, []) :- !.
forget([X|L1], L2, P, F) :- forget_list(X, L2, P, F1), forget(L1, L2, P, F2), append(F1, F2, F).

forget_list(X, [], P, []) :- !.
forget_list(X, [Y|L1], P, [H|L2]) :- resolution(X, Y, P, H), forget_list(X, L1, P, L2), !.

forgetKB([], _, P, []) :- !.  % rule-KB and rule-KK
forgetkB(_, [], _, []) :- !.
forgetKB([X|L1], L2, P, F) :- forgetKB_list(X, L2, P, F1), forgetKB(L1, L2, P, F2), append(F1, F2, F).

forgetKB_list(X, [], P, []) :- !.
forgetKB_list(X, [Y|L1], P, L) :- resolutionKB_circle(X, Y, P, H), 
	forgetKB_list(X, L1, P, L2), append(H, L2,L),!.

forgetK([], _, P, []) :- !.  % rule-K
forgetK(_, [], _, []) :- !.
forgetK([X|L1], L2, P, F) :- forgetK_list(X, L2, P, F1), forgetK(L1, L2, P, F2), append(F1, F2, F).

forgetK_list(X, [], P, []) :- !.
forgetK_list(X, [Y|L1], P, L) :- resolutionK(X, Y, P, H), 
	forgetK_list(X, L1, P, L2), append(H, L2,L),!.

forgetKK([], _, P, []) :- !.  % rule-KK
forgetkK(_, [], _, []) :- !.
forgetKK([X|L1], L2, P, F) :- forgetKK_list(X, L2, P, F1), forgetKK(L1, L2, P, F2), append(F1, F2, F).

forgetKK_list(X, [], P, []) :- !.
forgetKK_list(X, [Y|L1], P, L) :- resolutionKK_circle(X, Y, P, H), 
	forgetKK_list(X, L1, P, L2), append(H, L2,L),!.

forgetB([], P, []) :- !.  % rule-B
forgetB([X|L1],P, F) :- resolutionB(X, P, F1), forgetB(L1, P, F2), append(F1, F2, F).

%forgetB_list(X, P, L) :- resolutionB(X, P, H), 
%	forgetB_list(X, L1, P, L2), append(H, L2,L),!.

%-----------------------------end----------------------------------------------

%L = L2 - L1 and L2 >= L1(must be true)
difference_list([],L2, L2) :- !.
difference_list(L1, L2, L) :-  sort(L1, L11), sort(L2, L22), length(L11, X1), length(L22, X2), 
(X1 >= X2, L= []; bagof( X, (member(X, L22), \+ member(X, L11)), L)), !.


%-----------------------split_p/6--------------------------------------------
%split the set of KClause to six lists, which is L1, L2, L3, L4,L5, L6
%L1: the set of KClause-kclause(L1, L2, L3), where P is a member of L1
%L2: the set of KClause-kclause(L1, L2, L3), where -P is a member of L1
%L3: the set of KClause-kclause(L1, L2, L3), where P is a member of L2 or L3
%L4: the set of KClause-kclause(L1, L2, L3), where -P is a member of L2 or L3
%L5: the set of KClause-kclause(L1, L2, L3), where -P and P is a member of L2 or L3
%L6: the others
split_p([],_,[],[],[],[], [], []) :- !.
split_p([X|L], P, [X|L1], L2, L3, L4, L5, L6) :- X = kclause(Cclause, KT, BT), 
	Cclause \= [], Cclause = [Cclause1], member(P, Cclause1), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, [X|L2], L3, L4, L5, L6) :- X = kclause(Cclause, KT, BT), 
	Cclause \= [], Cclause = [Cclause1], member(-P, Cclause1), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_k(KT, P), member_b(BT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_k(KT, -P), member_b(BT, P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_k(KT, P), member_k(KT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_b(KT, P), member_b(BT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, [X|L3], L4, L5, L6) :- X = kclause(Cclause, KT, BT), member_k(KT, P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, [X|L3], L4, L5, L6) :- X = kclause(Cclause, KT, BT), \+ member_k(KT, P), member_b(BT, P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, L3, [X|L4], L5, L6) :- X = kclause(Cclause, KT, BT), member_k(KT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, [X|L4], L5, L6) :- X = kclause(Cclause, KT, BT), \+ member_k(KT, -P), member_b(BT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, L3, L4, L5, [X|L6]) :- split_p(L, P, L1, L2, L3, L4, L5, L6).


%if P appear in KT then return true, else false.
member_k(KT, P) :- member_klist(KT, P).

member_klist([], P) :- fail.
member_klist([X|L], P) :- X = [Y], (member(P, Y), !; member_klist(L, P)).

%if P appear in BT then return true, else false.
member_b(KT, P) :- member_blist(KT, P).

member_blist([], P) :- fail.
member_blist([X|L], P) :- (member_list(X, P), !; member_blist(L, P)).

member_list([], P) :- fail.
member_list([X|L], P) :- (member(P, X), !; member_list(L, P)).