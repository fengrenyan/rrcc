:- use_module(readf).
:- use_module(mcnf2list).
:- use_module(resolution).
:- use_module(eliminate).
:- use_module(supp).


:- op(300,fx,@). /*@K*/
:- op(400,fx,$). /*$B*/

:- op(500,fx,-).
%:- op(500,fx,~).
:- op(780,xfy,&).
:- op(790,xfy,\/).%/
:- op(800,xfy,->).
:- op(800,xfy,<->).

%-----------define the dynamic predicts------------------
:- dynamic(prop/1).
:- dynamic(klist/1).
:- dynamic(blist/1).
:- dynamic(pair/2).

%---------------------end define---------------------------

ksnc :-
	open('Cresult.txt', write, Str),   
	read_formula(Formula, P, Q),   write("Formula="), write(Formula), nl, !,
	gain_prop(Formula, PN1), write("PN1="), write(PN1), nl, 
	add_propTerm(PN1), append(PN1, [Q],OP), write("OP="), write(OP), nl, !,
	difference_list(P, OP, P1), write("P1="), write(P1), nl, 
	time_output_1(kForget(Formula, P1, SNC),U, V, W),
	write("P="), write(P), nl,
	write("Q="), write(Q), nl,
	write("P1="), write(P1), nl,
	write("T="), write(Formula), nl,
	write(Str,'P='), write(Str, P), nl(Str), %write(Str,"\n"),
	write(Str,'Q='), write(Str, Q), nl(Str), %write(Str,"\n"),
	write(Str,'P1='), write(Str, P1), nl(Str), %write(Str,"\n"),
	write(Str,'Theory='), write(Str, Formula), nl(Str), %write(Str,"\n"),
	write(Str, 'SNC is: '), write(Str, SNC), nl(Str), %write(Str,"\n"),
	write(Str,'UsedInf:'), write(Str, U), nl(Str), %write(Str,"\n"),
	write(Str,'UsedTime:'), write(Str, V), nl(Str), %write(Str,"\n"),
	write(Str,'Wall:'), write(Str, W), nl(Str), %write(Str,"\n"),
	write(Str,'...............................................'), nl(Str),
	retractall(prop(X)),
	close(Str).

	


%gain the atom of a formula
gain_prop(P & Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), 
	unionSet(L1, L2, L).
gain_prop(P \/ Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), %/
	unionSet(L1, L2, L).
gain_prop(@P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(-P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop($P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(P, [P]) :- \+ atom(P), !.

%compute the union of two sets
unionSet(L1, L2, L) :- append(L1, L2, L11), sort(L11, L).

add_propTerm([]) :- !.
add_propTerm([X|L]) :- assert(prop(X)), add_propTerm(L).


%------------------add-------------------------
equall(P, P) :- prop(P), !.
equall(-P, -P) :- prop(P), !.
equall(-(-P), P) :- prop(P), !.


kclause_true(C, Flag) :- C = kclause(Cclause, KT, BT),
	judge_Cclause(Cclause, Flag1),
	judge_KT(KT, Flag2),
	judge_BT(BT, Flag3),
	((Flag1 == true; Flag2 == true; Flag3 == true), Flag = true; Flag = false).

judge_Cclause(Clause, Flag) :- (member([], Clause), Flag = true; Flag = false).

judge_KT(KT, Flag) :- (member([[]], KT), Flag = true; Flag = false).

judge_BT(BT, Flag) :- (member([], BT), Flag = true; Flag = false).


%------------------output the time of solving a problem-----------
time_output_1(Goal, UsedInf,UsedTime,Wall) :-
	time_state(State0),
	call(Goal),
	report_output(State0, 11, UsedInf, UsedTime, Wall).

report_output(t(OldWall, OldTime, OldInferences), Sub, UsedInf,UsedTime,Wall) :-
	time_state(t(NewWall, NewTime, NewInferences)),
	UsedTime is NewTime - OldTime,
	UsedInf  is NewInferences - OldInferences - Sub,
	Wall     is NewWall - OldWall,
	(   UsedTime =:= 0
	->  Lips = 'Infinite'
	;   Lips is integer(UsedInf / UsedTime)
	),
	print_message(information, time(UsedInf, UsedTime, Wall)).


time_state(t(Wall, Time, Inferences)) :-
	get_time(Wall),
	statistics(cputime, Time),
	statistics(inferences, Inferences).
 

%------------------------- end -------------------------------


%-------------action consquent delete--------------
cons_delet :- retractall(pair(_,_)),
	retractall(klist(_)),
	retractall(blist(_)).

	
%--------------------end-----------------------------

 
	
%kForget:knowldege forget
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

%simplify kclause and eliminate true-kclause.
fact_circle([], []) :- !.
fact_circle([C|L], NL) :- fact(C, C1), kclause_true(C1, Flag), Flag == true, fact_circle(L, NL).
fact_circle([C|L], [C1|NL]) :- fact(C, C1), fact_circle(L, NL).


%fact: eliminate the repeat atom and complementary term
fact(C, C1) :- C = kclause(Cclause, KT, BT), 
	factK(KT, KT1),
	factB(BT, BT1),
	(Cclause \= [], (Cclause = [Cclause1], 
	factC(Cclause1, Cclause11),
	C1 = kclause([Cclause11], KT1, BT1));
	C1 = kclause(Cclause, KT1, BT1)).

factC(Cclause, NewC) :-  sort(Cclause, C1), complementary(C1, NewC), !.

%simplify all the KT, eliminate the repeat Kterm
%factK(KT, NewK) :- factK_list(KT, KT2), delete(KT2, [[]], KT1), sort(KT1, NewK).
factK(KT, NewK) :- factK_list(KT, KT1), sort(KT1, NewK), !.

%simplify all the BT, eliminate the repeat Bterm
%factB(BT, NewB) :- factB_list(BT, BT2), delete(BT2, [[]], BT1), sort(BT1, NewB).
factB(BT, NewB) :- factB_list(BT, BT1), sort(BT1, NewB), !.

%simplify Kterm, eliminate the repeat atoms in Kterm
factK_list([], []) :- !.
factK_list([X|L1], [Y|L2]) :- X = [X1], factC(X1, X11), Y = [X11], factK_list(L1, L2).

%simplify Bterm, eliminate the repeat atoms in Bterm
factB_list([], []) :- !.
factB_list([X|L1], [Y|L2]) :- factB_list_one(X, N1), delete(N1, [], N), sort(N, Y), factB_list(L1, L2).

%eliminate the repeat atoms in subterm of Bterm
factB_list_one([], []) :- !.
factB_list_one([X|L1], [Y|L2]) :- factC(X, Y), factB_list_one(L1, L2).


complementary(C, []) :- member(P, C), member(-P, C), !.
complementary(C, C) :- !.


%-----------------------find_P1-------------------
%find all the clause which doesn't include atoms in P.  
find_P1(L, [], L) :- !.
find_P1([], _, []) :- !.
find_P1(L, [P|PL], NewL) :- split_p(L, P, L1, L2, L3, L4, L5, L6),
	find_P1(L6, PL, NewL).
%--------------------------end---------------------------------


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

%----------------mcnf2list--------------------------------------------------------

mcnf2list(F, [KC|L]) :- F =.. [Y|Args], (Y == &), Args = [X, M], kc2list(X, KC), mcnf2list(M, L), !.
mcnf2list(F, [C]) :- kc2list(F, C).

kc2list(KC, kclause(Cclause, KT, BT)) :- devive(KC, L1, L2, L3), 
	(L3 \= [], Cclause=[L3]; Cclause = L3), 
	kterm2list(L1, KT), bterm2list(L2, BT), cons_delet.

%----------------end-----------------------------------------------------------


%--------------------------kterm2list---and---bterm2list---------
kterm2list([], []).
kterm2list([X|L], [H|L1]) :- pair(F, X), F = @P, wff2cnf(P, H), kterm2list(L, L1).

bterm2list([],[]).
bterm2list([X|L], [H|L1]) :- pair(F, X), F = $P, wff2cnf(P, H), bterm2list(L, L1).

%-----------------------------end---------------------------------------------------


devive(C, L1, L2, L3) :- kbc_len(C, Klen, Blen, 0, 0) ,   generate_KBterm(Klen, Blen) ,  
	Klen > 0, Blen > 0 ,
	new_substitute_allk(C, C1,1) , new_substitute_allb(C1, C2,1) ,
	wff2cnf(C2, CNF) , 
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).
	
devive(C, L1, L2, L3) :- klist(KL), blist(BL),  
	  kbc_len(C, Klen, Blen, 0, 0) ,   Klen == 0, Blen > 0,   
	generate_KBterm(Klen, Blen) , 
	new_substitute_allb(C, C2,1) ,
	wff2cnf(C2, CNF) ,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).
	
devive(C, L1, L2, L3) :- klist(KL), blist(BL), 
	  kbc_len(C, Klen, Blen, 0, 0),   Blen == 0, Klen > 0 ,
	generate_KBterm(Klen, Blen) , 
	new_substitute_allk(C, C2,1) ,
	wff2cnf(C2, CNF) , CNF = [Clause],
	split_k(Clause, L1, L2, L3).

devive(C, L1, L2, L3) :-   klist(KL), blist(BL), 
	wff2cnf(C, CNF) , 
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).


%-------------new_substitute_allk-----new_substitute_allb----------------
%Substitute terms @P in Formula with new atoms
new_substitute_allk(Term, NewTerm, N1) :-   getTermk(Term1,N1,L),
	  substitute(@P,Term, Term1, F, Flag),  
	assert(pair(@P,Term1)),
	assert(prop(Term1)),
	(Flag==true, N2 is N1+1; N2 is N1),
	(F == Term, NewTerm = F; new_substitute_allk(F, NewTerm, N2)).

new_substitute_allb(Term, NewTerm, N1) :-   getTermb(Term1,N1,L),  
	substitute($P,Term, Term1, F, Flag),  
	assert(pair($P,Term1)),
	assert(prop(Term1)),
	(Flag==true, N2 is N1+1; N2 is N1),
	(F == Term, NewTerm = F; new_substitute_allb(F, NewTerm, N2)).

% gain a new atom from klist(which is generate dynamic) to substitute
% term @P
getTermk(Term1, N,L) :-  
	klist(L), length(L, N1), (N1 < N, Term1='a'; th_list(L,N,Term1)).

%gain a new atom from blist to substitute term $P
getTermb(Term1, N,L) :-  
	blist(L), length(L, N1), (N1 < N, Term1='a'; th_list(L,N,Term1)).

%substitute @P or $P in formula with new atom
substitute(Term, Term, Terml, Terml, Flag) :- Flag=true,  !.
substitute( _, Term, _, Term, Flag) :- atomic( Term), Flag=false, !.
substitute( Sub, Term, Subl, Terml, Flag) :- Term =.. [F | Args], substlist(Sub, Args, Subl, Argsl, Flag), Terml =.. [F | Argsl].

substlist(_, [],_,[], Flag) :- Flag=false.
substlist(Sub, [Term | Terms], Subl, [Terml | Termsl], Flag):- substitute(Sub, Term, Subl, Terml, Flag1),
		substlist( Sub, Terms, Subl, Termsl, Flag2),
		(Flag1=true, Flag=Flag1; Flag=Flag2).

list_th([H|T],X, N,H) :- N == X,!.
list_th([H|T],X, N,Y) :- M is N+1, list_th(T,X, M,Y).
list_th(F,X, N,Y):- X =< 0, write("error: N<=0").
%list_th(F,X, N,Y):- length(F,L), X > L+1, write("error: N > length of list"), nl, write(N), nl.

th_list(F,X,Y):- list_th(F,X,1,Y).

% ----------end new_substitute_allk-----new_substitute_allb-------------


%----------wff2cnf------and--------wff2dnf--------
wff2cnf(P, [[P]]) :- prop(P), !.
wff2cnf(-P, [[-P]]) :- prop(P), !.
wff2cnf(P->Q, L) :- wff2cnf(-P\/Q, L), !.%/
wff2cnf(P<->Q, L) :- wff2cnf((-P\/Q)&(-Q\/P), L), !.%/
wff2cnf(P&Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), append(L1,L2,L), !.
wff2cnf(P\/Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), %/
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L), !.
wff2cnf(-P, L) :- wff2dnf(P, L1), negate(L1, L), !.

/* wff2cnf(W,NewW) :- negation_inside(W,W1), wff2cnf0(W1,NewW).
*/
wff2cnf0(P, [[P]]) :- prop(P), !.
wff2cnf0(-P, [[-P]]) :- prop(P), !.
wff2cnf0(P&Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), union(L1,L2,L), !.
wff2cnf0(P\/Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), %/
    setof(X, Y^Z^(member(Y,L1), member(Z,L2), union(Y,Z,X)), L), !.
	

	/* wff2dnf transforms a wff to its disjunctive normal form in list format */

wff2dnf(P,[[P]]) :- prop(P), !.
wff2dnf(-P,[[-P]]) :- prop(P), !.
wff2dnf(P->Q, L) :- wff2dnf(-P\/Q, L).
wff2dnf(P<->Q, L) :- wff2dnf((P->Q)&(Q->P), L).
wff2dnf(P\/Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2), append(L1,L2,L).
wff2dnf(P&Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2),
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L).
wff2dnf(-P, L) :- wff2cnf(P,L1), negate(L1,L).
%----------------end----------------------------------------------


/* negate(L1,L): negate L1 in DNF (CNF) and make it into a CNF (DNF). */
negate([],[]) :- !.
negate([[]],[[]]) :- !.
negate(L1,L) :- bagof(X, Y^(member(Y, L1), negate_one_clause(Y,X)), L).

/* negate_one_clause(L1, L2): make all elements in L1 into its complement */
negate_one_clause(L1, L2) :- bagof(X, Y^(member(Y,L1), complement(Y,X)), L2).

complement(true,false) :- !.
complement(false,true) :- !.
complement(P,-P) :- prop(P).
complement(-P,P) :- prop(P).


%L = L2 - L1 and L2 >= L1(must be true)
difference_list([],L2, L2) :- !.
difference_list(L1, L2, L) :-  sort(L1, L11), sort(L2, L22), length(L11, X1), length(L22, X2), 
(X1 >= X2, L= []; bagof( X, (member(X, L22), \+ member(X, L11)), L)), !.

 

%------------------------generate K and B term for substitute --------------------------
generate_KBterm(LK, LB) :- generate_list(1, LK, L1),
	change2Kterm(L1, KL),
	generate_list(1, LB, L2),
	change2Bterm(L2, BL),
	assert(klist(KL)),
	assert(blist(BL)).
	
change2Kterm([], []) :- !.
change2Kterm([X|L], [KX|KL]) :- string_concat('k', X, KY),
	string_to_atom(KY, KX),
	change2Kterm(L, KL).


change2Bterm([], []) :- !.
change2Bterm([X|L], [BX|BL]) :- string_concat('b', X, BY),
	string_to_atom(BY, BX),
	change2Bterm(L, BL).

%generate a list L which is between 1 to N.
generate_list(1, N, []) :- N < 1, !.
generate_list(1, 1, [1]) :- !.
generate_list(1, N, [N|L]) :- X is N-1, generate_list(1, X, L), !.

%-------------------------end-----------------------------


%-----------------------------compute the length of K term and B term of a KClause-----------
kbc_len(C, Klen, Blen, M, N) :- C =.. [Y|Args], Y == \/ , !, kc_listLen(Args, Klen, Blen, M, N), !. %/
kbc_len(C, Klen, Blen, M, N) :- C =.. [Y|Args], Y == @ , !, kc_length(C, Klen, Blen, M, N), !.
kbc_len(C, Klen, Blen, M, N) :- C =.. [Y|Args], Y == $ , !, kc_length(C, Klen, Blen, M, N), !.
kbc_len(C, M, N, M, N) :- !.

kc_listLen([], M, N, M, N) :- !.
kc_listLen([X|L], K, B, M, N) :-   kc_length(X, N1, N2, M, N), L = [Y],   kbc_len(Y, K, B, N1, N2). 

kc_length(C, KLen, BLen, N1, N2) :-  C =.. [Y|Args], Y == @, N11 is N1+1, KLen = N11, BLen = N2.
kc_length(C, KLen, BLen, N1, N2) :-  C =.. [Y|Args], Y == $, N21 is N2+1, KLen = N1, BLen = N21.
kc_length(C, N1, N2, N1, N2) :- !.

%-------------------------end----------------------------------------------

%---------------------split_k-------------------------------
% split the list of term to three classes, L1 is the list of term @P, L2
% is the list of term of $P and L3 is the list of objective term
split_k([],[],[],[]) :- !.
split_k([H|T], [H|L1], L2, L3) :- klist(L),  member(H, L), split_k(T, L1, L2, L3), !.
split_k([H|T], L1, [H|L2], L3) :- blist(L),  member(H, L), split_k(T, L1, L2, L3), !.
split_k([H|T], L1, L2, [H|L3]) :- split_k(T, L1, L2, L3), !.

%---------------------end split_k----------------------------------



%-------------------kcnf2Kwff----------------------------------
kcnf2Kwff(Kcnf, Kwff) :- kcnf2Kwff_list(Kcnf, F), union2Kwff(F, Kwff).

kcnf2Kwff_list([], []).
kcnf2Kwff_list([C|L1], [W|L2]) :- C = kclause(Clause, Kterm, Bterm),
	cnf2wff(Clause, Wff),
	kterm2wff(Kterm, KL),
	bterm2wff(Bterm, BL),
	union2KClause(Wff, KL, BL, W),
	kcnf2Kwff_list(L1, L2).

union2Kwff([], true) :- !.
union2Kwff([X], X) :- !.
union2Kwff([X, Y |L], F) :- F1 = (X & Y), union2Kwff(L, F2), F = (F1 & F2).

kterm2wff([], false) :-!.
kterm2wff([[]], true) :- !.
kterm2wff([L], @W) :- cnf2wff(L, W), !.
kterm2wff([K1|L1], @W1 \/ W2 ):- cnf2wff(K1, W1), kterm2wff(L1, W2).
	
bterm2wff([], false) :- !.
bterm2wff([[]], true) :- !.
bterm2wff([L], $W) :- cnf2wff(L, W), !.
bterm2wff([K1|L1], $W1 \/ W2 ):- cnf2wff(K1, W1), bterm2wff(L1, W2).

union2KClause(true, _, _, true) :- !.
union2KClause(_, true, _, true) :- !.
union2KClause(_, _, true, true) :- !.
union2KClause(false, KL, BL, W) :- union2KClausell(KL, BL, W).
union2KClause(Wff, KL, BL, W) :- union2KClausff(Wff, KL, BL, W).

union2KClausell(false, BL, BL) :- !.
union2KClausell( KL, false, KL) :- !.
union2KClausell(KL, BL, KL \/ BL) :- !.

union2KClausff(Wff, false, false, Wff) :- !.
union2KClausff(Wff, false, BL, Wff \/ BL) :- !.
union2KClausff(Wff, KL, false, Wff \/ KL) :- !.
union2KClausff(Wff, KL, BL, Wff \/ BL \/ KL) :- !.

%---------------cnf2wff----dnf2wff-----------
/* dnf2wff(L,W) convert a DNF list to a formula */

dnf2wff([],false) :- !.
dnf2wff([[]],true) :- !.
dnf2wff([L], W) :- list2conjunct(L,W), !.
dnf2wff([L1|L2], W1 \/ W2) :- list2conjunct(L1, W1), dnf2wff(L2,W2).

/* cnf2wff(L,W) convert a CNF list to a formula */

cnf2wff([[]],false) :- !.
cnf2wff([],true) :- !.
cnf2wff([L], W) :- list2disjunct(L,W), !.
cnf2wff([L1|L2], W1 & W2) :- list2disjunct(L1, W1), cnf2wff(L2,W2).


/* list2conjunct(L,A): A is the conjunction of all formulas in L */

list2conjunct([P],P) :- !.
list2conjunct([P | L],P & W) :- list2conjunct(L,W).


/* list2disjunct(L,A): A is the disjunction of all formulas in L: A=false when
   L is empty */

list2disjunct(L, true) :- member(true,L), !.
list2disjunct(L, true) :- member(-P,L), member(P,L), !.
list2disjunct(L, W) :- sort(L,L1), delete(L1,false,L2), list2disj(L2,W), !.
list2disj([], false) :- !.
list2disj([P],P) :- !.
list2disj([P | L],P \/ W) :- list2disj(L,W).

%-----------------------------end--------------------------------------



