
:- module(mcnf2list, [mcnf2list/2]).

:- use_module(wff2cnf).

%----------------mcnf2list--------------------------------------------------------

mcnf2list(F, [KC|L]) :- F =.. [Y|Args], (Y == &), Args = [X, M], kc2list(X, KC), mcnf2list(M, L), !.
mcnf2list(F, [C]) :- kc2list(F, C).

kc2list(KC, kclause(Cclause, KT, BT)) :- devive(KC, L1, L2, L3), 
	(L3 \= [], Cclause=[L3]; Cclause = L3), 
	kterm2list(L1, KT), bterm2list(L2, BT), cons_delet.

kterm2list([], []).
kterm2list([X|L], [H|L1]) :- pair(F, X), F = @P, wff2cnf(P, H), kterm2list(L, L1).

bterm2list([],[]).
bterm2list([X|L], [H|L1]) :- pair(F, X), F = $P, wff2cnf(P, H), bterm2list(L, L1).

%-----------------------------end---------------------------------------------------


devive(C, L1, L2, L3) :- kbc_len(C, Klen, Blen, 0, 0) ,   generate_KBterm(Klen, Blen) ,  
	Klen > 0, Blen > 0 ,
	new_substitute_allk(C, C1,1) , new_substitute_allb(C1, C2,1) ,
	wff2cnf(C2, CNF) , 
	write("CNF="), write(CNF), nl,
	%simply_dnf(DNF, F1),
	%write("DNF_simple="), write(F1), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).
	
devive(C, L1, L2, L3) :- klist(KL), write("KL="), write(KL), nl, blist(BL), write("BL="), write(BL), nl, 
	  kbc_len(C, Klen, Blen, 0, 0) ,   Klen == 0, Blen > 0,   
	generate_KBterm(Klen, Blen) ,
	%generate_list(1, Blen, L2) ,
	%change2Bterm(L2, BL) ,
	%assert(blist(BL)) ,
	new_substitute_allb(C, C2,1) ,
	wff2cnf(C2, CNF) ,
	write("CNF="), write(CNF), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).
	
devive(C, L1, L2, L3) :- klist(KL), write("KL="), write(KL), nl, blist(BL), write("BL="), write(BL), nl,
	  kbc_len(C, Klen, Blen, 0, 0),   Blen == 0, Klen > 0 ,
	generate_KBterm(Klen, Blen) ,
	%generate_list(1, Klen, L2) ,   
	%change2Kterm(L2, KL) ,
	%assert(klist(KL)) ,
	new_substitute_allk(C, C2,1) ,
	wff2cnf(C2, CNF) ,
	write("CNF="), write(CNF), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).

devive(C, L1, L2, L3) :-   klist(KL), write("KL="), write(KL), nl, blist(BL), write("BL="), write(BL), nl,
	wff2cnf(C, CNF) ,
	write("CNF="), write(CNF), nl,
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
getTermk(Term1, N,L) :- %L= [k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11],
	klist(L), length(L, N1), (N1 < N, Term1='a'; th_list(L,N,Term1)).

%gain a new atom from blist to substitute term $P
getTermb(Term1, N,L) :- %L=[b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11],
	blist(L), length(L, N1), (N1 < N, Term1='a'; th_list(L,N,Term1)).

%substitute @P or $P in formula with new atom
substitute(Term, Term, Terml, Terml, Flag) :- Flag=true,
	%write("Flag''="),write(Flag), nl,
	!.
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