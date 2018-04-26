
:- module(wff2cnf, [wff2cnf/2, wff2dnf/2]).

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