
:- module(eliminate, [eliminate_subsum/3]).

%eliminate those clauses in L, that are subsumed by another one of the clause in L
eliminate_subsum([],L, L) :- !.
eliminate_subsum(_, [], []) :- !.
eliminate_subsum([X|L1], L2, L) :- delete(L2, X, L3), eliminate_subsum_one(X, L3, L11),
	(\+ bagof(Y, (member(Y, L3), \+ member(Y, L11)), AL), AL = [];
		bagof(Y, (member(Y, L3), \+ member(Y, L11)), AL)),
	(\+ bagof(Y1, (member(Y1, L1), \+ member(Y1, AL)), L12), L12 = [];
		bagof(Y1, (member(Y1, L1), \+ member(Y1, AL)), L12)),
	(\+ member(X, AL), eliminate_subsum(L12, [X|L11], L); eliminate_subsum(L12, L11, L)).


%eliminate the clause B, if A subsum B
eliminate_subsum_one(_, [], []) :- !.
eliminate_subsum_one(X, [Y|L1], [Y|L]) :- subsum_Kcl(X, Y, Flag),
	Flag == false, eliminate_subsum_one(X, L1, L).
eliminate_subsum_one(X, [Y|L2], L) :- eliminate_subsum_one(X, L2, L).

%judge whether C1 subsume C2, if so then Flag=true, else Flag=false.
subsum_Kcl(C1, C2, Flag) :- C1 = kclause(Cclause1, KT1, BT1),
	C2 = kclause(Cclause2, KT2, BT2),
	Cclause1=[Cclause11], Cclause2=[Cclause21],
	subsume_Ccl(Cclause11, Cclause21, Flag1),
	(Flag1=false, (subsume_CBT(Cclause1, BT2, Flag4), Flag11=Flag4); Flag11=Flag1),
	subsume_KT(KT1, KT2, Cclause21, BT2, Flag2),
	subsume_BT(BT1, BT2, Flag3),
	((Flag11=true, Flag2=true, Flag3=true), Flag=true; Flag = false), !.

%if Cc1 subsume Cc2, i.e Cc1 is a subset of Cc2, then Flag=true, else Flag=false.
subsume_Ccl(Cc1, Cc2, Flag) :-  (\+ (member(X,Cc1), \+ member(X,Cc2)), Flag = true; Flag = false).

%if exists Y in BT2, s.t. Cclause subsume Y, then Flag=true, else Flag=false.
subsume_CBT(Cclause, BT2, Flag) :- subsume_BT_list(Cclause, BT2, Flag), !.

%if for every X in KT1, exists Y in KT2, s.t X subsume Y, then Flag=true, else Flag=false.
subsume_KT([], _, Cclause21, BT2, true) :- !.
subsume_KT(_, [], Cclause21, BT2, false) :- !.
subsume_KT([X|KT1], KT2, Cclause21, BT2, Flag) :- subsume_KT_list(X, KT2, Flag1), 
	(Flag1=false, (subsume_KTC(X, Cclause21, Flag3), Flag11=Flag3); Flag11=Flag1),
	(Flag11=false, (subsume_KTBT(X, BT2, Flag4), Flag111=Flag4); Flag111=Flag11),
	subsume_KT(KT1, KT2, Cclause21, BT2, Flag2), ((Flag111=true, Flag2=true), Flag=true; Flag=false).

%if X subsume Cclause, then Flag=ture, else Flag=false.
subsume_KTC(X, Cclause, Flag) :- X=[Y], subsume_Ccl(Y, Cclause, Flag), !.

%if exists Y in BT2, s.t X subsume every elements in Y. This is similar with subsume_BT.
subsume_KTBT(X, BT2, Flag) :- subsume_BT_list(X, BT2, Flag), !.

% If exists Y in KT2 s.t X subsume Y, then Flag=true, else Flag=false.
subsume_KT_list(X, [], false) :- !.
subsume_KT_list(X, [Y|KT2], Flag) :- X = [X1], Y = [Y1], subsume_Ccl(X1, Y1, Flag1),
	(Flag1=true, (Flag=true, !); subsume_KT_list(X, KT2, Flag)).

%if for every X in BT1, exists Y in BT2, s.t X subsume Y, then Flag=true, else Flag=false.
subsume_BT([], _, true) :- !.
subsume_BT(_, [], false) :- !.
subsume_BT([X|BT1], BT2, Flag) :- subsume_BT_list(X, BT2, Flag1),
	subsume_BT(BT1, BT2, Flag2), ((Flag1=true, Flag2=true), Flag=true; Flag=false).

% If exists Y in BT2 s.t X subsume Y, then Flag=true, else Flag=false.
subsume_BT_list(X, [], false) :- !.
subsume_BT_list(X, [Y|BT2], Flag) :- subsume_bterm(X, Y, Flag1),
	(Flag1=true, (Flag=true, !); subsume_BT_list(X, BT2, Flag)).

%if for all Y in L2, exists X in L1 s.t X subsume Y, then Flag=true, else Flag=false.
subsume_bterm([], X, false) :- !.
subsume_bterm(_, [], true) :- !.
subsume_bterm(L1, [Y|L2], Flag) :- subsume_bterm_list(L1, Y, Flag1),
	subsume_bterm(L1, L2, Flag2), ((Flag1=true, Flag2=true), Flag=true; Flag=false).

subsume_bterm_list([], _, false) :- !.
subsume_bterm_list([X|L1], Y, Flag) :- subsume_Ccl(X, Y, Flag1),
	(Flag1=true, (Flag=true, !); subsume_bterm_list(L1, Y, Flag)).

%-----------------------------------end--------------------------