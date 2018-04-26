
:- module(readf,  [read_formula/3]).

%read formula from file and assert the atom which in formula
read_formula(Formula, P, Q) :- 
	write_ln('input: '), read(user_input,Input), %consult(Input),
	string_concat(Input, '.txt', Filename1),
	string_to_atom(Filename1, Filename),
	read_file(Filename, Formula, P, Q).


read_file(Filename, [],P,Q) :- open(Filename, read, Str), at_end_of_stream(Str), write("there is no formula\n"), !.
read_file(Filename, Formula, P, Q) :-
	open(Filename, read, Str),
	read(Str, Formula),
	read(Str, Q),
	read(Str, P),
	close(Str).