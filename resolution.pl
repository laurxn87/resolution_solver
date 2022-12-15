/*
1. YES
2. YES
3. YES
4. NO
5. NO
6. NO
7. YES
8. NO
9. NO
10.YES
*/

?-op(140,fy,neg).
?-op(160,xfy,[and, or, imp, revimp, uparrow, downarrow, notimp, notrevimp, equiv, notequiv]).

/* member(Item,List) :- Item occurs in List 
*/
member(X,[X|_]).
member(X,[_|Tail]) :- member(X,Tail).

/*remove(Item,List,Newlist):-Newlist is the result of removing all occurrences of of Item from List 
*/
remove(_,[],[]).
remove(X, [X|Tail], Newtail):- 
    !,
    remove(X,Tail,Newtail).
remove(X,[Head|Tail],[Head|Newtail]):-
    remove(X,Tail,Newtail).

/* conjunctive(X) :- X is an alpha formula.
*/
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).
conjunctive(neg(_ equiv _)).
conjunctive(_ notequiv _).


/* disjunctive(X) :- X is an alpha formula.
*/
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ uparrow _).
disjunctive(_ revimp _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).
disjunctive(neg(_ notequiv _)).
disjunctive(_ equiv _).

/* unary(X):- X is a double negation or a negated constant 
*/
unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X, Y, Z):- Y and Z are the components of the formula X, as defined in the alpha and beta table.
*/
components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).
components(X equiv Y, X and Y , neg X and neg Y).
components(neg(X equiv Y), neg X or Y, X or neg Y).
components(X notequiv Y, neg X or Y, X or neg Y).
components(neg(X notequiv Y), X and Y , neg X and neg Y).

/* component(X,Y) :- Y is the component of the unary formula X */
component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion process to Old, which is a generalized disjunction of generalized conjunctions.
*/
singlestep([Disjunction|Rest],New):-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    remove(Formula,Disjunction,Temporary),
    Newdis = [Newformula|Temporary],
    New = [Newdis|Rest].

singlestep([Disjunction|Rest],New):-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha,Alpha1,Alpha2),
    remove(Alpha,Disjunction,Temporary),
    Newdis1 = [Alpha1|Temporary],
    Newdis2 = [Alpha2|Temporary],
    New = [Newdis1, Newdis2|Rest].


singlestep([Disjunction|Rest],New):-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta,Beta1,Beta2),
    remove(Beta,Disjunction,Temporary),
    Newdis = [Beta1,Beta2|Temporary],
    New = [Newdis|Rest].

singlestep([Disjunction|Rest],[Disjunction|Newrest]) :-
    singlestep(Rest,Newrest).

/* expand(Old,New) :- New is the result of applying singlestep as many times as possible, starting with Old */
expand(Con, Newcon) :- 
    singlestep(Con, Temp),
    !,
    expand(Temp,Newcon).

expand(Con, Con).

/* clauseform(X,Y) :- Y is the conjunctive normal form of X */
clauseform(X,Y):- expand([[X]],Y).

/* double(X,Y,Z):- true if X is a member of Y where Y is a list of lists and Z is the rest of the list containing X */
double(X,[X|_],X).
double(X,[Y|_],Z):- 
    member(X,Y), 
    Z = Y.
double(X,[_|Tail],Z):- 
    double(X,Tail,Z).

/*sub(X,Y) :- true if X is a subset of any of Y */
sub(X,[Element|Rest]):-     
    not(subset(Element,X)),
    sub(X,Rest).

sub(X,[Element|_]):- 
    subset(Element,X).

/* combine(A,B,C):- combines list A and list B without any duplicates */
combine(A, B, C):-
  append(A1, Common, A),
  append(Common, B1, B),
  !,  
  /*The cut here is to keep the longest common sub-list*/
  append([A1, Common, B1], C).

/* resolutionstep(Conjunction, Newconjunction):- applies one step of resolution to the Conjunction and returns it as Newconjunction */
resolutionstep([[false]|Rest],[[]|Rest]).

resolutionstep([Disjunction|Rest],New):- 
    /*given [X|Y]*/
    member(X,Disjunction),
    remove(X,Disjunction,Y),

    (unary(neg X)->
        component(neg X, Neg);
    not(unary(neg X))->
        Neg = neg X
    ),
    /*check for the existence of [neg X|Z]*/
    double(Neg, Rest,T),
    /*add [Y|Z] to the conjunctive list, */
    remove(Neg,T,Z),
    combine(Y,Z,Resolvent),
    %check that no permutation of the resolvent is already in the list or that the resolvent isnt already in the list in some form
    not(sub(Resolvent,Rest)),
    % writeln('resolution possible'),
    append([Disjunction|Rest],[Resolvent],New).
    % writeln(New).

resolutionstep([Disjunction|Rest],[Disjunction|Newrest]):-  
% writeln('failed'),    
resolutionstep(Rest,Newrest). 


/* resolution(Conjunction, Newcon):- repeatedly applies the resolutionstep until it is no longer is possible */
resolution(Conjunction, Newcon):- % resolution did something
    resolutionstep(Conjunction, Temporary),
    % get the resolvent
    last(Temporary,X),
    % check if the resolvent was already present in the list
    not(sub(X,Conjunction)),
    % writeln('resolution did something'),
    resolution(Temporary, Newcon).

resolution(Conjunction, Conjunction).

% closed(Tableau):- True if there is a [] or false is in the list of expanded disjunctions
closed(Tableau):- 
    member([],Tableau).

closed(Tableau):- 
    member([false], Tableau).

if_then_else(P,Q,_):- P, !, Q.
if_then_else(_,_,R):- R.

yes:- write('YES'),nl.
no:- write('NO'), nl.

test(X):- 
    clauseform(neg X,Cnf),
    % writeln(Cnf),
    resolution(Cnf,Final),!,
    % writeln(Final),
    if_then_else(closed(Final), yes, no).
