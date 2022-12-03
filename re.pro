%% -*- prolog -*-

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Fonctions de compatibilité entre différents systèmes Prolog.
%% Devrait marcher avec SWI-Prolog et GNU Prolog.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% character(+C)
%% Vérifie que C est un caractère.
%% Prolog, comme C, représente les caractères par leur code ASCII,
%% mais certaines implémentation, comme SWI, utilisent des atomes
%% de longueur 1 à la place.
character(Char) :- integer(Char); atom(Char), atom_length(Char, 1).

%% Certains systèms définissent `list` d'autres `is_list`, alors à la place
%% on défini le nôtre.
isa_list([]).
isa_list([_|_]).

%% string_to_chars(+Str, -Chars)
%% Converti une "string" en une liste de caractères.
%% Les chaînes de caractères peuvent être représentées de différentes manières,
%% et cela dépend aussi du système Prolog utilisé.
string_to_chars(Str, Chars) :- atom(Str), atom_codes(Str, Chars).
string_to_chars(Str, Chars) :-
    %% Le Prolog officiel fait comme Haskell:  "String = [Char]".
    %% GNU Prolog suit cette pratique mais pas SWI Prolog qui utilise un
    %% type séparé pour les chaînes de caractères, qu'il faut donc convertir
    %% via `string_chars`.
    "" = [] -> fail;
    string(Str), string_chars(Str, Chars).
string_to_chars(Str, Chars) :- isa_list(Str), Chars = Str.

%% chars_to_string(+Chars, -Str)
%% Converti une liste de caractères en une "string".
%% Si le système Prolog utilisé supporte les "string"s utilise ça,
%% sinon utilise un atome.
chars_to_string(Chars, Str) :-
    "" = [] -> atom_codes(Str, Chars); string_chars(Str, Chars).

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :-
    (predicate_property(new_atom/2, built_in);    % Older GNU Prolog
     predicate_property(new_atom(_,_), built_in)) % Newer GNU Prolog
    -> new_atom(X, A);
    gensym(X, A).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%         Expressions Régulières (RE)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% re_wf(+RE)
%% Vérifie que RE est une expression régulière valide (Well-Formed).
re_wf(Char) :- character(Char).
re_wf(any).                     % Souvent nommé `.`.
re_wf(in([])).
re_wf(in([Char|Chars])) :- character(Char), re_wf(in(Chars)).
re_wf(notin(Chars)) :- re_wf(in(Chars)).
re_wf([]).                                   % Souvent nommé `ϵ`.
re_wf([RE|REs]) :- re_wf(RE), re_wf(REs).    % Concaténation.
re_wf(RE1 \/ RE2) :- re_wf(RE1), re_wf(RE2). % Disjonction.
re_wf(?(RE)) :- re_wf(RE).
re_wf(*(RE)) :- re_wf(RE).
re_wf(+(RE)) :- re_wf(RE).
re_wf(name(Name, RE)) :- (atom(Name); integer(Name)), re_wf(RE). %Motif nommé.
%% Compatibilité pour les Prolog où "String ≠ [Char]".
re_wf(in(String)) :-
    "" = [] -> fail;
    string(String), string_chars(String, Chars), re_wf(in(Chars)).
re_wf(String) :-
    "" = [] -> fail;
    string(String), string_chars(String, Chars), re_wf(Chars).

%% match(+RE, +Str, -Groups, -Tail)
%% Fait un pattern-match de l'expression régulière RE sur la liste de
%% caractères Str.  Tail est la partie de Str qui reste après la
%% partie acceptée par RE.  Groups contient la liste des "motifs nommés" qui
%% ont été trouvés, avec leur chaîne de caractères.
match(Char, [Char|Tail], [], Tail) :- character(Char).
match(any, [_|Tail], [], Tail).
match(in(Chars), [Char|Tail], [], Tail) :- member(Char, Chars).
match(notin(Chars), [Char|Tail], [], Tail) :-
    isa_list(Chars), \+ member(Char, Chars).
match([], Tail, [], Tail).
match([RE|REs], Str, Gs, Tail) :-
    match(RE, Str, Gs1, T), match(REs, T, Gs2, Tail),
    append(Gs1, Gs2, Gs).
match(RE1 \/ RE2, Str, Gs, Tail) :-
    match(RE1, Str, Gs, Tail); match(RE2, Str, Gs, Tail).
match(?(RE), Str, [], Tail) :- match(RE, Str, [], Tail).
match(?(_), Str, [], Str).
match(*(RE), Str, Gs, Tail) :-
    match(RE, Str, Gs1, T),
    Str \= T,      %Évite boucle-sans-fin lorsque RE accepte la chaîne vide.
    match(*(RE), T, Gs2, Tail),
    append(Gs1, Gs2, Gs).
match(*(_), Str, [], Str).
match(+(RE), Str, Gs, Tail) :-
    match(RE, Str, Gs1, S), match(*(RE), S, Gs2, Tail),
    append(Gs1, Gs2, Gs).
match(name(Name, RE), Str, [(Name = GStr)|Gs], Tail) :-
    match(RE, Str, Gs, Tail),
    append(GChars, Tail, Str),
    %% Utilise `chars_to_string` pour que le résultat soit plus facile
    %% à lire pour un humain.
    chars_to_string(GChars, GStr).
%% Compatibilité pour les Prolog où "String ≠ [Char]".
match(String, Str, Gs, Tail) :-
    "" = [] -> fail;
    string(String), string_chars(String, Chars), match(Chars, Str, Gs, Tail).
match(in(String), Str, Gs, Tail) :-
    "" = [] -> fail;
    string(String), string_chars(String, Chars),
    match(in(Chars), Str, Gs, Tail).
match(notin(String), Str, Gs, Tail) :-
    "" = [] -> fail;
    string(String), string_chars(String, Chars),
    match(notin(Chars), Str, Gs, Tail).

%% match_string(+RE, +Str, -Groups, -Tail)
%% Comme `match`, mais opère sur des "string".
%% Accepte en entrée n'importe quel type de "string":
%% - un atome
%% - une liste de caractères (la représentation standard ISO Prolog).
%% - un objet de type "string" (e.g. comme utilisé dans SWI-Prolog).
%% En sortie renvoie un "string" si possible (e.g. en SWI-Prolog)
%% ou sinon renvoie un atome.
match_string(RE, Str, Gs, Tail) :-
    string_to_chars(Str, Chars),
    match(RE, Chars, Gs, TailChars),
    chars_to_string(TailChars, Tail).

%% search_in_chars(+RE, +Str, -Res)
%% Boucle de recherche, qui essaie de trouver des sous-chaînes acceptées par
%% l'expression régulière RE.
%% Renvoie dans Res la chaîne qui a été acceptée par RE et
%% les sous-groupes qui ont été trouvés.
search_in_chars(RE, Str, Res) :-
    match(RE, Str, Gs, Tail), append(FoundChars, Tail, Str),
    chars_to_string(FoundChars, Found),
    Res = ['' = Found | Gs].
search_in_chars(RE, [_|Str], Res) :- search_in_chars(RE, Str, Res).

%% search(+RE, +Str, -Res)
%% Comme `search_in_chars` mais accepte des "strings".
search(RE, Str, Res) :-
    string_to_chars(Str, Chars),
    search_in_chars(RE, Chars, Res).

%% Exemples de recherches:
%% search("hello" \/ "help" \/ [*("a"),"b"], "hello about help", Res)
%% search(["(", name(k,*(any)), "=", name(v,*(any)), ")"],
%%         "(age=23) and (position=straight)", Res)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%         Non-deterministic Finite State Automaton  (NFA)
%%
%% Un automate à états finis non-déterministe est représenté ici par un
%% ensemble d'états ("State"), où chaque état est associé à un pas ("Step")
%% qui indique ce qui peux se passer quand on est dans cet état.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% state_wf(+State, +NFA)
%% Vérifie que State est un état valide dans NFA.
state_wf(State, NFA) :- atom(State), member((State = _), NFA).

%% step_wf(+Step, +NFA)
%% Vérifie que Step est un pas valide dans NFA.
%% Un pas peu prendre la forme:
%% - "success" si on a atteint un état final (i.e. un succès).
%% - "step(Steps)" où Steps est une liste d'éléments de la forme
%%   (Char -> State) qui indique quel est l'état suivant selon le prochain
%%   caractère.  À noter que ces éléments peuvent mentionner plusieurs fois
%%   le même caractère, auquel cas chacun des états correspondants est
%%   acceptable.  C'est ce qui justifie le "N" de "NFA".
%%   Au lieu de se terminer par une liste vide, la liste
%%   simplement chaînée peut se terminer par un état, qui est alors utilisé
%%   pour n'impore quel caractère qui n'est pas mentionné dans la liste.
%% - "epsilon(Marks,States)" où States est une liste d'états vers lesquels la
%%   machine peut transitionner sans avoir besoin d'avancer d'un caractère.
%%   Ceci aussi justifie le "N" de "NFA".
%%   Marks est une liste de "marques" de la forme `beg(Name)` ou `end(Name)`,
%%   qui indiquent que le sous-groupe nommé Name commence ou fini ici.
step_wf(success, _).
step_wf(step([]), _).
step_wf(step(S), NFA) :- state_wf(S, NFA).
step_wf(step([(Char -> State) | Steps]), NFA) :-
    character(Char), state_wf(State, NFA), step_wf(step(Steps), NFA).
step_wf(epsilon([], []), _).
step_wf(epsilon([], [State | States]), NFA) :-
    state_wf(State, NFA), step_wf(epsilon([], States), NFA).
step_wf(epsilon([Mark|Marks], Ss), NFA) :-
    step_wf(epsilon(Marks, Ss), NFA),
    (Mark = beg(Name); Mark = end(Name)),
    (atom(Name); integer(Name)).

%% nfa_wf(+NFA)
%% Vérifie que NFA est une machine valide.
nfa_wf(NFA) :- nfa_wf(NFA, NFA).

%% nfa_wf(+Ss, +NFA)
%% Boucle interne de nfa_wf.
nfa_wf([], _).
nfa_wf([State = Step | Ss], NFA) :-
    %% Chaque état ne peut être défini qu'une seule fois.
    member(State = _, Ss) -> fail;
    step_wf(Step, NFA), nfa_wf(Ss, NFA).

%% nfa_match(+NFA, +Step, +Marks, +Str, -Groups, -Tail)
%% Cette relation est vérifiée si la machine NFA, en partant de Step sur la
%% chaîne Str, peut atteindre un état terminal, auquel cas Tail contient
%% ce qui reste de la chaîne.
%% En d'autres termes, elle consomme des caractères de Str jusqu'à atteindre
%% un état terminal et renvoie le reste non-consommé de la chaîne dans Tail.
%% Marks contient les marques déjà vues, et Groups renvoie les sous-groupes
%% nommés.

append1( [], X, X).                                   % (* your 2nd line *)
append1( [X | Y], Z, [X | W]) :- append( Y, Z, W).    % (* your first line *)


nfa_match(_, success, [], Str, [], Str).
%% !!REMPLIR ICI!!

nfa_match([State = Step | _], step(State), _,_, _,_):-
    Step == success.

nfa_match([State = Step | Steps], step(St), _,[H|T], _,_):-
    St \== State,
    append1(Steps, [State = Step], Temp),
    nfa_match(Temp, step(S), _, [H|T], _,_).

nfa_match([State = [(Char -> St) | Ss] | Steps], step(S), _, [H|T],_,_):-
    S \== State,
    append1(Steps, [State = [(Char -> St) | Ss]], Temp),
    nfa_match(Temp, step(S), _, [H|T], _,_).


nfa_match([State = [(Char -> St) | Ss] | Steps], step(S), _, [H|T],_,_):-
    S == State,
    Char \== H,
    nfa_match([State = Ss | Steps], step(S), _, [H|T], _,_).

nfa_match([State = [(Char -> St) | Ss] | Steps], step(S), _, [H|T],_,_):-
    S == State,
    Char == H,
    append1(Steps, [State = [(Char -> St) | Ss]], Temp),
    nfa_match(Temp, step(St), _, T, _,_).






%% nfa_search_in_chars(+NFA, +Str, -Res)
%% Boucle de recherche, qui essaie de trouver des sous-chaînes acceptées par
%% la machine NFA.
%% Renvoie dans Res la chaîne qui a été acceptée par la NFA, et ses
%% sous-groupes, comme `search_in_chars`.
nfa_search_in_chars(NFA, Str, Res) :-
    %% Le premier état dans la liste est pris comme état initial.
    NFA = [(_State = Step) | _],
    nfa_match(NFA, Step, [], Str, Gs, Tail), append(FoundChars, Tail, Str),
    chars_to_string(FoundChars, Found),
    Res = ['' = Found | Gs].
nfa_search_in_chars(NFA, [_|Str], Res) :-
    nfa_search_in_chars(NFA, Str, Res).

%% nfa_search(+NFA, +Str, -Res)
%% Comme `nfa_search_in_chars` mais avec des "string".
nfa_search(NFA, Str, Res) :-
    string_to_chars(Str, Chars),
    nfa_search_in_chars(NFA, Chars, Res).

%% Exemples de recherches:
%% nfa_search([s0 = success], "hello", Res).
%%   -> devrait renvoyer ['' = ""] 6 fois.
%% nfa_search([s0 = step(s1), s1 = epsilon([], [s0, s2])), s2 = success],
%%            "hello", Res).
%%   -> devrait trouver toutes les sous-chaînes non-vides de "hello".
%% nfa_search([s0 = step([(108 -> s1), (101 -> s1)]),
%%             s1 = epsilon([], [s0, s2]),
%%             s2 = success],
%%            "hello", Res).
%%   -> devrait trouver "ell", "el", "e", "ll", "l", et "l".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% new_state(-State)
%% Crée un nouvel état pas encore utilisé dans NFA.
new_state(State) :- genatom(s, State).

%% re_comp(+RE, +EndState, -BeginState, -NFA)
%% Compile l'expression régulière RE en un NFA dont l'état de départ
%% est BeginState (qui est aussi le premier état de sa liste) et l'état de
%% sortie lorsque RE a été acceptée avec succès est EndState.
re_comp([], S, S, []).
re_comp([RE|REs], E, B, NFA) :-
    re_comp(REs, E, I, NFA2),
    re_comp(RE, I, B, NFA1),
    append(NFA1, NFA2, NFA).
re_comp(any, E, B, [B = step(E)]) :- new_state(B).
re_comp(*(RE), E, B, [B = epsilon([], [B1,E]) | NFA]) :-
    new_state(B), re_comp(RE, B, B1, NFA).
%% Compatibilité pour les Prolog où "String ≠ [Char]".
re_comp(String, E, B, NFA) :-
    "" = [] -> fail;
    string(String), string_chars(String, Chars), re_comp(Chars, E, B, NFA).
%% !!REMPLIR ICI!!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Élimination des cycles d'epsilon infinis
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% !!À COMPLÉTER!!  Le code ci-dessous élimine les cycles d'epsilon
%% mais n'a aucun respect pour les "marques".

%% nfa_epsilons(+NFAi, -NFAo)
%% NFAo est une version "optimisée" de NFAi.
%% L'optimisation consiste à remplacer dans les "epsilon(Ss)" les états
%% qui sont eux-même des epsilons par leurs destinations, de manière à
%% ce qu'il n'y ait plus de chaînes d'epsilon.
%% Le but principal est d'éliminer les *cycles* d'epsilon.
nfa_epsilons(NFAi, NFAo) :- nfa_epsilons(NFAi, NFAi, NFAo).

%% nfa_epsilons(+NFA, +NFAi, -NFAo)
%% Boucle interne.
nfa_epsilons(_, [], []).
nfa_epsilons(NFA, [S = epsilon(_, Ss) | NFA1], [S = epsilon([], Ns) | NFA2]) :-
    !, nfa_epsilons_1(NFA, [S], Ss, Ns),
    nfa_epsilons(NFA, NFA1, NFA2).
nfa_epsilons(NFA, [S | NFA1], [S | NFA2]) :- nfa_epsilons(NFA, NFA1, NFA2).

%% nfa_epsilons_1(+NFA, +Epsilons, +States, -NonEpsilons)
%% Prend un liste d'états `States` et renvoie une liste d'états `NonEpsilons`
%% equivalente mais où les états-epsilon ne sont plus présents.
%% `Epsilons` est la liste des états-epsilon déjà vus.
nfa_epsilons_1(_, _, [], []).
nfa_epsilons_1(NFA, Es, [S|Ss], Ns) :-
    member(S, Es)
    %% Si S est un état-epsilon qu'on a déjà vu, il n'y a rien de nouveau.
    -> nfa_epsilons_1(NFA, Es, Ss, Ns)
    ;  (member(S = epsilon(_, Ss1), NFA)
        %% Un nouvel état-epsilon.
       -> append(Ss1, Ss, Ss2),
          nfa_epsilons_1(NFA, [S|Es], Ss2, Ns)
       ;  nfa_epsilons_1(NFA, Es, Ss, Ns1),
          (member(S, Ns1)
          -> Ns = Ns1
          ;  Ns = [S|Ns1])).

%% re_compile(+RE, -NFA)
%% Point d'entrée pour compiler une expression régulière en une NFA.
re_compile(RE, NFA) :-
        new_state(E),                          % L'état final.
        re_comp(RE, E, B, NFA1),
        %% Élimine les cycle d'epsilon qui peuvent apparaître par exemple
        %% avec `*(RE)` si RE accepte la chaîne vide, comme `*(*("a"))`.
        nfa_epsilons(NFA1, NFA2),
        (B = E; NFA2 = [B = _ | _])
        %% Attention à garder l'état initial B comme premier élément de NFA.
        -> append(NFA2, [E = success], NFA)
        ; write(user_error, re_comp(not(etat_initial = premier_etat))),
          nl(user_error), !, fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% re_search(+RE, +Str, -Res)
%% Boucle de recherche, qui essaie de trouver des sous-chaînes acceptées par
%% l'expression régulière RE en la compilant d'abord vars un NFA.
%% Devrait donner des résultats aussi fidèles que possible
%% à "search(RE, Str, Res)".
re_search(RE, Str, Res) :-
        re_compile(RE, NFA),
        (nfa_wf(NFA)
            -> nfa_search(NFA, Str, Res);
          Res = re_compile_error).
