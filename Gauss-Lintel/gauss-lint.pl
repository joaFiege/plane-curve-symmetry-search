% Gauss-lint algorithms suite. Tested with SWI-Prolog 8.0.3.  
% Implemented by Alexei Lisitsa in collaboration with Alexei Vernitski and Abdullah Khan (2020-2021).
% Further details can be found in accompanying paper A.Khan, A.Lisitsa, A. Vernitski, Experimental Mathematics Approach 
% to Gauss Diagrams Realizability (to appear in arXiv, 2021).
% Under active developemnt. This is a version from 01.03.2021.    
% This work was supported by the Leverhulme Trust Research Project Grant RPG-2019-313.


use_module(lists).


  % "Lintel_generate(N,X)" generates all non-equivalent (wrt rotations and reflections)  lintels of size N/2 and stores all of them as 
  %  dynamic facts "lintel(N,L)"
  %  For that X should be assigned a value = [1,2,...,N/2]. Example: "lintel_generate(8,[1,2,3,4])" will generate   %all non-equivalent lintels of size 4    
  %  assertz(lintel(0,[])) is an initiazliation "ad hoc" trick just to let an ineterpeter/compiler know that   %"lintel/2" will be used as dynamic predicate  

lintel_generate(N,X):-assertz(lintel(0,[])), lintel_gen(N,X,L),not(lintel(N,L)),assertz(lintel(N,L)),fail.
lintel_generate(N,X). 

  % the same for lintels satsifying Biryukov 2 condition 

lintel_generate_B2(N,X):-assertz(lintel(0,[])), lintel_gen(N,X,L),not(lintel(N,L)),not(negBiryukov2(L)),assertz(lintel(N,L)),fail.
lintel_generate_B2(N,X).


  % the same for lintels satisfying Biryukov 2 and 3 conditions    

lintel_generate_B23(N,X):-assertz(lintel(0,[])), lintel_gen(N,X,L),not(lintel(N,L)),not(negBiryukov2(L)),
not(negBiryukov3(L)),
assertz(lintel(N,L)),fail.
lintel_generate_B23(N,X). 

  % the same for *prime* lintels staifying Biryukov 2 and 3 conditions 
  % note that "connected(..)" checks connectendness of the corresponding intersection graph, while 
  % "reducible(..)" checks the fact that the graph remains connected after deleting one of the vertices. 
  % It appears that generally changing these conditions changes the numbers of generated lintels, but not of     
  %lintels satisfying B2-3 conditions (up to N=9)  - it remains 102  for N=9 and either choice 
 
lintel_generate_B23_C(N,X):-assertz(lintel(0,[])), lintel_gen(N,X,L),K is N/2,
                           connected(K,L),
                            %not(reducible(K,L)),    
                            not(lintel(N,L)),
                           not(negBiryukov2(L)),
                           not(negBiryukov3(L)),
                       %    not(negB3(L)), 
                       %     connected(K,L),
                            assertz(lintel(N,L)),fail.
lintel_generate_B23_C(N,X). 

% generation of prime/connected lintels satisfying realisability conditions
lintel_generate_R(N,X):-assertz(lintel(0,[])), lintel_gen(N,X,L),K is N/2,
                           connected(K,L),
                            %not(reducible(K,L)),
                            realizable(N,L),   
                            not(lintel(N,L)),
                            assertz(lintel(N,L)),fail.
lintel_generate_R(N,X). 

lintel_generate_NR(N,X):-assertz(lintel(0,[])), lintel_gen(N,X,L),K is N/2,
                           connected(K,L),
                            %not(reducible(K,L)),
                            not(realizable(N,L)),   
                            not(lintel(N,L)),
                            assertz(lintel(N,L)),fail.
lintel_generate_NR(N,X). 

%% generation of lintels satisfying STZ conditions 
lintel_generate_STZ(N,X):-assertz(lintel_stz(0,[])), lintel_gen(N,X,L),K is N/2,
                           connected(K,L),
                            %not(reducible(K,L)),
                            lintel_to_graph(N,L,G), 
                            realiz_STZ(K,G),   
                            not(lintel_stz(N,L)),
                            assertz(lintel_stz(N,L)),fail.
lintel_generate_STZ(N,X). 


                                         
lintel_generate_ID(N,X):-   assertz(lintel_id(0,[])), lintel_gen(N,X,L),K is N/2,                       
                            connected(K,L),                                    
                            %not(reducible(K,L)),                               
                            lintel_to_graph(N,L,G), 
                            %realiz_STZ(K,G),   
                            graph_matrix_id(K,G),
                            not(lintel_id(N,L)),  
                            assertz(lintel_id(N,L)),fail.
lintel_generate_ID(N,X). 


%% generation of lintels satisfying GL conditions 
lintel_generate_GL(N,X):-   assertz(lintel_gl(0,[])), lintel_gen(N,X,L),K is N/2,                       
                            connected(K,L),                                    
                            %not(reducible(K,L)),                               
                            lintel_to_graph(N,L,G), 
                            not(neg_par(K,G)),
                            not(lintel_gl(N,L)),  
                            assertz(lintel_gl(N,L)),fail.
lintel_generate_GL(N,X). 


%generation of all non-isomoprhic graphs corresponding to a set of lintels recorded by lintel(N,X) facts.
% Naive isomporphism checks, not very efficient. 

graph_generate(N):-assertz(graph(0,[])),lintel(N,L), lintel_to_graph(N,L,G),not(exists_iso(N,G)),assertz(graph(N,G)),fail.
graph_generate(N).



% Given N and X as above, lintel_gen/4,  generates a lintel and then its two canonical representatives wrt to rotations only, one for each of two orientations: 
%"clockwise" and "anticlockwise". Can be used for experiments with "weaker" lintels - equivalence up to rotations only. 
% Not required by any other predicate    

lintel_gen(N,X,L,LL):-permutation(X,Y),odd_gen(X,L1),even_gen(Y,L2),merge(L1,L2,L3),lintel_can(N,L3,L),lintel_can_ref(N,L,LL).  

 % Given N and X as above, lintel_gen/3 generates a lintel and converts it into its canonical representative wrt rotations and reflections  
  % when backtracked over generates all canonical lintels    

lintel_gen(N,X,L):-permutation(X,Y),odd_gen(X,L1),even_gen(Y,L2),merge(L2,L1,L3),
                   %%  lintel_can(N,L3,L),  
                  %% lintel_can_ref(N,L3,L).
                  %% One-sided canonisation  
                  lintel_canonical(N,L3,L).  

%Generation of non-canonical lintels
lintel_gen_NC(N,X,L):-permutation(X,Y),odd_gen(X,L1),even_gen(Y,L2),merge(L1,L2,L).
                  


lintel_g(N,X,L):-permutation(X,Y),odd_gen(X,L1),even_gen(Y,L2),merge(L1,L2,L3),lintel_canonical(N,L3,L),
                 reflect(N,L3,R3),lintel_canonical(N,R3,R),not(L=R).  


% the following predicates "even_gen", "odd_gen" and "merge" are used to implement a bijection between lintels (as sets of %pairs)  of size n and permutations of size n:
% for  a permuation g:[1..n]->[1..n] the corresponding lintel is {{2*i-1,2*g(i)-2}| i in [1..n]}. Together with built-  %in %predicate
% permutation/2 they give an efficient weay of generation of all lintels of size n; see "lintel_gen/3" and "lintel_gen/4" above       

even_gen([X|Y],[XX|YY]):-XX is 2*X-2,even_gen(Y,YY). 
even_gen([],[]).

odd_gen([X|Y],[XX|YY]):-XX is 2*X-1,odd_gen(Y,YY). 
odd_gen([],[]).

merge([X|Y],[XX|YY],[[X,XX]|ZZ]):-merge(Y,YY,ZZ).
merge([],[],[]). 

 
% Given a lintel, say [[X1,X2],[Y1,Y2],...[V1,V2]], "column_ord/2"  sorts it "columnwise", that is each pair   becomes sorted:  [T1,T2] with T1 < T2     
  
column_ord([[X,Y]|T],[[X,Y]|TT]):-X < Y,column_ord(T,TT).
column_ord([[X,Y]|T],[[Y,X]|TT]):-X > Y,column_ord(T,TT).
column_ord([],[]).   

% Given a lintel, "reflect/2" calculates a reflected counterpart lintel 

reflect(N,[[X,Y]|T],[[XX,YY]|TT]):- XX is (N-X) mod N,YY is (N-Y) mod N, reflect(N,T,TT). 
reflect(N,[],[]).  

% Given a lintel, "shift/3" shift it by +1 mod N    

shift(N,[[X,Y]|T],[[XX,YY]|TT]):- XX is (X+1) mod N,YY is (Y+1) mod N, shift(N,T,TT). 
shift(N,[],[]).  

  % lexicographic order on lintels
lintel_less([[X,Y]|T],[[XX,YY]|TT]):-X < XX.
lintel_less([[X,Y]|T],[[X,YY]|TT]):- Y < YY.
lintel_less([[X,Y]|T],[[X,Y]|TT]):-lintel_less(T,TT). 

  % minimal out of two lintels 
lintel_min(X,X,X).
lintel_min(X,Y,X):-lintel_less(X,Y).
lintel_min(X,Y,Y):-lintel_less(Y,X).

  % "sorted/2" sorts a lintel both "vertically" and horizontally". 
  % Uses built-in predicate "sort/4"(SWI-Prolog). Its availability in other Prolog implementations TBC  

sorted(L,LS):- column_ord(L,LO),sort(0,@<,LO,LS).

  % Given a lintel L "lintel_can/3" calculates its canonical representative C wrt rotations (shifts) only. No reflection is taken into account"  
    
lintel_can(N,L,C):-sorted(L,LS),lintel_can(N,N,LS,LS,C). 

  % Technical part of the above canonization process. A lintel is shifted, sorted and compared with a current minimal one, if it is less than current 
  % minimal, then latter is updated. The process is repeated N times and the minimal found lintel comes as a result.       

lintel_can(_,0,C,_,C):-!.
%lintel_can(N,K,LM,L,C):-shift(N,L,LL),sorted(LL,LS),lintel_less(LS,LM),KK is K-1,lintel_can(N,KK,LS,LL,C).
%lintel_can(N,K,LM,L,C):-shift(N,L,LL),sorted(LL,LS),not(lintel_less(LS,LM)),KK is K-1,lintel_can(N,KK,LM,LL,C). 
%lintel_can(N,K,LM,L,C):-shift(N,L,LL),sorted(LL,LS),lintel_min(LS,LM,M),KK is K-1,lintel_can(N,KK,M,LL,C). 
lintel_can(N,K,LM,L,C):-shift(N,L,LL),sorted(LL,LS),lintel_min(LS,LM,M),KK is K-1,lintel_can(N,KK,M,LS,C).  
% Given a lintel L "lintel_can_ref/3" calculates the canonical representative of the reflected L (wrt shifts only)  

lintel_can_ref(N,L,C):-reflect(N,L,LL),
                       lintel_can(N,LL,C). 

  % Given a lintel L "lintel_canonical/3" calculates "true" canonical 
  % representative of L by taking minimal out of two representatives with respect to two orientations  
   
lintel_canonical(N,L,C):-lintel_can(N,L,C1),lintel_can_ref(N,L,C2),lintel_min(C1,C2,C). 

% Intersection predicate for chords
% MinIzinc version: predicate interr(int:i,int:j) = ((r[0,i]< r[0,j]) /\ (r[0,j] < r[1,i]) /\ (r[1,i] < r[1,j]))\/ %((r[0,j]< r[0,i]) /\ (r[0,i] < r[1,j]) /\ (r[1,j] < r[1,i]));
% 
intersect([X,Y],[XX,YY]):- X < XX, XX < Y, Y < YY.
intersect([X,Y],[XX,YY]):- XX < X, X < YY, YY < Y.  

%
%  Retrieve pairs of elements  
%

memb2(X,Y,L):-memb(X,L,LL),memb(Y,LL,_).

% where 

memb(X,[X|T],T).
memb(X,[Y|T],TT):-memb(X,T,TT). 


% Retrieve triples of elements 

memb3(X,Y,Z,L):-memb(X,L,LL),memb(Y,LL,LLL),memb(Z,LLL,_). 



%
% Retrieve pairs of non-intersecting chords from a lintel  
%

non_int_pair(X,Y,L):-memb2(X,Y,L),not(intersect(X,Y)). 

% Retrieve triples of pairwise intersecting chords

inter_triples(X,Y,Z,L):-memb3(X,Y,Z,L),intersect(X,Y),intersect(X,Z),intersect(Y,Z). 


% Chord X intersects both chords Y and Z in lintel L

 intersect_both(X,Y,Z,L):-member(X,L),intersect(X,Y),intersect(X,Z).

% For two chords X and Y in lintel L create a list of chords which intersect them both 

 intersect_both_list(X,Y,L,LL):-findall(Z,intersect_both(Z,X,Y,L),LL). 

% Checking negation of Biryukov condition 2 for a lintel L
negBiryukov2(L):-non_int_pair(X,Y,L),intersect_both_list(X,Y,L,LL),length(LL,N), 1 is mod(N,2). 

%Checking negation of Biryukov condition 3 (AV version)  for a lintel 3

negBiryukov3(L):-inter_triples(X,Y,Z,L), 
                 intersect_both_list(X,Y,L,L1),
                 intersect_both_list(X,Z,L,L2),
                 intersect_both_list(Y,Z,L,L3),  
                 length(L1,N1), length(L2,N2), 
                 length(L3,N3), NN is N1+N2+N3, 0 is mod(NN,2). 



%Checking negation of Biryukov condition 3 (original) for a lintel 

negB3(L):-inter_triples(X,Y,Z,L),
          check_3(X,Y,Z,L).

check_3(X,Y,Z,L):-
          triple_b3_list1(X,Y,Z,L,L2),
          triple_b3_list2(X,Y,Z,L,L3),
          length(L2,N2),length(L3,N3),NN is N2+N3, 1 is mod(NN,2).   

check_3(Y,Z,X,L):-
          triple_b3_list1(X,Y,Z,L,L2),
          triple_b3_list2(X,Y,Z,L,L3),
          length(L2,N2),length(L3,N3),NN is N2+N3, 1 is mod(NN,2).   
check_3(Z,X,Y,L):-
          triple_b3_list1(X,Y,Z,L,L2),
          triple_b3_list2(X,Y,Z,L,L3),
          length(L2,N2),length(L3,N3),NN is N2+N3, 1 is mod(NN,2).   




triple_b3_list1(X,Y,Z,L,L1):-findall(K,intersect_triple1(K,X,Y,Z,L),L1).  
triple_b3_list2(X,Y,Z,L,L2):-findall(K,intersect_triple2(K,X,Y,Z,L),L2).  

intersect_triple1(X,Y,Z,V,L):-member(X,L),not(X=Z),not(X=V),intersect(X,Y),not(intersect(X,Z)),not(intersect(X,V)). 
intersect_triple2(X,Y,Z,V,L):-member(X,L),not(X=Y),not(intersect(X,Y)),intersect(X,Z),intersect(X,V). 



%  Reachable chords

reach_1(X,L):-select(Y,X,_),member(Z,L),intersect(Y,Z).

reach(X,L,LL):-select(Y,X,R),member(Z,L),intersect(Y,Z),reach(R,[Y|L],LL).
reach(X,L,L):-not(reach_1(X,L)).   

% Deterministic predicate for reachable chords
det_reach(X,L,LL):-reach(X,L,LL),!. 


% Checking that all chords are reachable from the first one 
connected(N,[H|T]):-det_reach(T,[H],L), length(L,N).

% Reducibility -- graph remains connected after removing any vertex

reducible(N,L):-select(X,L,R),NN is N-1,not(connected(NN,R)).


% PQ generation of lintels
% 

lintel_PQ(N,XX,L3):-
lintel_pq(N,L),
%lintel(N,L), 
select(P,XX,_), adjust_num(P,L,L1),reconnect_pq(P,L1,L2),NN is N+2,
lintel_canonical(NN,L2,L3).  


lintel_gen_PQ(N,XX):-assertz(lintel_pq(0,[])), NN is N+2, lintel_PQ(N,XX,L),K is N/2,  
                           not(lintel_pq(NN,L)),
                     %      not(negBiryukov2(L)),
                     %      not(negBiryukov3(L)),
                     %       not(negB3(L)), 
                         KK is NN/2,
                          connected(KK,L),
                            assertz(lintel_pq(NN,L)),fail.
lintel_gen_PQ(N,XX).


% all lintels, N is a double size of a lintel, K is normally set to 4 to calculate all lintels up to size N/2 
% can be used for partial computations, starting from already computed lintels of some size either by direct methods, or by %PQ).  Double check that correct version is uncommented in "lintel_PQ" definition above: either lintel_pq(_,_), or lintel%(_,_)   
lin_pq_all(N,K):- lintel_init_pq, lintel_gen_pq(N,K).

% realizable 
lin_pq(N,K):- assertz(lintel_pq(6,[[0,3],[1,4],[2,5]])),lintel_gen_pq(N,K).

lintel_gen_pq(N,N). 
lintel_gen_pq(N,K):- K1 is K-1,numlist(0,K1,XX),lintel_gen_PQ(K,XX),KK is K+2,lintel_gen_pq(N,KK). 


lintel_init_pq:-assertz(lintel_pq(0,[])), lintel_gen(6,[1,2,3],L),not(lintel_pq(6,L)),assertz(lintel_pq(6,L)),fail.
lintel_init_pq.




adjust_num(P,[[X,Y]|T],[[XX,YY]|TT]):- X > P, Y > P, XX is X+2, YY is Y + 2, adjust_num(P,T,TT). 
adjust_num(P,[[X,Y]|T],[[XX,Y]|TT]):- X > P, not(Y > P), XX is X+2, adjust_num(P,T,TT). 
adjust_num(P,[[X,Y]|T],[[X,YY]|TT]):- not(X > P), Y > P, YY is Y + 2, adjust_num(P,T,TT). 
adjust_num(P,[[X,Y]|T],[[X,Y]|TT]):- not(X > P), not(Y > P), adjust_num(P,T,TT).
adjust_num(P,[],[]). 


reconnect_pq(P,L,LL):-P1 is P+1, P2 is P+2, select([X,Y],L,R),add_pq(P1,P2,X,Y,R,LL). 

add_pq(P1,P2,X,Y,R,[[P1,X],[P2,Y]|R]):-1 is (P1+X) mod 2, 1 is (P2+Y) mod 2 .
add_pq(P1,P2,X,Y,R,[[P2,X],[P1,Y]|R]):-1 is (P2+X) mod 2, 1 is (P1+Y) mod 2. 


%gen(N,K,[K|T]):-KK is K+1,gen(N,KK,T).
%gen(N,N,[]). 

%% Translation of Tait format to lintels  

tait_to_lin(N,K,[],[]).
tait_to_lin(N,K,[H|T],[[X,Y]|TT]):-X is K, Y is (K+H) mod N, KK is K+1,tait_to_lin(N,KK,T,TT). 

convert_tait(N):-assertz(lin_tait(0,[])),tait(X),tait_to_lin(N,0,X,L),column_ord(L,L2),list_to_set(L2,L3),lintel_canonical(N,L,C),not(lin_tait(N,C)),assertz(lin_tait(N,C)),fail.


%%%% Immersions calculated by Tait Curves program, N=9

tait([3,5,5,15,7,5,13,13,7,5,13,11,5,3,13,11,15,13]).
tait([3,5,5,15,7,7,13,13,5,7,5,11,11,13,3,13,11,15]).
tait([3,5,5,15,7,7,13,13,7,5,7,11,11,3,13,11,15,11]).
tait([3,5,5,15,7,7,13,13,7,7,3,11,11,15,3,11,11,15]).
tait([3,5,5,15,7,7,13,13,9,5,5,11,11,3,13,13,15,9]).
tait([3,5,5,15,9,7,13,13,3,7,5,15,11,9,3,13,11,15]).
tait([3,5,5,15,9,7,13,13,7,7,7,3,11,9,15,11,11,11]).
tait([3,5,5,15,9,7,13,13,9,5,5,5,11,9,13,13,13,9]).
tait([3,5,5,15,9,7,13,13,9,7,5,3,11,9,15,13,11,9]).
tait([3,5,5,15,9,9,13,13,3,7,5,15,5,9,9,13,11,13]).
tait([3,5,5,15,9,9,13,13,3,7,7,15,3,9,9,15,11,11]).
tait([3,5,5,15,9,9,13,13,7,3,7,5,15,9,9,11,13,11]).
tait([3,5,5,15,9,9,13,13,9,3,5,5,15,9,9,13,13,9]).
tait([3,5,5,15,11,9,13,13,5,3,7,5,15,13,9,7,13,11]).
tait([3,7,5,15,5,9,7,13,11,13,5,5,5,11,9,13,13,13]).
tait([3,7,5,15,5,9,7,13,11,13,7,5,3,11,9,15,13,11]).
tait([3,7,5,15,7,11,7,13,11,5,5,11,5,11,13,13,7,13]).
tait([3,7,5,15,9,5,9,13,11,5,13,5,5,9,13,9,13,13]).
tait([3,7,5,15,9,7,11,13,11,5,5,5,11,9,13,13,13,7]).
tait([3,7,5,15,9,7,11,13,11,7,5,3,11,9,15,13,11,7]).
tait([3,7,5,15,9,9,3,13,11,15,5,5,5,9,9,13,13,13]).
tait([3,7,5,15,9,9,3,13,11,15,7,5,3,9,9,15,13,11]).
tait([3,7,5,15,9,11,5,13,11,5,5,13,5,9,13,13,7,13]).
tait([3,7,5,15,11,5,7,13,11,5,13,5,5,11,13,7,13,13]).
tait([3,7,5,15,13,7,7,13,11,5,5,5,11,11,13,13,13,5]).
tait([3,7,5,15,13,7,7,13,11,7,5,3,11,11,15,13,11,5]).
tait([3,7,7,15,3,9,7,15,11,11,5,5,5,11,9,13,13,13]).
tait([3,7,7,15,3,9,7,15,11,11,7,5,3,11,9,15,13,11]).
tait([3,7,7,15,7,7,9,7,11,11,7,11,11,3,11,9,15,11]).
tait([3,7,7,15,7,9,7,9,11,11,7,11,3,11,9,15,9,11]).
tait([3,7,7,15,7,9,9,3,11,11,15,11,5,3,9,9,15,13]).
tait([3,7,7,15,7,9,9,5,11,11,7,11,13,3,9,9,15,11]).
tait([3,7,7,15,7,11,7,7,11,11,7,11,3,11,11,15,7,11]).
tait([3,7,7,15,9,7,9,9,11,11,7,3,11,9,15,9,9,11]).
tait([3,7,7,15,9,9,5,9,11,11,7,13,3,9,9,15,9,11]).
tait([3,7,7,15,9,9,9,5,11,11,7,5,13,9,9,9,13,11]).
tait([3,7,7,15,11,7,7,7,11,11,7,5,11,11,11,7,13,11]).
tait([3,7,7,15,11,7,7,9,11,11,7,3,11,11,15,7,9,11]).
tait([3,7,7,15,11,9,5,3,11,11,15,13,5,3,9,7,15,13]).
tait([3,7,7,15,11,9,7,5,11,11,7,5,13,11,9,7,13,11]).
tait([3,7,7,15,13,5,7,7,11,11,13,5,3,11,11,15,13,5]).
tait([3,7,7,15,13,7,7,9,11,11,5,3,11,11,15,13,9,5]).
tait([3,9,7,15,3,9,7,15,9,11,9,5,3,11,9,15,13,9]).
tait([3,9,7,15,3,9,9,15,3,11,9,15,5,3,9,9,15,13]).
tait([3,9,7,15,7,3,9,7,15,11,9,11,5,3,11,9,15,13]).
tait([3,9,7,15,7,7,7,9,7,11,9,11,11,11,3,11,9,15]).
tait([3,9,7,15,7,7,9,7,9,11,9,11,11,3,11,9,15,9]).
tait([3,9,7,15,7,7,9,9,5,11,9,11,11,13,3,9,9,15]).
tait([3,9,7,15,7,9,7,9,9,11,9,11,3,11,9,15,9,9]).
tait([3,9,7,15,7,9,9,5,9,11,9,11,13,3,9,9,15,9]).
tait([3,9,7,15,7,9,9,9,5,11,9,11,5,13,9,9,9,13]).
tait([3,9,7,15,7,11,7,7,7,11,9,11,5,11,11,11,7,13]).
tait([3,9,7,15,7,11,9,7,5,11,9,11,5,13,11,9,7,13]).
tait([3,9,7,15,9,7,5,9,7,11,9,13,11,9,3,11,9,15]).
tait([3,9,7,15,9,7,9,9,9,11,9,3,11,9,15,9,9,9]).
tait([3,9,7,15,9,7,11,9,7,11,9,3,11,9,15,11,9,7]).
tait([3,9,7,15,9,9,5,9,9,11,9,13,3,9,9,15,9,9]).
tait([3,9,7,15,9,9,9,5,9,11,9,5,13,9,9,9,13,9]).
tait([3,9,7,15,9,9,9,9,3,11,9,15,5,9,9,9,9,13]).
tait([3,9,7,15,9,11,9,7,3,11,9,15,5,9,11,9,7,13]).
tait([3,9,7,15,11,7,7,7,9,11,9,5,11,11,11,7,13,9]).
tait([3,9,7,15,11,9,7,5,9,11,9,5,13,11,9,7,13,9]).
tait([3,9,7,15,13,7,7,7,7,11,9,5,11,11,11,11,13,5]).
tait([3,9,7,15,13,7,9,7,5,11,9,5,11,13,11,9,13,5]).
tait([3,9,7,15,13,9,7,5,7,11,9,5,13,11,9,11,13,5]).
tait([3,9,7,15,13,9,9,5,3,11,9,15,13,3,9,9,15,5]).
tait([3,9,9,15,3,9,9,15,5,7,9,9,5,13,9,9,11,13]).
tait([3,9,9,15,3,9,9,15,9,3,9,9,15,3,9,9,15,9]).
tait([3,9,9,15,5,9,9,5,9,13,9,9,13,3,9,9,15,9]).
tait([3,9,9,15,5,9,9,9,5,13,9,9,5,13,9,9,9,13]).
tait([3,9,9,15,5,11,7,7,7,13,9,9,5,11,11,11,7,13]).
tait([3,9,9,15,5,11,9,7,5,13,9,9,5,13,11,9,7,13]).
tait([3,9,9,15,9,9,9,9,9,3,9,9,15,9,9,9,9,9]).
tait([3,9,9,15,9,9,11,9,7,3,9,9,15,9,9,11,9,7]).
tait([3,9,9,15,9,11,9,7,9,3,9,9,15,9,11,9,7,9]).
tait([3,9,9,15,11,11,11,5,5,5,9,9,13,13,13,7,7,7]).
tait([3,9,9,15,11,11,11,7,5,3,9,9,15,13,11,7,7,7]).
tait([3,9,9,15,13,7,7,7,7,7,9,9,11,11,11,11,11,5]).
tait([3,9,9,15,13,7,7,9,7,5,9,9,11,11,13,11,9,5]).
tait([3,9,9,15,13,7,9,7,5,7,9,9,11,13,11,9,11,5]).
tait([3,9,9,15,13,9,9,9,5,3,9,9,15,13,9,9,9,5]).
tait([3,9,9,15,13,11,9,5,5,5,9,9,13,13,13,9,7,5]).
tait([3,9,9,15,13,11,9,7,5,3,9,9,15,13,11,9,7,5]).
tait([5,5,5,9,9,13,13,13,9,5,5,5,9,9,13,13,13,9]).
tait([5,5,7,9,11,13,13,7,5,11,7,5,9,13,11,7,13,11]).
tait([5,5,13,9,5,13,13,7,5,13,7,5,9,13,11,5,13,11]).
tait([5,7,11,9,5,13,9,7,11,13,7,5,9,7,11,9,13,11]).
tait([5,9,5,13,9,13,5,13,7,5,9,13,5,9,13,11,5,13]).
tait([5,9,7,11,9,13,5,9,7,11,9,13,5,9,7,11,9,13]).
tait([5,9,9,9,9,13,9,9,9,5,9,9,9,9,13,9,9,9]).
tait([5,9,9,9,9,13,11,7,7,7,9,9,9,9,11,11,11,7]).
tait([5,9,9,9,9,13,11,9,7,5,9,9,9,9,13,11,9,7]).
tait([5,9,11,9,7,13,9,9,9,5,9,11,9,7,13,9,9,9]).
tait([5,9,11,9,7,13,11,7,7,7,9,11,9,7,11,11,11,7]).
tait([5,9,11,9,7,13,11,9,7,5,9,11,9,7,13,11,9,7]).
tait([5,9,13,5,9,13,5,9,13,5,9,13,5,9,13,5,9,13]).
tait([7,9,9,9,9,9,9,11,9,7,9,9,9,9,9,9,11,9]).
tait([7,9,9,9,11,9,7,11,9,7,9,9,9,11,9,7,11,9]).
tait([7,9,9,11,9,7,9,11,9,7,9,9,11,9,7,9,11,9]).
tait([7,11,9,7,11,9,7,11,9,7,11,9,7,11,9,7,11,9]).
tait([9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9]).


%Conversion of lintel into equivalent Gauss words
convert_lin_Gauss(N,L,G):-NN is N-1,numlist(0,NN,XX), con_l_G(XX,L,G). 

con_l_G([X|T],L,[Y|TT]):-memb_min(X,L,Y),con_l_G(T,L,TT).
con_l_G([],L,[]).   


memb_min(X,L,Y):-member([X,Z],L),min(X,Z,Y). 
memb_min(X,L,Y):-member([Z,X],L),min(Z,X,Y). 


min(X,X,X). 
min(X,Y,X):-X < Y. 
min(X,Y,Y):-Y < X. 

% Inversion of the subword W between two occurences of S

invert_between(S,[X|T],[X|I]):-not(X is S), invert_between(S,T,I). 
invert_between(S,[S|T],[S|I]):-invert_prefix(S,T,I). 

invert_prefix(S,T,I):-member_split(S,T,P,R),reverse(P,PP),append([PP,[S],R],I).  

member_split(S,[X|T],[X|P],R):- not(X is S), member_split(S,T,P,R). 
member_split(S,[S|T],[],T). 


iterate_invert([X|T],G,R):-invert_between(X,G,I), 
%write(I),write("\n"),
iterate_invert(T,I,R). 
iterate_invert([],R,R).

between(S,[X|T],B):-not(X is S),between(S,T,B).
between(S,[S|T],B):-between2(S,T,B). 
between2(S,[X|T],[X|B]):-not(X is S),between2(S,T,B). 
between2(S,[S|T],[]). 


%checking interlacement condition 
between_once(S,X,B):-between(S,X,B1),findall(M,member_once(M,B1),B).

% Realiziability condition
realizable(N,L):-convert_lin_Gauss(N,L,G),list_to_set(G,GG),iterate_invert(GG,G,R),generate_graph(GG,R,B),bipart_graph(GG,B,[],[],LL,RR).  

generate_graph([X|T],R,[B|TT]):-between_once(X,R,B),generate_graph(T,R,TT).
generate_graph([],R,[]):-!.

member_once(X,L):-select(X,L,L1),not(select(X,L1,L2)). 
 
sorted_lists([],[]). 
sorted_lists([H|T],[HH|TT]):-sort(0,@<,H,HH),sorted_lists(T,TT).


% checking sublist relation

sublist([H|T],L):-member(H,L),sublist(T,L). 
sublist([],L). 

% checking whther a graph is bipartite
bipart_graph([],[],X,Y,XX,YY):-!,list_to_set(X,XX),list_to_set(Y,YY).
bipart_graph([H|T],[HH|TT],L,R,V,W):-not(member(H,L)),not(sublist(HH,R)),append(HH,L,LL),bipart_graph(T,TT,LL,[H|R],V,W).
bipart_graph([H|T],[HH|TT],L,R,V,W):-not(member(H,R)),not(sublist(HH,L)),append(HH,R,RR),bipart_graph(T,TT,[H|L],RR,V,W).

%given a lintel L compute its interlacement graph
lintel_to_graph(N,L,Gr):-convert_lin_Gauss(N,L,G),list_to_set(G,GG),generate_graph(GG,G,B),
                           NN is N/2-1,numlist(0,NN,NL),
                           merge(GG,NL,LP),ren_list_list(B,LP,G2),sorted_lists(G2,Gr).
                           %,apply_permut(G3,NL,NL,Gr2,Gr).
 
% check if a graph isomorphic to given graph has already been recorded by a fact graph(N,G) 
exists_iso(N,G1):-graph(N,G2),isomorph(N,G1,G2).




% auxiliary predicate to replace the elements of list L using list of pairs of elements 

ren_list([H|T],L,[HH|TT]):-member([H,HH],L),ren_list(T,L,TT).
ren_list([],L,[]). 

% the same as above for a list of lists
ren_list_list([H|T],L,[HH|TT]):-ren_list(H,L,HH),ren_list_list(T,L,TT). 
ren_list_list([],L,[]). 



apply_permut(L,X,Y,LS):-merge(X,Y,Z),ren_list_list(L,Z,LL),sorted_lists(LL,L2),merge(Y,L2,LLL),sort(0,@<,LLL,LS).

%apply_permut2(L,Y,LL)

isomorph(N,G1,G2):-NN is N/2-1,numlist(0,NN,NL),apply_permut(G1,NL,NL,G),permutation(NL,X),apply_permut(G2,NL,X,G).

%
graph_profile(1,[H|T],[L|TT]):-length(H,L),graph_profile(1,T,TT).
graph_profile(1,[],[]). 


graph_prof(1,G,L):-graph_profile(1,G,L1),sort(0,@=<,L1,L).
graph_prof(2,G,L):-length(G,K),graph_degree(K,G,DL),sort_list_list(DL,LL),sort(0,@=<,LL,L). 

sort_list_list([],[]).
sort_list_list([H|T],[HH|TT]):-sort(0,@=<,H,HH),sort_list_list(T,TT).



list_length([],[]). 
list_length([H|T],[HH|TT]):-length(H,HH),list_length(T,TT).

graph_degree(K,G,DL):- KK is K-1,numlist(0,KK,NL),list_length(G,L),merge(NL,L,LL),ren_list_list(G,LL,DL).  

%Check whether a graph matrix is idempotent over GF(2)

graph_matrix_id(N,G):- K is N-1, numlist(0,K,NL), not(neggmi(NL,G)).

neggmi(NL,G):-memb2(X,Y,NL),nth0(X,G,L1),nth0(Y,G,L2),check_id(X,Y,L1,L2).

check_id(X,Y,L1,L2):-member(X,L2),member(Y,L1),intersection(L1,L2,L),length(L,N), 0 is N mod 2.
check_id(X,Y,L1,L2):-not(member(X,L2)),not(member(Y,L1)),intersection(L1,L2,L),length(L,N),1 is N mod 2.


subset([], []).
subset([E|Tail], [E|NTail]):-
  subset(Tail, NTail).
subset([_|Tail], NTail):-
  subset(Tail, NTail). 

% the following is taken from stackoverflow https://stackoverflow.com/questions/8519203/prolog-replace-an-element-in-a-% list-at-a-specified-index;
% complexity requires further investigation  

replace(I, L, E, K) :-
  nth0(I, L, _, R),
  nth0(I, K, E, R).


%% update the graph in a way corresponidng to adding a diagonal matrix to the adjacency matrix 

upd_graph_matr([],G,G):-!.
upd_graph_matr([H|T],G,L):-nth0(H,G,X),replace(H,G,[H|X],G1),upd_graph_matr(T,G1,L). 


%%
realiz_STZ(N,G):- K is N-1, numlist(0,K,NL), subset(NL,S),upd_graph_matr(S,G,GG), graph_matrix_id(N,GG),!.
realiz_STZ(N,G,S):- K is N-1, numlist(0,K,NL), subset(NL,S),upd_graph_matr(S,G,GG), graph_matrix_id(N,GG),!.

% reduction operation from Grinblat-Lopatkin condition 

select_GL(N,G,S,G2):-K is N-1,numlist(0,K,NL),merge(NL,G,GG),select(S,GG,G2).


update_GL(NL,[S,T],G2,GG):-findall([X,Y],memb2(X,Y,T),Z), 
upd_GL_iter(Z,G2,GG).

upd_GL_iter([],G,G).
upd_GL_iter([[X,Y]|T],G,R):-upd_GL(X,Y,G,GG),upd_GL_iter(T,GG,R).


upd_GL(X,Y,G,GG):- nth0(I,G,[X,L]),member(Y,L),
                   nth0(II,G,[Y,LL]),member(X,LL),
                   select(Y,L,L1),replace(I,G,[X,L1],G1),
                   select(X,LL,L2),replace(II,G1,[Y,L2],GG).


upd_GL(X,Y,G,GG):- nth0(I,G,[X,L]),not(member(Y,L)),nth0(II,G,[Y,LL]),not(member(X,LL)),
                   replace(I,G,[X,[Y|L]],G1),replace(II,G1,[Y,[X|LL]],GG).

clean_remove(N,[],[]).
clean_remove(N,[[X,T]|TT],[C|T3]):-select(N,T,C),clean_remove(N,TT,T3).
clean_remove(N,[[X,T]|TT],[T|T3]):-not(member(N,T)),clean_remove(N,TT,T3).


adjust2(N,[],[]).
adjust2(N,[X|T],[X|TT]):- N > X,adjust2(N,T,TT).
adjust2(N,[X|T],[XX|TT]):- N < X, XX is X-1,adjust2(N,T,TT).

adjust2_list(N,[],[]).
adjust2_list(N,[X|T],[XX|TT]):-adjust2(N,X,XX),adjust2_list(N,T,TT). 

% Second parity condition (both GL and B) in terms of graphs  

%parityII

% collect the whole list of non-neighbours 

neighbours(X,Y,G):-nth0(X,G,L),member(Y,L),nth0(Y,G,LL),member(X,LL),X < Y.
% list of neighbours
neighbours_list(G,L):-findall([X,Y],neighbours(X,Y,G),L). 

sym_n(X,Y,G):-neighbours(X,Y,G).
sym_n(X,Y,G):-neighbours(Y,X,G).


nn_memb2(X,Y,T,G):-memb2(X,Y,T),not(neighbours(X,Y,G)).

%list of non-members
nn_list(N,G,L):-K is N-1, numlist(0,K,NL),findall([X,Y],nn_memb2(X,Y,NL,G),L). 

common_n(X,Y,G,Z):-sym_n(X,Z,G),sym_n(Y,Z,G).
common_n_list(X,Y,G,L):-findall(Z,common_n(X,Y,G,Z),L).


parityII(N,G,P):-nn_list(N,G,L),parityII_iter(L,G,P).

parityII_iter([],G).
parityII_iter([[X,Y]|T],G):-common_n_list(X,Y,G,L),length(L,N), 
0 is N mod 2, parityII_iter(T,G).

parityII_iter([],G,[]).
parityII_iter([[X,Y]|T],G,[N|TT]):-common_n_list(X,Y,G,L),length(L,N), 0 is N mod 2, parityII_iter(T,G,TT).


odd_parityII(N,G):-nn_list(N,G,L),odd_check(L,G).
odd_check(L,G):-member([X,Y],L),common_n_list(X,Y,G,LL),length(LL,N),1 is N mod 2. 

neg_par(N,G):-odd_parityII(N,G).
neg_par(N,G):- K is N-1,numlist(0,K,NL),merge(NL,G,GG),select([S,T],GG,G2),update_GL(NL,[S,T],G2,G3),clean_remove(S,G3,G4),adjust2_list(S,G4,G5),sorted_lists(G5,G6),neighbours_list(G6,LL),nn_list(6,G6,L3),odd_parityII(N,G6).


% N is "small" 
neg_parII(N,G):- K is N-1,numlist(0,K,NL),merge(NL,G,GG),select([S,T],GG,G2),update_GL(NL,[S,T],G2,G3),clean_remove(S,G3,G4),adjust2_list(S,G4,G5),sorted_lists(G5,G6),neighbours_list(G6,LL),write(LL),nn_list(6,G6,L3),write("\n"),write(L3),not(parityII(6,G6,P)),write("\n"),write(P).

write_lintels:-open('<path>',write,Str),write_lin(Str). 

write_lin(Str):-lintel(N,L),not(N=0),write(Str,L),write(Str,'\n'),fail.
write_lin(Str):-close(Str). 


write_graphs:-open('<path>',write,Str),write_gr(Str). 

write_gr(Str):-graph(N,L),not(N=0),write(Str,L),write(Str,'\n'),fail.
write_gr(Str):-close(Str). 



%%%%%%%%%%%%%%%%%%%%  DATA %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5%%% 

% "Offensive" facts represent lintels staisfying both B and GL conditions, but not realiziable.  

offensive(10,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,19],[7,14],[8,13],[11,18],[12,17]]).
offensive(10,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,12],[10,17],[11,18],[14,19]]).
offensive(10,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,11],[7,14],[8,15],[12,19],[13,18]]).
offensive(10,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,14],[10,15],[11,18],[12,19]]).
offensive(10,[[0,5],[1,10],[2,15],[3,16],[4,9],[6,13],[7,14],[8,19],[11,18],[12,17]]).
offensive(10,[[0,5],[1,16],[2,15],[3,10],[4,9],[6,19],[7,14],[8,13],[11,18],[12,17]]).


offensive(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,17],[7,14],[8,13],[11,18],[12,19],[15,20]]).
offensive(11,[[0,3],[1,10],[2,9],[4,21],[5,18],[6,17],[7,14],[8,15],[11,16],[12,19],[13,20]]).
offensive(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,12],[10,19],[11,18],[14,21],[17,20]]).
offensive(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,17],[7,14],[8,13],[11,18],[12,19],[16,21]]).
offensive(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,21],[7,14],[8,13],[11,20],[12,19],[15,18]]).
offensive(11,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,14],[10,17],[11,20],[12,21],[13,16]]).
offensive(11,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,17],[11,14],[12,21],[13,20]]).
offensive(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,11],[7,14],[8,15],[12,21],[13,20],[16,19]]).
offensive(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,14],[10,15],[11,20],[12,19],[18,21]]).
offensive(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,15],[11,20],[12,21],[16,19]]).
offensive(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,19],[11,16],[12,21],[15,20]]).
offensive(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,12],[10,19],[11,20],[14,21],[15,18]]).
offensive(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,19],[11,20],[12,15],[16,21]]).
offensive(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,13],[11,20],[12,19],[16,21]]).
offensive(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,15],[7,14],[8,11],[12,19],[13,20],[16,21]]).
offensive(11,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,15],[12,21],[13,20],[14,17]]).
offensive(11,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,12],[10,17],[11,16],[14,21],[15,20]]).
offensive(11,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,15],[7,12],[8,17],[11,16],[13,20],[14,21]]).
offensive(11,[[0,3],[1,10],[2,11],[4,21],[5,18],[6,17],[7,12],[8,15],[9,16],[13,20],[14,19]]).
offensive(11,[[0,3],[1,10],[2,11],[4,21],[5,16],[6,17],[7,20],[8,15],[9,14],[12,19],[13,18]]).
offensive(11,[[0,3],[1,12],[2,11],[4,7],[5,18],[6,17],[8,21],[9,16],[10,15],[13,20],[14,19]]).
offensive(11,[[0,3],[1,10],[2,11],[4,7],[5,18],[6,17],[8,15],[9,14],[12,19],[13,20],[16,21]]).
offensive(11,[[0,3],[1,10],[2,11],[4,7],[5,18],[6,19],[8,15],[9,16],[12,17],[13,20],[14,21]]).
offensive(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,21],[7,16],[8,15],[9,12],[13,20],[14,19]]).
offensive(11,[[0,5],[1,8],[2,9],[3,18],[4,17],[6,13],[7,14],[10,15],[11,20],[12,19],[16,21]]).
offensive(11,[[0,5],[1,8],[2,9],[3,18],[4,17],[6,13],[7,14],[10,21],[11,16],[12,19],[15,20]]).
offensive(11,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,15],[7,14],[10,21],[11,18],[12,19],[13,20]]).
offensive(11,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,15],[7,14],[10,21],[11,20],[12,19],[13,18]]).
offensive(11,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,15],[7,14],[10,19],[11,20],[12,21],[13,18]]).
offensive(11,[[0,5],[1,10],[2,11],[3,16],[4,17],[6,21],[7,20],[8,15],[9,14],[12,19],[13,18]]).
offensive(11,[[0,5],[1,10],[2,17],[3,16],[4,11],[6,21],[7,14],[8,15],[9,20],[12,19],[13,18]]).
offensive(11,[[0,5],[1,8],[2,13],[3,12],[4,9],[6,19],[7,18],[10,17],[11,16],[14,21],[15,20]]).
offensive(11,[[0,5],[1,14],[2,15],[3,10],[4,9],[6,21],[7,16],[8,17],[11,18],[12,19],[13,20]]).
offensive(11,[[0,5],[1,14],[2,15],[3,12],[4,11],[6,21],[7,16],[8,17],[9,18],[10,19],[13,20]]).
offensive(11,[[0,5],[1,14],[2,15],[3,12],[4,11],[6,21],[7,18],[8,17],[9,16],[10,19],[13,20]]).
offensive(11,[[0,5],[1,14],[2,15],[3,12],[4,11],[6,21],[7,16],[8,19],[9,18],[10,17],[13,20]]).


offensive(12,[[0,3],[1,10],[2,11],[4,23],[5,22],[6,19],[7,18],[8,15],[9,16],[12,17],[13,20],[14,21]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,19],[7,18],[8,15],[9,16],[12,17],[13,22],[14,23]]).
offensive(12,[[0,5],[1,12],[2,17],[3,18],[4,11],[6,23],[7,22],[8,15],[9,16],[10,21],[13,20],[14,19]]).
offensive(12,[[0,3],[1,10],[2,11],[4,17],[5,22],[6,21],[7,18],[8,15],[9,14],[12,19],[13,20],[16,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,23],[5,16],[6,21],[7,18],[8,15],[9,14],[12,19],[13,20],[17,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,23],[5,22],[6,17],[7,18],[8,15],[9,14],[12,19],[13,20],[16,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,17],[12,23],[13,22],[14,21],[15,20]]).
offensive(12,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,11],[7,16],[8,17],[12,23],[13,22],[14,19],[15,18]]).
offensive(12,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,21],[7,20],[8,15],[9,18],[10,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,17],[7,20],[8,15],[9,14],[12,21],[13,22],[16,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,23],[5,18],[6,17],[7,22],[8,15],[9,14],[12,21],[13,20],[16,19]]).
offensive(12,[[0,5],[1,10],[2,13],[3,14],[4,9],[6,23],[7,20],[8,19],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,13],[4,9],[5,22],[6,19],[7,18],[8,23],[10,17],[11,16],[14,21],[15,20]]).
offensive(12,[[0,3],[1,12],[2,13],[4,23],[5,8],[6,19],[7,18],[9,22],[10,17],[11,16],[14,21],[15,20]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,15],[7,18],[8,17],[9,16],[12,19],[13,22],[14,23]]).
offensive(12,[[0,5],[1,12],[2,17],[3,18],[4,11],[6,15],[7,16],[8,23],[9,22],[10,21],[13,20],[14,19]]).
offensive(12,[[0,3],[1,10],[2,11],[4,17],[5,20],[6,19],[7,18],[8,15],[9,14],[12,21],[13,22],[16,23]]).
offensive(12,[[0,5],[1,10],[2,17],[3,18],[4,9],[6,15],[7,16],[8,23],[11,22],[12,21],[13,20],[14,19]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,17],[7,16],[8,15],[9,14],[12,21],[13,22],[18,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,23],[7,16],[8,15],[11,22],[12,21],[13,20],[14,19]]).
offensive(12,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,19],[7,20],[8,23],[9,18],[10,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,17],[7,16],[8,13],[9,12],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,17],[7,18],[8,13],[9,12],[14,19],[15,22],[16,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,17],[5,22],[6,19],[7,16],[8,15],[9,12],[13,20],[14,21],[18,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,17],[7,14],[8,13],[9,18],[12,19],[15,22],[16,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,23],[7,16],[8,15],[9,12],[13,22],[14,21],[17,20]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,23],[7,14],[8,13],[11,22],[12,21],[15,20],[16,19]]).
offensive(12,[[0,3],[1,12],[2,11],[4,7],[5,18],[6,19],[8,23],[9,16],[10,15],[13,22],[14,21],[17,20]]).
offensive(12,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,11],[7,14],[8,19],[9,18],[10,15],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,17],[7,16],[8,15],[9,18],[12,19],[13,22],[14,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,23],[5,20],[6,19],[7,16],[8,13],[9,18],[12,17],[14,21],[15,22]]).
offensive(12,[[0,5],[1,18],[2,17],[3,10],[4,9],[6,23],[7,16],[8,15],[11,22],[12,21],[13,20],[14,19]]).
offensive(12,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,23],[7,14],[8,13],[11,20],[12,19],[17,22],[18,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,15],[5,22],[6,17],[7,14],[8,13],[11,20],[12,19],[16,23],[18,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,21],[7,14],[8,13],[11,20],[12,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,23],[5,22],[6,17],[7,18],[8,21],[9,16],[10,15],[13,20],[14,19]]).
offensive(12,[[0,5],[1,12],[2,19],[3,18],[4,13],[6,11],[7,22],[8,17],[9,16],[10,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,10],[2,9],[4,23],[5,20],[6,19],[7,14],[8,13],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,23],[7,22],[8,21],[9,16],[10,15],[13,20],[14,19]]).
offensive(12,[[0,5],[1,18],[2,17],[3,12],[4,11],[6,19],[7,20],[8,23],[9,16],[10,15],[13,22],[14,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,23],[7,16],[8,15],[11,22],[12,21],[13,18],[14,17]]).
offensive(12,[[0,3],[1,10],[2,9],[4,23],[5,18],[6,17],[7,14],[8,13],[11,20],[12,21],[15,22],[16,19]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,11],[7,14],[8,15],[12,21],[13,20],[18,23],[19,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,22],[6,17],[7,14],[8,15],[11,16],[12,21],[13,20],[18,23]]).
offensive(12,[[0,5],[1,8],[2,9],[3,20],[4,19],[6,15],[7,14],[10,23],[11,18],[12,17],[13,22],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,15],[7,14],[10,21],[11,22],[12,17],[13,16],[18,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,23],[5,18],[6,19],[7,14],[8,15],[11,20],[12,17],[13,22],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,15],[7,14],[10,21],[11,18],[12,23],[13,16],[17,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,15],[7,14],[10,21],[11,18],[12,17],[13,22],[16,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,23],[5,22],[6,19],[7,18],[8,13],[9,16],[10,17],[14,21],[15,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,23],[7,18],[8,17],[9,16],[10,15],[13,22],[14,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,11],[7,16],[8,15],[12,23],[13,18],[14,21],[17,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,14],[10,15],[11,22],[12,23],[16,21],[17,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,23],[5,8],[6,19],[7,20],[9,16],[10,17],[13,18],[14,21],[15,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,23],[7,18],[8,17],[9,14],[10,13],[15,22],[16,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,23],[7,18],[8,17],[11,16],[12,15],[13,22],[14,21]]).
offensive(12,[[0,5],[1,8],[2,19],[3,18],[4,9],[6,15],[7,14],[10,23],[11,20],[12,17],[13,22],[16,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,17],[7,12],[8,15],[11,16],[13,22],[14,21],[18,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,23],[7,14],[8,15],[11,22],[12,17],[13,20],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,14],[10,21],[11,16],[12,23],[15,22],[17,20]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,14],[10,17],[11,20],[12,23],[15,22],[16,21]]).
offensive(12,[[0,5],[1,8],[2,9],[3,18],[4,19],[6,17],[7,16],[10,15],[11,20],[12,23],[13,22],[14,21]]).
offensive(12,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,19],[7,20],[8,17],[9,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,9],[5,18],[6,19],[7,16],[8,15],[10,23],[13,20],[14,21],[17,22]]).
offensive(12,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,15],[7,14],[10,21],[11,20],[12,19],[13,22],[18,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,19],[7,16],[8,15],[12,23],[13,20],[14,21],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,15],[7,14],[8,23],[11,22],[12,19],[13,20],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,23],[11,22],[12,19],[13,20],[16,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,19],[7,20],[8,17],[9,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,19],[7,18],[8,13],[9,16],[10,17],[14,23],[15,22]]).
offensive(12,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,15],[7,14],[10,19],[11,22],[12,21],[13,20],[18,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,19],[7,16],[8,15],[12,23],[13,20],[14,21],[17,22]]).
offensive(12,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,21],[7,20],[8,17],[9,18],[14,19],[15,22],[16,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,9],[5,20],[6,19],[7,16],[8,17],[10,23],[13,18],[14,21],[15,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,9],[5,20],[6,19],[7,16],[8,17],[12,23],[13,18],[14,21],[15,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,15],[7,16],[8,23],[11,22],[12,17],[13,20],[14,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,23],[11,22],[12,17],[13,20],[14,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,21],[7,20],[8,17],[9,18],[14,19],[15,22],[16,23]]).
offensive(12,[[0,5],[1,8],[2,9],[3,18],[4,19],[6,17],[7,16],[10,15],[11,22],[12,21],[13,20],[14,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,19],[7,16],[8,17],[12,23],[13,18],[14,21],[15,22]]).
offensive(12,[[0,5],[1,12],[2,19],[3,20],[4,11],[6,17],[7,16],[8,15],[9,18],[10,23],[13,22],[14,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,23],[5,18],[6,19],[7,14],[8,15],[11,16],[12,21],[13,22],[17,20]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,23],[7,14],[8,15],[11,16],[12,21],[13,20],[17,22]]).
offensive(12,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,21],[9,20],[10,17],[11,18],[14,19],[15,22],[16,23]]).
offensive(12,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,15],[9,16],[10,23],[11,22],[12,17],[13,20],[14,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,14],[8,15],[12,23],[13,22],[16,21],[17,20]]).
offensive(12,[[0,5],[1,8],[2,9],[3,18],[4,17],[6,15],[7,14],[10,23],[11,22],[12,19],[13,20],[16,21]]).
offensive(12,[[0,5],[1,12],[2,19],[3,20],[4,11],[6,15],[7,18],[8,17],[9,16],[10,23],[13,22],[14,21]]).
offensive(12,[[0,3],[1,12],[2,13],[4,9],[5,8],[6,19],[7,20],[10,17],[11,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,19],[11,22],[12,21],[13,20],[16,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,14],[10,17],[11,22],[12,21],[13,16],[20,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,19],[7,22],[8,17],[9,16],[12,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,17],[7,16],[10,19],[11,14],[12,23],[13,22],[15,18]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,17],[7,16],[10,15],[11,18],[12,23],[13,22],[14,19]]).
offensive(12,[[0,3],[1,12],[2,11],[4,7],[5,20],[6,19],[8,13],[9,16],[10,17],[14,23],[15,22],[18,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,21],[11,20],[12,19],[13,22],[16,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,19],[7,14],[8,17],[9,18],[12,23],[15,22],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,17],[11,22],[12,21],[13,20],[14,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,13],[7,16],[8,17],[9,22],[12,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,23],[7,12],[8,17],[9,16],[13,18],[14,21],[15,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,23],[7,18],[8,13],[9,16],[12,17],[14,21],[15,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,17],[11,14],[12,21],[13,22],[20,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,21],[7,16],[8,15],[9,22],[12,23],[13,20],[14,19]]).
offensive(12,[[0,5],[1,8],[2,9],[3,12],[4,13],[6,19],[7,20],[10,17],[11,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,7],[5,18],[6,19],[8,15],[9,14],[12,21],[13,22],[16,23],[17,20]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,17],[11,20],[12,23],[13,22],[14,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,15],[7,16],[10,17],[11,14],[12,23],[13,22],[18,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,15],[7,16],[10,13],[11,22],[12,21],[14,17],[18,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,15],[11,22],[12,21],[16,19],[20,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,21],[11,20],[12,15],[16,23],[19,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,14],[10,13],[11,22],[12,21],[16,23],[17,20]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,12],[10,21],[11,20],[14,23],[15,18],[19,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,12],[10,21],[11,20],[14,19],[15,22],[18,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,19],[7,14],[8,17],[9,18],[10,23],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,20],[8,23],[9,16],[10,15],[13,22],[14,21]]).
offensive(12,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,13],[9,16],[10,17],[11,22],[12,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,13],[7,16],[8,17],[9,22],[10,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,17],[5,20],[6,19],[7,18],[8,23],[9,16],[10,15],[13,22],[14,21]]).
offensive(12,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,20],[10,17],[11,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,13],[5,20],[6,19],[7,14],[10,17],[11,18],[12,23],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,23],[5,8],[6,19],[7,18],[9,16],[10,15],[13,20],[14,21],[17,22]]).
offensive(12,[[0,5],[1,8],[2,15],[3,10],[4,13],[6,21],[7,20],[9,14],[11,18],[12,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,11],[7,18],[8,19],[12,17],[13,16],[14,23],[15,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,22],[6,19],[7,16],[8,15],[11,14],[12,21],[13,20],[18,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,13],[7,16],[8,19],[11,18],[12,17],[14,23],[15,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,13],[7,20],[10,21],[11,18],[12,17],[15,22],[16,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,15],[12,21],[13,22],[14,17],[20,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,11],[7,16],[8,15],[12,17],[13,22],[14,21],[18,23]]).
offensive(12,[[0,5],[1,10],[2,9],[3,20],[4,19],[6,11],[7,16],[8,15],[12,21],[13,18],[14,23],[17,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,19],[7,22],[8,17],[9,16],[10,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,23],[7,16],[8,15],[11,14],[12,21],[13,22],[17,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,18],[8,17],[9,16],[10,19],[14,23],[15,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,11],[7,18],[8,17],[12,15],[13,22],[14,23],[16,19]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,16],[8,19],[9,18],[10,17],[14,23],[15,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,20],[8,23],[9,18],[10,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,21],[7,20],[8,15],[9,18],[10,19],[16,23],[17,22]]).
offensive(12,[[0,5],[1,16],[2,17],[3,10],[4,11],[6,23],[7,18],[8,21],[9,14],[12,19],[13,20],[15,22]]).
offensive(12,[[0,5],[1,12],[2,19],[3,20],[4,11],[6,13],[7,14],[8,17],[9,18],[10,23],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,18],[6,19],[7,20],[8,13],[9,16],[10,17],[14,23],[15,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,21],[7,18],[8,13],[9,16],[10,17],[14,23],[15,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,23],[7,14],[8,13],[11,20],[12,21],[15,18],[19,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,15],[7,14],[8,13],[9,18],[10,19],[16,23],[17,22]]).
offensive(12,[[0,5],[1,8],[2,9],[3,14],[4,13],[6,21],[7,20],[10,15],[11,18],[12,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,19],[7,14],[8,17],[9,18],[10,23],[15,22],[16,21]]).
offensive(12,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,19],[7,20],[8,23],[9,18],[10,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,17],[12,15],[13,22],[14,21],[20,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,15],[7,12],[8,17],[11,16],[13,22],[14,21],[20,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,23],[7,16],[8,17],[9,18],[10,15],[13,22],[14,21]]).
offensive(12,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,21],[7,20],[8,15],[9,18],[10,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,15],[7,16],[10,19],[11,18],[12,17],[13,22],[14,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,15],[7,14],[8,11],[12,21],[13,22],[16,23],[17,20]]).
offensive(12,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,19],[7,22],[8,17],[9,16],[10,23],[14,21],[15,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,21],[7,16],[8,15],[9,22],[10,23],[13,20],[14,19]]).
offensive(12,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,12],[10,19],[11,20],[14,23],[17,22],[18,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,13],[7,12],[10,17],[11,18],[14,23],[15,22],[16,19]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,12],[10,21],[11,22],[14,23],[15,20],[16,19]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,12],[10,17],[11,16],[14,21],[15,22],[20,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,23],[7,18],[8,15],[9,16],[10,17],[13,22],[14,21]]).
offensive(12,[[0,5],[1,8],[2,9],[3,20],[4,19],[6,13],[7,12],[10,17],[11,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,5],[1,8],[2,19],[3,20],[4,9],[6,13],[7,14],[10,23],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,5],[1,8],[2,9],[3,20],[4,21],[6,13],[7,12],[10,17],[11,18],[14,19],[15,22],[16,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,15],[7,18],[8,19],[9,14],[10,13],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,15],[7,14],[8,11],[12,19],[13,18],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,15],[7,14],[8,11],[12,21],[13,20],[16,23],[19,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,15],[7,16],[8,11],[12,17],[13,22],[14,23],[18,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,15],[7,16],[8,11],[12,21],[13,18],[14,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,15],[7,12],[8,17],[11,16],[13,22],[14,23],[18,21]]).
offensive(12,[[0,3],[1,10],[2,11],[4,7],[5,20],[6,19],[8,15],[9,16],[12,17],[13,22],[14,23],[18,21]]).
offensive(12,[[0,3],[1,10],[2,11],[4,7],[5,20],[6,19],[8,15],[9,16],[12,21],[13,18],[14,23],[17,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,15],[7,16],[10,19],[11,22],[12,23],[13,18],[14,17]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,13],[7,14],[10,19],[11,18],[12,15],[16,23],[17,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,12],[10,19],[11,20],[14,21],[15,22],[16,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,12],[10,19],[11,20],[14,23],[15,22],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,19],[7,20],[10,23],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,15],[7,20],[8,21],[12,19],[13,18],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,15],[7,20],[8,21],[12,19],[13,18],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,19],[7,20],[8,23],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,15],[7,14],[10,17],[11,22],[12,23],[13,16],[18,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,23],[7,16],[8,15],[11,20],[12,21],[13,22],[14,19]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,23],[7,16],[8,15],[11,22],[12,19],[13,20],[14,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,13],[11,20],[12,21],[16,23],[19,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,14],[10,15],[11,20],[12,21],[18,23],[19,22]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,17],[7,18],[10,19],[11,16],[12,15],[13,22],[14,23]]).
offensive(12,[[0,5],[1,14],[2,11],[3,12],[4,13],[6,19],[7,20],[8,23],[9,18],[10,17],[15,22],[16,21]]).
offensive(12,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,19],[7,20],[8,23],[9,18],[10,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,20],[10,23],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,21],[9,16],[10,15],[11,22],[12,23],[13,20],[14,19]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,13],[7,12],[10,17],[11,16],[14,23],[15,22],[18,21]]).
offensive(12,[[0,3],[1,10],[2,11],[4,7],[5,20],[6,21],[8,15],[9,14],[12,19],[13,18],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,22],[6,17],[7,12],[8,15],[9,16],[13,20],[14,21],[18,23]]).
offensive(12,[[0,5],[1,18],[2,17],[3,10],[4,9],[6,23],[7,16],[8,15],[11,20],[12,21],[13,22],[14,19]]).
offensive(12,[[0,5],[1,18],[2,17],[3,10],[4,9],[6,23],[7,16],[8,15],[11,22],[12,19],[13,20],[14,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,13],[7,12],[10,19],[11,18],[14,17],[15,22],[16,23]]).
offensive(12,[[0,5],[1,14],[2,9],[3,10],[4,13],[6,21],[7,20],[8,15],[11,18],[12,19],[16,23],[17,22]]).
offensive(12,[[0,5],[1,8],[2,9],[3,18],[4,19],[6,13],[7,14],[10,23],[11,20],[12,17],[15,22],[16,21]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,23],[7,16],[8,17],[11,14],[12,21],[13,22],[15,18]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,13],[7,16],[8,17],[9,12],[14,23],[15,22],[18,21]]).
offensive(12,[[0,3],[1,10],[2,11],[4,23],[5,18],[6,19],[7,12],[8,15],[9,16],[13,22],[14,21],[17,20]]).
offensive(12,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,20],[8,23],[9,16],[10,15],[13,22],[14,21]]).
offensive(12,[[0,5],[1,12],[2,19],[3,20],[4,11],[6,15],[7,16],[8,17],[9,18],[10,23],[13,22],[14,21]]).
offensive(12,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,19],[11,20],[12,21],[13,22],[16,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,15],[7,16],[10,17],[11,18],[12,19],[13,22],[14,23]]).
offensive(12,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,21],[9,20],[10,17],[11,18],[14,19],[15,22],[16,23]]).
offensive(12,[[0,5],[1,16],[2,17],[3,10],[4,11],[6,23],[7,18],[8,15],[9,22],[12,19],[13,20],[14,21]]).
offensive(12,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,19],[9,20],[10,23],[11,18],[12,17],[15,22],[16,21]]).
offensive(12,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,21],[9,20],[10,15],[11,18],[12,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,17],[12,23],[13,20],[14,21],[15,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,15],[7,16],[8,17],[9,18],[12,19],[13,22],[14,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,21],[7,22],[8,23],[9,16],[10,15],[13,20],[14,19]]).
offensive(12,[[0,5],[1,14],[2,11],[3,12],[4,13],[6,21],[7,20],[8,15],[9,18],[10,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,23],[7,12],[8,15],[9,16],[13,20],[14,21],[17,22]]).
offensive(12,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,11],[7,14],[8,15],[12,21],[13,22],[16,19],[20,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,17],[12,21],[13,22],[14,23],[15,20]]).
offensive(12,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,19],[9,20],[10,17],[11,16],[14,21],[15,22],[18,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,17],[7,14],[8,15],[9,16],[12,21],[13,22],[18,23]]).
offensive(12,[[0,5],[1,10],[2,17],[3,18],[4,9],[6,15],[7,16],[8,23],[11,20],[12,21],[13,22],[14,19]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,15],[7,16],[8,17],[9,14],[12,21],[13,22],[18,23]]).
offensive(12,[[0,5],[1,10],[2,17],[3,18],[4,9],[6,15],[7,16],[8,23],[11,22],[12,19],[13,20],[14,21]]).
offensive(12,[[0,5],[1,8],[2,9],[3,12],[4,13],[6,21],[7,20],[10,17],[11,18],[14,19],[15,22],[16,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,20],[6,17],[7,16],[10,15],[11,14],[12,21],[13,22],[18,23]]).
offensive(12,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,20],[10,15],[11,18],[12,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,15],[9,14],[10,23],[11,22],[12,19],[13,20],[16,21]]).
offensive(12,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,21],[7,20],[8,15],[9,18],[10,19],[16,23],[17,22]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,16],[8,17],[9,18],[10,19],[14,23],[15,22]]).
offensive(12,[[0,3],[1,10],[2,11],[4,19],[5,20],[6,21],[7,18],[8,15],[9,16],[12,17],[13,22],[14,23]]).
offensive(12,[[0,3],[1,10],[2,11],[4,21],[5,18],[6,19],[7,20],[8,15],[9,16],[12,17],[13,22],[14,23]]).
offensive(12,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,11],[7,16],[8,17],[12,15],[13,22],[14,23],[18,21]]).
offensive(12,[[0,5],[1,8],[2,9],[3,18],[4,19],[6,15],[7,16],[10,23],[11,22],[12,17],[13,20],[14,21]]).
offensive(12,[[0,5],[1,12],[2,17],[3,18],[4,11],[6,15],[7,16],[8,21],[9,22],[10,23],[13,20],[14,19]]).
offensive(12,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,19],[7,20],[8,15],[9,14],[12,21],[13,22],[16,23]]).
offensive(12,[[0,5],[1,8],[2,9],[3,18],[4,19],[6,17],[7,16],[10,15],[11,20],[12,21],[13,22],[14,23]]).
offensive(12,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,15],[7,14],[10,19],[11,20],[12,21],[13,22],[18,23]]).
offensive(12,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,17],[11,20],[12,21],[13,22],[14,23]]).
offensive(12,[[0,5],[1,10],[2,11],[3,16],[4,17],[6,19],[7,20],[8,15],[9,14],[12,21],[13,22],[18,23]]).
offensive(12,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,14],[8,15],[9,18],[10,19],[16,23],[17,22]]).



%non-equivalent prime realisable lintels/Gauss diagrams computed by this program (364) 
lintel_com_s(10,[[0,3],[1,8],[2,7],[4,19],[5,12],[6,11],[9,16],[10,15],[13,18],[14,17]]).

lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,12],[6,11],[9,16],[10,15],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,11],[5,12],[6,19],[9,16],[10,15],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,19],[9,16],[10,15],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,14],[6,13],[9,18],[10,15],[11,16],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,12],[6,13],[10,17],[11,16],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,12],[6,13],[9,16],[10,17],[11,14],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,9],[10,17],[11,16],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,14],[6,13],[9,16],[10,17],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,14],[6,13],[9,18],[10,17],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,19],[9,14],[10,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,19],[9,14],[10,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,16],[6,15],[9,14],[10,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,15],[11,14],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,19],[5,14],[6,15],[9,12],[10,17],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,14],[10,17],[11,16],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,15],[11,18],[12,17],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,17],[11,16],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,17],[11,18],[12,15],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,12],[10,17],[11,16],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,13],[11,18],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,13],[11,18],[12,17],[14,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,13],[11,18],[12,17],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,17],[11,14],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,13],[9,16],[10,17],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,15],[9,16],[10,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,16],[12,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,16],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,14],[12,17],[13,18],[16,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,16],[12,15],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,16],[10,13],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,11],[5,18],[6,13],[9,16],[10,15],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,11],[5,14],[6,17],[9,16],[10,15],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,19],[9,16],[10,15],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,16],[10,15],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,19],[9,18],[10,15],[11,16],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,19],[9,16],[10,17],[11,14],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,9],[10,17],[11,16],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,19],[9,16],[10,17],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,19],[9,18],[10,17],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,18],[10,15],[11,16],[14,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,18],[10,15],[11,16],[12,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,16],[10,17],[11,14],[15,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,12],[10,17],[11,16],[15,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,16],[10,17],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,18],[10,17],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,11],[9,16],[10,17],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,11],[9,16],[10,17],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,11],[9,18],[10,17],[12,15],[16,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,16],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,16],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,18],[10,17],[11,16],[12,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,16],[10,17],[11,18],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,18],[10,17],[11,16],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,18],[10,17],[11,14],[16,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,12],[10,17],[11,18],[16,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,16],[10,19],[11,14],[15,18]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,18],[10,19],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,16],[10,15],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,16],[10,15],[11,18],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,18],[10,15],[11,14],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,9],[10,17],[11,18],[12,15],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,18],[6,11],[9,16],[10,15],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,10],[6,15],[9,14],[11,18],[12,17],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,13],[5,18],[6,15],[9,12],[10,17],[11,16],[14,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,19],[9,16],[10,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,16],[10,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,19],[9,12],[10,17],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,18],[10,13],[11,16],[12,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,12],[10,17],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,18],[10,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,18],[10,17],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,12],[10,19],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,16],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,16],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,18],[10,17],[11,16],[12,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,12],[10,17],[11,18],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,12],[10,17],[11,18],[16,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,12],[10,19],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,14],[10,13],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,13],[11,18],[12,17],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,10],[6,13],[9,14],[11,18],[12,17],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,15],[5,18],[6,13],[9,12],[10,17],[11,16],[14,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,13],[9,14],[10,19],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,13],[9,14],[10,15],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,14],[10,13],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,8],[2,7],[4,17],[5,14],[6,11],[9,16],[10,15],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,11],[7,16],[10,15],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,16],[6,11],[7,14],[10,15],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,10],[6,15],[7,14],[11,18],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,13],[7,18],[10,15],[11,16],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,14],[10,15],[11,16],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,13],[7,18],[10,17],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,13],[7,14],[10,17],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,19],[7,16],[8,15],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,19],[5,16],[6,13],[7,14],[8,15],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,13],[7,18],[8,19],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,13],[7,18],[10,19],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,10],[6,15],[7,14],[11,16],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,11],[7,10],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,11],[7,10],[12,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,11],[7,12],[8,13],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,13],[7,12],[8,11],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,19],[7,12],[8,11],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,19],[5,16],[6,15],[7,12],[8,11],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,17],[7,12],[8,11],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,19],[5,12],[6,15],[7,16],[8,13],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,15],[7,16],[8,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,19],[5,16],[6,15],[7,14],[8,13],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,15],[7,14],[8,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,15],[7,12],[8,17],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,12],[6,17],[7,14],[10,15],[11,16],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,17],[7,12],[10,15],[11,16],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,11],[5,18],[6,15],[7,14],[10,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,13],[10,17],[11,18],[12,15],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,7],[5,14],[6,15],[8,19],[11,16],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,7],[5,14],[6,15],[8,19],[11,18],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,13],[11,18],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,15],[8,11],[12,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,15],[8,11],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,13],[7,16],[8,15],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,13],[7,16],[8,17],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,13],[7,18],[8,17],[12,15],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,15],[7,16],[8,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,15],[7,12],[8,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,15],[7,18],[8,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,11],[5,12],[6,15],[7,16],[10,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,15],[7,12],[10,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,11],[5,14],[6,15],[7,18],[10,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,15],[7,10],[12,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,15],[7,10],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,8],[6,15],[7,16],[12,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,8],[6,15],[7,16],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,15],[7,18],[8,13],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,15],[7,16],[8,13],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,15],[7,16],[8,17],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,15],[7,14],[8,17],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,15],[7,14],[8,17],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,17],[7,16],[8,13],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,14],[8,13],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,16],[8,13],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,17],[7,16],[8,15],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,15],[7,14],[10,19],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,17],[7,18],[8,15],[11,14],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,19],[7,18],[8,17],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,11],[7,16],[10,15],[12,17],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,11],[7,16],[8,17],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,11],[7,18],[8,17],[12,15],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,15],[7,12],[8,19],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,15],[7,16],[8,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,15],[7,14],[8,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,12],[10,19],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,16],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,14],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,15],[7,10],[11,16],[12,17],[14,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,16],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,14],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,12],[10,17],[11,18],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,15],[7,18],[8,11],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,15],[7,16],[8,11],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,15],[7,18],[8,17],[11,14],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,17],[7,18],[8,19],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,12],[6,17],[7,16],[10,19],[11,14],[15,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,17],[7,18],[10,19],[11,16],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,17],[7,14],[10,15],[11,16],[12,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,12],[6,17],[7,16],[10,15],[11,18],[14,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,17],[7,12],[10,15],[11,16],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,17],[7,16],[8,11],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,17],[7,14],[8,11],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,11],[7,18],[8,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,11],[7,18],[10,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,12],[6,11],[7,16],[10,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,13],[7,12],[8,19],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,13],[7,16],[8,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,12],[10,19],[11,18],[14,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,16],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,13],[7,10],[11,16],[12,17],[14,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,16],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,12],[6,13],[7,14],[10,17],[11,18],[16,19]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,12],[10,17],[11,18],[16,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,17],[7,12],[8,19],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,17],[7,12],[10,19],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,14],[10,13],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,14],[8,11],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,11],[7,16],[10,15],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,13],[7,16],[8,19],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,13],[7,16],[10,19],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,14],[10,19],[11,18],[12,15]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,15],[7,12],[8,19],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,12],[10,19],[11,18],[13,16]]).
lintel_com(10,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,14],[10,13],[11,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,15],[7,14],[8,11],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,15],[8,19],[9,12],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,15],[7,12],[8,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,13],[7,14],[8,15],[9,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,13],[7,14],[8,15],[9,16],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,13],[7,16],[8,15],[9,14],[12,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,13],[7,14],[8,15],[9,16],[10,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,13],[7,16],[8,15],[9,14],[10,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,13],[7,16],[8,17],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,16],[8,13],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,13],[7,14],[8,17],[9,16],[10,15]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,13],[9,12],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,15],[7,16],[8,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,17],[7,16],[8,13],[9,12],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,8],[6,15],[7,16],[12,19],[13,18],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,15],[7,16],[8,13],[9,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,15],[7,14],[8,13],[9,18],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,15],[7,14],[8,13],[9,16],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,12],[6,15],[7,16],[8,17],[9,14],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,15],[7,18],[8,19],[12,17],[13,16]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,17],[7,18],[8,13],[9,12],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,17],[7,16],[8,13],[9,12],[14,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,10],[6,15],[7,16],[8,17],[9,14],[13,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,18],[8,19],[9,14],[10,13]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,19],[7,18],[8,17],[9,14],[10,13]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,17],[7,18],[8,15],[9,14],[10,13]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,8],[6,17],[7,16],[10,13],[14,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,8],[6,15],[7,16],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,17],[7,18],[8,13],[9,14],[10,15]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,16],[8,13],[9,14],[10,15]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,12],[6,17],[7,14],[8,15],[9,16],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,19],[5,12],[6,17],[7,16],[8,15],[9,14],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,15],[7,18],[8,13],[9,12],[14,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,10],[6,17],[7,14],[8,15],[9,16],[13,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,10],[6,17],[7,16],[8,15],[9,14],[13,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,15],[5,18],[6,17],[7,16],[8,19],[9,14],[10,13]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,16],[8,15],[9,14],[10,13]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,16],[8,15],[9,14],[10,13]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,18],[8,17],[9,12],[16,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,13],[9,18],[10,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,15],[8,13],[9,18],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,18],[8,17],[9,12],[16,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,17],[9,14],[10,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,7],[5,14],[6,15],[8,17],[9,18],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,15],[8,17],[9,14],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,15],[9,14],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,8],[6,17],[7,16],[9,14],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,15],[7,18],[8,13],[10,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,15],[7,18],[8,13],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,15],[7,16],[8,13],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,15],[7,16],[8,17],[10,19],[13,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,15],[7,14],[8,17],[10,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,15],[7,16],[8,17],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,15],[7,14],[8,17],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,17],[7,18],[8,15],[10,13],[14,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,16],[8,19],[10,13],[15,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,16],[8,13],[10,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,17],[7,16],[9,14],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,17],[7,16],[8,13],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,14],[8,13],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,16],[8,15],[10,19],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,17],[7,16],[8,15],[12,19],[13,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,9],[5,18],[6,17],[7,16],[8,15],[10,13],[14,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,18],[8,15],[9,16],[10,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,9],[7,16],[8,17],[12,19],[15,18]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,16],[8,17],[9,18],[10,15]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,18],[8,17],[9,16],[10,15]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,17],[7,16],[8,19],[9,12],[15,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,8],[6,15],[7,16],[9,18],[12,19],[14,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,10],[8,19],[9,18],[14,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,16],[8,19],[9,18],[10,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,14],[8,19],[9,18],[10,17]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,16],[8,17],[9,18],[10,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,18],[8,17],[9,16],[10,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,15],[7,16],[8,17],[9,14],[10,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,16],[8,17],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,18],[8,17],[9,16],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,15],[7,14],[8,17],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,15],[7,16],[8,17],[9,14],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,15],[7,16],[8,17],[9,12],[14,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,18],[8,19],[9,16],[10,15]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,16],[8,15],[9,18],[10,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,17],[7,14],[8,15],[9,16],[10,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,18],[8,15],[9,14],[10,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,17],[7,16],[8,15],[9,14],[10,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,17],[7,16],[8,15],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,14],[8,15],[9,16],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,17],[7,18],[8,15],[9,14],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,16],[8,15],[9,14],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,17],[7,18],[8,15],[9,12],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,16],[8,15],[9,12],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,19],[7,18],[8,13],[9,16],[12,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,19],[7,12],[8,17],[9,16],[13,18]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,9],[7,18],[8,17],[12,19],[13,16]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,16],[8,19],[9,18],[10,17]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,16],[8,17],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,18],[8,17],[9,16],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,13],[7,12],[8,17],[9,16],[14,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,17],[7,14],[8,13],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,16],[8,13],[9,14],[10,15]]).
lintel_com(10,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,14],[8,15],[9,16],[10,13]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,13],[7,14],[8,15],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,17],[5,14],[6,15],[7,16],[8,13],[9,18],[12,19]]).
lintel_com(10,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,15],[7,14],[8,13],[9,18],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,11],[3,18],[4,13],[7,14],[8,15],[9,16],[10,17],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,11],[3,18],[4,13],[7,16],[8,15],[9,14],[10,17],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,13],[3,18],[4,11],[7,14],[8,15],[9,16],[10,17],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,13],[3,18],[4,11],[7,16],[8,15],[9,14],[10,17],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,11],[3,18],[4,13],[7,14],[8,17],[9,16],[10,15],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,13],[3,18],[4,11],[7,14],[8,17],[9,16],[10,15],[12,19]]).
lintel_com(10,[[0,5],[1,14],[2,7],[3,16],[4,9],[6,13],[8,15],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,14],[2,7],[3,16],[4,9],[6,13],[8,15],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,10],[4,11],[8,15],[9,16],[12,17],[13,18],[14,19]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,19],[9,18],[10,15],[11,16],[12,17]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,15],[9,16],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,15],[9,16],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,15],[9,18],[10,17],[11,16],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,15],[9,16],[10,17],[11,18],[14,19]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,15],[9,18],[10,17],[11,16],[14,19]]).
lintel_com(10,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,17],[9,16],[10,15],[11,18],[14,19]]).
lintel_com(10,[[0,5],[1,8],[2,11],[3,18],[4,15],[6,13],[7,12],[9,16],[10,17],[14,19]]).
lintel_com(10,[[0,5],[1,8],[2,15],[3,18],[4,11],[6,13],[7,14],[9,16],[10,17],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,9],[3,16],[4,13],[7,14],[8,15],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,13],[3,16],[4,9],[7,14],[8,15],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,6],[2,9],[3,16],[4,13],[7,14],[8,15],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,6],[2,13],[3,16],[4,9],[7,14],[8,15],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,8],[2,17],[3,10],[4,15],[6,13],[7,12],[9,16],[11,18],[14,19]]).
lintel_com(10,[[0,5],[1,14],[2,9],[3,16],[4,11],[6,13],[7,18],[8,17],[10,15],[12,19]]).
lintel_com(10,[[0,5],[1,8],[2,9],[3,12],[4,13],[6,15],[7,16],[10,17],[11,18],[14,19]]).
lintel_com(10,[[0,5],[1,10],[2,13],[3,8],[4,15],[6,19],[7,16],[9,14],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,12],[2,15],[3,16],[4,11],[6,13],[7,14],[8,17],[9,18],[10,19]]).
lintel_com(10,[[0,5],[1,8],[2,9],[3,14],[4,13],[6,17],[7,16],[10,15],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,12],[2,15],[3,16],[4,11],[6,13],[7,14],[8,19],[9,18],[10,17]]).
lintel_com(10,[[0,5],[1,10],[2,9],[3,14],[4,15],[6,19],[7,16],[8,13],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,8],[2,9],[3,16],[4,15],[6,13],[7,12],[10,17],[11,18],[14,19]]).
lintel_com(10,[[0,5],[1,8],[2,15],[3,10],[4,13],[6,17],[7,16],[9,14],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,8],[2,17],[3,16],[4,9],[6,13],[7,12],[10,15],[11,18],[14,19]]).
lintel_com(10,[[0,5],[1,8],[2,9],[3,16],[4,17],[6,13],[7,14],[10,15],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,8],[2,15],[3,16],[4,9],[6,13],[7,14],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,5],[1,8],[2,15],[3,16],[4,9],[6,13],[7,14],[10,19],[11,18],[12,17]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,19],[7,18],[8,15],[9,16],[10,17]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,17],[7,18],[8,19],[9,16],[10,15]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,19],[7,18],[8,17],[9,16],[10,15]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,17],[7,16],[8,15],[9,18],[10,19]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,15],[7,16],[8,17],[9,18],[10,19]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,15],[7,18],[8,17],[9,16],[10,19]]).
lintel_com(10,[[0,5],[1,10],[2,11],[3,12],[4,13],[6,15],[7,16],[8,17],[9,18],[14,19]]).
lintel_com(10,[[0,5],[1,10],[2,11],[3,12],[4,13],[6,15],[7,18],[8,17],[9,16],[14,19]]).
lintel_com(10,[[0,5],[1,12],[2,11],[3,10],[4,13],[6,15],[7,18],[8,17],[9,16],[14,19]]).
lintel_com(10,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,15],[7,16],[8,19],[9,18],[10,17]]).
lintel_com(10,[[0,5],[1,10],[2,11],[3,12],[4,13],[6,17],[7,16],[8,15],[9,18],[14,19]]).
lintel_com(10,[[0,5],[1,10],[2,13],[3,12],[4,11],[6,15],[7,18],[8,17],[9,16],[14,19]]).
lintel_com(10,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,19],[7,18],[8,15],[9,16],[10,17]]).
lintel_com(10,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,17],[7,18],[8,19],[9,16],[10,15]]).
lintel_com(10,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,19],[7,18],[8,17],[9,16],[10,15]]).
lintel_com(10,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,15],[7,16],[8,19],[9,18],[10,17]]).
lintel_com(10,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,15],[7,16],[8,17],[9,18],[10,19]]).
lintel_com(10,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,15],[7,18],[8,17],[9,16],[10,19]]).
lintel_com(10,[[0,5],[1,10],[2,13],[3,12],[4,11],[6,17],[7,16],[8,15],[9,18],[14,19]]).
lintel_com(10,[[0,5],[1,14],[2,15],[3,10],[4,11],[6,13],[7,16],[8,17],[9,18],[12,19]]).
lintel_com(10,[[0,5],[1,14],[2,15],[3,10],[4,11],[6,13],[7,18],[8,17],[9,16],[12,19]]).
lintel_com(10,[[0,5],[1,8],[2,15],[3,10],[4,17],[6,13],[7,14],[9,16],[11,18],[12,19]]).
lintel_com(10,[[0,7],[1,14],[2,9],[3,16],[4,11],[5,18],[6,13],[8,15],[10,17],[12,19]]).
lintel_com(10,[[0,7],[1,8],[2,9],[3,14],[4,15],[5,16],[6,13],[10,17],[11,18],[12,19]]).
lintel_com(10,[[0,7],[1,8],[2,9],[3,16],[4,15],[5,14],[6,13],[10,17],[11,18],[12,19]]).

% Non-equivalent prime realizable lintels/Gauss diagrams generated by this progream (1610 of them) 
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,14],[12,19],[13,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,12],[6,11],[9,16],[10,17],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,12],[6,11],[9,16],[10,17],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,13],[9,12],[10,17],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,21],[11,18],[12,17],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,12],[6,13],[9,14],[10,17],[11,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,12],[6,13],[9,18],[10,17],[11,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,12],[6,13],[9,16],[10,17],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,12],[6,13],[9,20],[10,17],[11,16],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,12],[10,17],[11,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,18],[10,17],[11,20],[12,15],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,20],[10,17],[11,18],[12,15],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,16],[10,17],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,18],[10,17],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,21],[9,20],[10,17],[11,16],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,16],[10,19],[11,18],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,18],[10,19],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,13],[9,16],[10,19],[11,18],[12,17],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,21],[9,20],[10,17],[11,16],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,9],[10,21],[11,18],[12,17],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,18],[6,17],[10,21],[11,16],[12,15],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,16],[10,13],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,14],[10,13],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,18],[10,13],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,20],[10,13],[11,18],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,12],[10,17],[11,18],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,16],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,16],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,18],[10,17],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,20],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,14],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,14],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,16],[6,21],[9,20],[10,15],[11,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,12],[10,19],[11,18],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,12],[10,19],[11,18],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,12],[10,19],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,16],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,20],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,18],[10,19],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,14],[6,15],[9,20],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,15],[9,14],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,21],[9,20],[10,15],[11,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,17],[9,14],[10,13],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,17],[9,14],[10,13],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,19],[9,18],[12,17],[13,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,18],[6,17],[9,14],[10,15],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,15],[9,14],[10,21],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,17],[9,18],[10,15],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,16],[6,17],[9,20],[10,15],[11,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,21],[5,18],[6,17],[9,16],[10,15],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,15],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,17],[11,18],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,12],[6,13],[10,17],[11,18],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,12],[6,13],[10,17],[11,18],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,16],[12,17],[13,20],[14,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,11],[9,16],[10,15],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,13],[10,19],[11,18],[12,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,21],[11,18],[12,17],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,20],[10,15],[11,18],[12,17],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,21],[11,20],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,21],[11,16],[12,19],[13,18],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,21],[11,18],[12,19],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,21],[11,14],[12,19],[13,18],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,21],[11,18],[12,19],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,21],[11,20],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,13],[11,18],[12,19],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,13],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,13],[11,20],[12,19],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,17],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,17],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,17],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,17],[11,18],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,17],[11,20],[12,19],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,17],[11,20],[12,19],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,17],[11,14],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,19],[11,18],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,19],[11,20],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,15],[10,19],[11,18],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,19],[11,18],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,14],[6,15],[10,19],[11,20],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,21],[11,18],[12,15],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,20],[10,13],[11,18],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,21],[11,14],[12,19],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,21],[11,14],[12,19],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,13],[11,20],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,13],[11,20],[12,19],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,18],[6,17],[10,15],[11,14],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,15],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,15],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,15],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,18],[6,17],[10,15],[11,14],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,15],[11,14],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,16],[6,17],[10,19],[11,14],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,18],[6,17],[10,19],[11,16],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,18],[12,15],[13,20],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,13],[9,16],[10,15],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,18],[6,19],[10,15],[11,16],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,9],[5,18],[6,19],[10,17],[11,16],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,16],[12,19],[13,18],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,12],[6,21],[9,16],[10,17],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,12],[6,21],[9,16],[10,17],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,15],[9,12],[10,17],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,16],[12,21],[13,18],[14,19],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,21],[9,16],[10,17],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,21],[9,16],[10,17],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,21],[9,18],[10,17],[13,16],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,13],[9,18],[10,17],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,13],[9,18],[10,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,13],[9,16],[10,17],[14,19],[15,20],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,13],[9,18],[10,19],[14,17],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,15],[9,16],[10,21],[13,18],[14,19],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,15],[9,16],[12,19],[13,20],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,15],[9,20],[10,17],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,16],[10,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,16],[10,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,18],[10,21],[13,16],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,16],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,16],[12,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,18],[12,21],[13,16],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,18],[12,15],[13,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,16],[12,15],[13,20],[14,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,16],[12,19],[13,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,10],[8,17],[9,18],[12,19],[13,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,18],[10,13],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,18],[10,13],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,16],[10,13],[14,19],[15,20],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,20],[10,15],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,17],[9,14],[10,19],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,19],[9,18],[10,13],[14,17],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,11],[5,12],[8,19],[9,14],[10,17],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,20],[6,13],[9,16],[10,17],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,18],[6,15],[9,16],[10,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,18],[6,15],[9,16],[10,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,14],[6,17],[9,16],[10,15],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,14],[6,19],[9,16],[10,17],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,11],[5,16],[6,19],[9,18],[10,17],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,21],[9,14],[10,17],[11,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,21],[9,18],[10,17],[11,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,21],[9,16],[10,17],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,12],[10,17],[11,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,18],[10,17],[11,20],[12,15],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,20],[10,17],[11,18],[12,15],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,16],[10,17],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,18],[10,17],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,20],[10,17],[11,16],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,16],[10,19],[11,18],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,18],[10,19],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,21],[9,16],[10,19],[11,18],[12,17],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,20],[10,17],[11,16],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,21],[9,14],[10,17],[11,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,21],[9,18],[10,17],[11,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,21],[9,16],[10,17],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,12],[10,17],[11,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,18],[10,17],[11,20],[12,15],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,20],[10,17],[11,18],[12,15],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,16],[10,17],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,18],[10,17],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,16],[10,19],[11,18],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,18],[10,19],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,16],[10,19],[11,18],[12,17],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,21],[9,20],[10,19],[11,16],[12,17],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,11],[9,18],[10,17],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,11],[9,18],[10,17],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,11],[9,18],[10,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,11],[9,18],[10,19],[14,17],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,11],[9,18],[10,19],[12,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,16],[10,21],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,18],[10,17],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,20],[10,17],[11,18],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,18],[10,17],[11,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,20],[10,17],[11,18],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,20],[10,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,16],[10,17],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,16],[10,19],[11,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,18],[10,19],[11,16],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,16],[10,19],[11,18],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,18],[10,19],[11,16],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,15],[9,18],[10,19],[11,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,12],[10,19],[11,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,18],[10,19],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,20],[10,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,15],[9,16],[10,19],[11,20],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,18],[10,21],[11,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,16],[10,21],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,18],[10,15],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,18],[10,15],[11,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,16],[10,15],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,16],[10,19],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,18],[10,19],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,16],[10,19],[11,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,17],[9,18],[10,19],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,18],[10,19],[11,20],[12,15],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,20],[10,19],[11,18],[12,15],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,17],[9,20],[10,19],[11,16],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,18],[10,21],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,20],[10,21],[11,16],[12,17],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,18],[10,15],[11,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,20],[10,15],[11,16],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,20],[10,15],[11,16],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,16],[10,17],[11,18],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,16],[10,17],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,18],[10,17],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,16],[10,17],[11,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,16],[10,17],[11,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,12],[8,19],[9,18],[10,17],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,18],[10,17],[11,20],[12,15],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,13],[5,14],[8,19],[9,20],[10,17],[11,16],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,9],[10,15],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,9],[10,17],[11,18],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,9],[10,17],[11,18],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,12],[6,9],[10,17],[11,18],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,11],[9,16],[10,15],[12,21],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,14],[6,9],[10,19],[11,18],[12,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,20],[6,11],[9,16],[10,17],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,10],[6,15],[9,14],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,20],[6,15],[9,12],[10,17],[11,18],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,20],[6,15],[9,16],[10,17],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,20],[6,15],[9,18],[10,17],[11,16],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,20],[6,15],[9,16],[10,19],[11,18],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,13],[5,16],[6,19],[9,12],[10,17],[11,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,21],[11,18],[12,17],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,16],[10,13],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,14],[10,13],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,18],[10,13],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,20],[10,13],[11,18],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,12],[10,17],[11,18],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,16],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,16],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,18],[10,17],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,20],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,14],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,14],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,20],[10,17],[11,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,12],[10,19],[11,18],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,12],[10,19],[11,18],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,12],[10,19],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,16],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,20],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,18],[10,19],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,21],[9,20],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,21],[9,14],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,20],[10,17],[11,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,20],[10,13],[11,18],[12,17],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,16],[10,13],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,14],[10,13],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,18],[10,13],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,20],[10,13],[11,18],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,12],[10,17],[11,18],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,16],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,16],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,18],[10,17],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,20],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,14],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,14],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,12],[10,19],[11,18],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,12],[10,19],[11,18],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,12],[10,19],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,16],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,20],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,18],[10,19],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,21],[9,20],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,14],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,21],[9,20],[10,19],[11,14],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,20],[10,21],[12,17],[13,18],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,11],[9,20],[10,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,11],[9,20],[10,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,11],[9,18],[10,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,11],[9,18],[10,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,18],[10,17],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,18],[10,19],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,11],[9,20],[10,19],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,11],[9,18],[10,19],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,18],[10,19],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,11],[9,20],[10,19],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,16],[10,21],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,18],[10,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,18],[10,17],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,20],[10,17],[11,18],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,20],[10,17],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,20],[10,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,16],[10,17],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,16],[10,19],[11,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,18],[10,19],[11,16],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,18],[10,19],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,20],[10,19],[11,18],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,12],[10,19],[11,18],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,12],[10,19],[11,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,12],[10,19],[11,20],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,18],[10,19],[11,20],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,13],[9,20],[10,19],[11,18],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,18],[10,19],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,20],[10,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,13],[9,16],[10,19],[11,20],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,18],[10,21],[11,20],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,14],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,14],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,18],[10,21],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,18],[10,13],[11,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,18],[10,13],[11,20],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,20],[10,13],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,18],[10,13],[11,20],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,20],[10,13],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,14],[10,13],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,18],[10,19],[11,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,20],[10,19],[11,18],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,14],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,18],[10,19],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,12],[10,19],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,17],[9,12],[10,19],[11,20],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,12],[10,19],[11,18],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,12],[10,19],[11,20],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,17],[9,12],[10,19],[11,20],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,19],[9,12],[10,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,20],[10,21],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,20],[10,21],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,19],[9,20],[10,21],[11,14],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,20],[10,13],[11,16],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,18],[10,17],[11,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,19],[9,18],[10,17],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,16],[8,19],[9,12],[10,17],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,15],[5,14],[8,19],[9,12],[10,17],[11,18],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,21],[11,20],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,21],[11,18],[12,19],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,21],[11,14],[12,19],[13,18],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,21],[11,18],[12,19],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,21],[11,20],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,13],[11,18],[12,19],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,13],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,13],[11,20],[12,19],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,17],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,17],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,17],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,17],[11,18],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,17],[11,20],[12,19],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,17],[11,20],[12,19],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,19],[11,18],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,16],[6,9],[10,19],[11,20],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,19],[11,18],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,14],[6,9],[10,19],[11,20],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,18],[6,11],[9,16],[10,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,18],[6,11],[9,16],[10,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,10],[6,13],[9,14],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,20],[6,13],[9,12],[10,17],[11,18],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,20],[6,13],[9,16],[10,17],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,20],[6,13],[9,18],[10,17],[11,16],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,20],[6,13],[9,16],[10,19],[11,18],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,10],[6,17],[9,16],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,10],[6,17],[9,16],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,10],[6,17],[9,16],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,10],[6,17],[9,16],[11,14],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,20],[6,17],[9,14],[10,13],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,12],[6,19],[9,16],[10,17],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,15],[5,12],[6,19],[9,18],[10,17],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,16],[6,21],[9,14],[10,13],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,16],[6,21],[9,14],[10,13],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,18],[6,21],[9,14],[10,15],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,15],[9,14],[10,17],[11,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,16],[6,21],[9,18],[10,15],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,18],[6,21],[9,16],[10,15],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,21],[9,14],[10,13],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,21],[9,14],[10,13],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,21],[9,14],[10,15],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,21],[9,14],[10,15],[11,20],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,21],[9,18],[10,15],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,21],[9,16],[10,15],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,13],[9,12],[10,21],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,13],[9,14],[10,19],[11,20],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,14],[10,21],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,14],[10,15],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,20],[10,15],[11,16],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,20],[10,15],[11,16],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,14],[10,15],[11,20],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,13],[9,14],[10,15],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,14],[10,19],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,13],[9,12],[10,19],[11,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,13],[9,14],[10,19],[11,20],[12,15],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,14],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,14],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,18],[10,21],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,15],[9,14],[10,13],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,18],[10,13],[11,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,18],[10,13],[11,20],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,20],[10,13],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,15],[9,14],[10,13],[11,20],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,14],[10,13],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,14],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,18],[10,19],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,12],[10,19],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,15],[9,12],[10,19],[11,20],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,16],[8,19],[9,14],[10,13],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,19],[9,14],[10,15],[11,16],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,19],[9,14],[10,15],[11,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,17],[5,18],[8,19],[9,16],[10,15],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,14],[6,11],[9,16],[10,15],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,10],[6,15],[9,16],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,10],[6,15],[9,16],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,10],[6,15],[9,16],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,10],[6,15],[9,16],[11,14],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,20],[6,15],[9,14],[10,13],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,17],[5,10],[6,19],[9,18],[11,16],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,11],[9,16],[10,17],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,15],[9,16],[10,13],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,15],[9,16],[10,17],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,17],[9,14],[10,15],[11,16],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,6],[2,7],[4,19],[5,18],[8,17],[9,16],[10,15],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,19],[5,14],[6,11],[9,16],[10,17],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,19],[5,16],[6,11],[9,18],[10,17],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,19],[5,16],[6,13],[9,12],[10,17],[11,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,19],[5,12],[6,15],[9,16],[10,17],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,19],[5,12],[6,15],[9,18],[10,17],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,7],[4,19],[5,10],[6,17],[9,18],[11,16],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,11],[7,16],[8,15],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,11],[7,16],[8,15],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,13],[10,17],[11,18],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,12],[6,13],[10,17],[11,18],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,17],[7,12],[8,11],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,20],[6,15],[7,12],[8,11],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,13],[7,18],[8,15],[11,16],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,12],[6,13],[7,14],[10,19],[11,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,19],[7,16],[8,15],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,12],[6,13],[7,16],[8,17],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,13],[7,12],[8,17],[11,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,18],[6,13],[7,12],[8,17],[11,16],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,13],[7,20],[8,19],[11,16],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,13],[7,18],[8,17],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,10],[6,15],[7,16],[11,20],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,13],[10,15],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,10],[6,15],[7,16],[11,18],[12,19],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,10],[6,15],[7,16],[11,20],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,11],[7,10],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,13],[11,18],[12,19],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,11],[7,10],[12,19],[13,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,11],[7,10],[12,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,18],[6,17],[10,19],[11,16],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,18],[6,19],[10,17],[11,16],[12,15],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,12],[6,15],[7,18],[10,17],[11,16],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,18],[6,15],[7,12],[10,17],[11,16],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,14],[6,15],[7,20],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,15],[7,14],[10,17],[11,18],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,14],[6,15],[7,20],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,14],[6,15],[7,20],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,15],[7,14],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,21],[5,20],[6,15],[7,14],[10,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,8],[6,15],[7,16],[11,20],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,13],[10,19],[11,18],[12,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,8],[6,15],[7,16],[11,18],[12,19],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,8],[6,15],[7,16],[11,20],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,17],[7,12],[8,11],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,13],[7,12],[8,11],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,17],[7,12],[8,11],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,13],[7,12],[8,11],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,15],[7,18],[8,13],[11,16],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,12],[10,19],[11,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,12],[10,19],[11,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,15],[7,18],[8,13],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,18],[6,15],[7,16],[8,13],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,15],[7,12],[8,17],[11,16],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,15],[7,16],[8,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,15],[7,16],[8,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,15],[7,14],[8,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,15],[7,14],[8,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,15],[7,14],[8,21],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,19],[7,16],[10,15],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,12],[6,15],[7,16],[8,19],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,15],[7,12],[8,19],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,15],[7,18],[8,19],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,15],[7,14],[8,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,18],[6,15],[7,14],[8,19],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,15],[7,14],[8,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,18],[6,17],[10,15],[11,14],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,15],[11,14],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,18],[6,17],[10,15],[11,14],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,21],[7,12],[8,11],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,21],[7,12],[8,11],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,17],[7,12],[8,11],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,17],[7,12],[8,11],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,12],[6,17],[7,16],[8,13],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,17],[7,16],[8,13],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,16],[6,17],[7,14],[8,13],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,17],[7,12],[8,15],[11,16],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,17],[7,16],[8,15],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,17],[7,16],[8,15],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,14],[10,21],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,16],[6,17],[7,18],[10,15],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,17],[7,16],[10,15],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,19],[7,12],[8,11],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,17],[7,12],[8,11],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,19],[7,18],[8,13],[11,16],[12,17],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,12],[6,19],[7,16],[8,15],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,19],[7,18],[8,15],[11,16],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,20],[6,19],[7,14],[8,15],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,21],[5,14],[6,19],[7,12],[8,17],[11,16],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,12],[6,13],[10,17],[11,18],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,15],[8,21],[11,20],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,19],[11,18],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,15],[8,21],[11,18],[12,19],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,15],[8,21],[11,20],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,21],[11,20],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,21],[11,18],[12,19],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,21],[11,18],[12,19],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,21],[11,20],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,13],[11,18],[12,19],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,13],[11,20],[12,19],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,17],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,17],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,17],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,17],[11,18],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,17],[11,20],[12,19],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,17],[11,20],[12,19],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,17],[11,14],[12,19],[13,20],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,19],[11,20],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,15],[10,19],[11,18],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,19],[11,18],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,14],[6,15],[10,19],[11,20],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,19],[11,14],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,21],[11,14],[12,19],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,13],[11,20],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,13],[11,20],[12,19],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,15],[11,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,15],[11,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,16],[6,17],[10,15],[11,20],[12,19],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,17],[8,11],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,17],[8,11],[12,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,7],[5,16],[6,17],[8,11],[12,19],[13,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,7],[5,18],[6,19],[10,15],[11,16],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,21],[7,16],[8,17],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,21],[7,16],[8,17],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,13],[7,18],[8,21],[12,17],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,13],[7,16],[8,21],[12,17],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,13],[7,18],[10,21],[12,17],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,18],[6,13],[7,16],[10,21],[12,17],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,13],[7,20],[8,15],[12,17],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,13],[7,16],[8,17],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,13],[7,18],[8,17],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,13],[7,18],[8,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,13],[7,14],[8,17],[12,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,13],[7,18],[8,19],[12,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,13],[7,14],[8,19],[12,17],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,15],[7,20],[8,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,15],[7,16],[8,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,15],[7,20],[8,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,15],[7,16],[8,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,15],[7,20],[10,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,20],[6,15],[7,16],[10,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,15],[7,20],[10,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,20],[6,15],[7,16],[10,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,15],[7,18],[8,17],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,15],[7,16],[8,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,15],[7,20],[8,17],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,15],[7,16],[8,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,16],[10,17],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,14],[10,17],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,15],[7,18],[8,19],[12,21],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,15],[7,16],[8,19],[12,21],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,15],[7,16],[8,19],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,15],[7,20],[8,19],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,16],[8,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,16],[8,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,12],[8,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,12],[8,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,12],[6,17],[7,16],[10,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,12],[6,17],[7,16],[10,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,17],[7,12],[10,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,17],[7,12],[10,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,17],[7,10],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,17],[7,10],[12,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,17],[7,10],[12,19],[13,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,8],[6,17],[7,16],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,8],[6,17],[7,16],[12,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,8],[6,17],[7,16],[12,19],[13,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,17],[7,18],[8,13],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,17],[7,14],[8,13],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,20],[8,13],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,20],[6,17],[7,16],[8,13],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,18],[8,13],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,18],[8,13],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,17],[7,18],[8,15],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,18],[8,15],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,17],[7,16],[8,15],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,20],[8,15],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,18],[8,15],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,17],[7,16],[8,15],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,16],[10,17],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,17],[7,16],[8,19],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,17],[7,14],[8,19],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,17],[7,14],[8,19],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,18],[10,13],[11,20],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,18],[10,13],[11,20],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,19],[7,16],[8,21],[12,17],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,19],[7,14],[8,21],[12,17],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,14],[6,19],[7,16],[10,21],[12,17],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,11],[5,16],[6,19],[7,14],[10,21],[12,17],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,15],[7,14],[10,19],[11,20],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,16],[6,19],[7,20],[8,15],[12,17],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,19],[7,20],[8,15],[12,17],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,18],[6,19],[7,14],[8,15],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,14],[6,19],[7,16],[8,17],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,11],[5,12],[6,19],[7,14],[8,17],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,17],[7,16],[10,13],[11,20],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,19],[7,18],[8,15],[11,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,21],[7,16],[8,17],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,21],[7,18],[8,19],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,11],[7,18],[10,19],[12,17],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,11],[7,18],[8,17],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,11],[7,18],[8,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,11],[7,18],[8,19],[12,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,15],[7,20],[8,21],[11,16],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,16],[10,19],[11,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,16],[10,19],[11,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,15],[7,18],[8,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,15],[7,16],[8,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,15],[7,20],[10,21],[11,16],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,16],[10,21],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,14],[10,21],[11,18],[12,19],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,18],[10,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,15],[7,16],[10,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,20],[6,15],[7,18],[10,17],[11,16],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,14],[10,19],[11,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,18],[10,19],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,15],[7,16],[10,19],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,12],[10,19],[11,20],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,15],[7,16],[10,19],[11,20],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,15],[7,14],[10,19],[11,20],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,20],[6,15],[7,16],[8,17],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,15],[7,20],[8,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,12],[6,15],[7,18],[8,19],[11,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,17],[7,12],[8,21],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,17],[7,16],[8,21],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,17],[7,14],[8,21],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,12],[6,17],[7,18],[10,21],[11,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,17],[7,12],[10,21],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,17],[7,16],[10,21],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,17],[7,14],[10,21],[11,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,12],[6,17],[7,18],[10,15],[11,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,17],[7,16],[10,19],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,17],[7,14],[10,19],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,12],[6,17],[7,18],[10,19],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,17],[7,12],[10,19],[11,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,17],[7,18],[8,11],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,17],[7,14],[8,11],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,16],[6,17],[7,20],[8,11],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,20],[6,17],[7,16],[8,11],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,20],[6,17],[7,16],[8,15],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,17],[7,20],[8,19],[11,16],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,19],[7,18],[8,21],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,19],[7,14],[8,21],[11,16],[12,17],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,19],[7,18],[10,21],[11,16],[12,15],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,19],[7,14],[10,21],[11,16],[12,17],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,16],[6,19],[7,10],[11,18],[12,17],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,19],[7,14],[10,15],[11,16],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,19],[7,12],[10,15],[11,16],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,18],[6,19],[7,14],[10,15],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,19],[7,18],[10,17],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,13],[5,14],[6,19],[7,18],[10,17],[11,20],[12,15],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,18],[6,19],[7,20],[8,15],[11,16],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,20],[6,19],[7,18],[8,15],[11,16],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,13],[5,14],[6,19],[7,20],[8,17],[11,16],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,21],[7,18],[8,17],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,21],[7,20],[8,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,21],[7,20],[8,19],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,11],[7,20],[8,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,11],[7,20],[8,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,11],[7,20],[10,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,11],[7,20],[10,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,11],[7,18],[8,17],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,11],[7,18],[8,19],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,11],[7,20],[8,19],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,13],[7,20],[8,21],[11,16],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,13],[7,18],[8,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,13],[7,20],[10,21],[11,16],[12,17],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,18],[10,21],[11,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,18],[10,19],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,13],[7,12],[10,19],[11,20],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,13],[7,16],[10,19],[11,20],[12,17],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,13],[7,18],[8,11],[12,17],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,13],[7,12],[8,17],[11,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,13],[7,18],[8,17],[11,16],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,13],[7,20],[8,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,12],[6,17],[7,20],[8,21],[11,16],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,17],[7,18],[8,21],[11,20],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,14],[8,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,14],[8,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,18],[10,19],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,17],[7,16],[10,19],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,12],[6,17],[7,20],[10,21],[11,16],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,17],[7,18],[10,21],[11,20],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,14],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,14],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,18],[10,21],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,17],[7,16],[10,21],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,17],[7,14],[10,13],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,18],[10,13],[11,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,17],[7,16],[10,13],[11,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,14],[10,13],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,17],[7,18],[10,19],[11,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,17],[7,14],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,17],[7,12],[10,19],[11,20],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,17],[7,14],[8,11],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,18],[8,11],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,17],[7,16],[8,11],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,18],[8,11],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,17],[7,16],[8,11],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,20],[8,13],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,12],[6,17],[7,18],[8,19],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,17],[7,12],[8,19],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,16],[6,19],[7,12],[8,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,19],[7,20],[8,21],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,19],[7,20],[8,21],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,19],[7,14],[8,21],[11,16],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,16],[6,19],[7,12],[10,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,19],[7,20],[10,21],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,14],[6,19],[7,20],[10,21],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,15],[5,18],[6,19],[7,14],[10,21],[11,16],[12,17],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,19],[7,18],[8,11],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,19],[7,16],[8,11],[12,17],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,19],[7,18],[8,11],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,19],[7,14],[8,11],[12,17],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,18],[6,19],[7,20],[8,13],[11,16],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,19],[7,18],[8,13],[11,16],[12,17],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,12],[6,19],[7,18],[8,17],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,20],[6,19],[7,12],[8,17],[11,16],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,15],[5,14],[6,19],[7,12],[8,17],[11,18],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,21],[7,14],[8,13],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,21],[7,14],[8,15],[11,16],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,20],[6,11],[7,14],[10,15],[12,19],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,11],[7,12],[8,13],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,11],[7,12],[8,13],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,11],[7,14],[8,15],[12,19],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,13],[7,16],[8,21],[11,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,13],[7,18],[8,21],[11,16],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,13],[7,12],[8,21],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,13],[7,16],[10,19],[11,20],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,13],[7,14],[8,21],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,13],[7,16],[10,21],[11,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,13],[7,18],[10,21],[11,16],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,12],[10,21],[11,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,13],[7,14],[10,19],[11,20],[12,15],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,21],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,13],[7,18],[10,15],[11,20],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,13],[7,14],[10,15],[11,20],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,13],[7,18],[10,19],[11,14],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,13],[7,20],[8,15],[11,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,13],[7,20],[8,15],[11,16],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,20],[6,13],[7,14],[8,15],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,13],[7,14],[8,19],[11,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,13],[7,12],[8,19],[11,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,15],[7,20],[8,21],[11,16],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,15],[7,16],[8,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,15],[7,16],[8,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,14],[6,15],[7,18],[8,21],[11,20],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,15],[7,14],[8,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,15],[7,14],[8,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,18],[10,19],[11,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,15],[7,20],[10,21],[11,16],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,16],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,16],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,18],[10,21],[11,20],[12,19],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,14],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,14],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,18],[10,21],[11,14],[12,19],[13,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,18],[6,15],[7,14],[10,13],[11,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,18],[10,13],[11,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,16],[10,13],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,14],[10,13],[11,20],[12,19],[18,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,16],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,18],[10,19],[11,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,15],[7,14],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,14],[6,15],[7,12],[10,19],[11,20],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,15],[7,14],[8,11],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,15],[7,20],[8,13],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,20],[6,15],[7,14],[8,13],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,15],[7,12],[8,19],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,19],[7,14],[8,21],[11,16],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,19],[7,14],[10,21],[11,16],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,16],[6,19],[7,14],[10,13],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,17],[5,12],[6,19],[7,14],[10,15],[11,20],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,16],[6,19],[7,14],[8,11],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,19],[7,20],[8,15],[11,16],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,12],[6,19],[7,14],[8,15],[11,18],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,17],[5,18],[6,19],[7,12],[8,15],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,20],[6,21],[7,14],[8,15],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,11],[7,16],[8,15],[12,17],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,16],[6,13],[7,10],[11,18],[12,17],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,12],[6,13],[7,18],[10,17],[11,14],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,12],[6,13],[7,14],[8,17],[11,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,13],[7,12],[8,17],[11,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,12],[6,15],[7,16],[8,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,16],[6,15],[7,12],[8,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,15],[7,20],[8,21],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,15],[7,18],[8,21],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,14],[6,15],[7,20],[8,21],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,12],[6,15],[7,16],[10,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,16],[6,15],[7,12],[10,21],[11,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,15],[7,20],[10,21],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,15],[7,18],[10,21],[11,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,15],[7,20],[10,21],[11,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,16],[6,15],[7,18],[10,13],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,18],[6,15],[7,16],[10,13],[11,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,15],[7,18],[10,17],[11,16],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,12],[6,15],[7,16],[8,17],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,14],[6,17],[7,16],[10,13],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,8],[2,9],[4,19],[5,16],[6,17],[7,14],[10,13],[11,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,16],[6,17],[7,14],[8,11],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,12],[6,17],[7,16],[8,15],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,9],[4,19],[5,18],[6,17],[7,12],[8,15],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,21],[7,12],[8,13],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,21],[7,14],[8,13],[9,12],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,18],[6,17],[7,12],[8,13],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,18],[6,17],[7,14],[8,13],[9,12],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,18],[6,17],[8,21],[9,14],[10,13],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,18],[6,17],[8,13],[9,12],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,21],[7,18],[8,17],[10,13],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,18],[6,17],[7,14],[8,13],[10,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,17],[7,14],[8,13],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,14],[8,21],[9,12],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,18],[8,15],[9,16],[10,17],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,13],[7,14],[8,17],[9,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,13],[7,18],[8,17],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,13],[7,16],[8,17],[9,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,13],[7,12],[8,17],[9,18],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,21],[7,16],[8,17],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,10],[6,13],[7,18],[8,17],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,17],[7,16],[8,13],[9,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,13],[7,18],[8,17],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,16],[8,17],[9,18],[10,15],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,13],[7,18],[8,17],[9,16],[10,15],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,16],[8,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,19],[7,12],[8,13],[9,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,19],[7,14],[8,13],[9,12],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,19],[7,18],[8,15],[9,12],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,16],[6,15],[7,18],[8,13],[9,20],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,20],[6,15],[7,16],[8,19],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,20],[6,15],[7,16],[8,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,15],[7,20],[8,13],[9,18],[10,17],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,15],[7,20],[8,21],[12,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,15],[7,18],[8,17],[9,14],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,15],[7,16],[8,17],[9,18],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,15],[7,18],[8,17],[9,16],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,19],[7,20],[8,13],[9,12],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,19],[7,16],[8,13],[9,12],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,15],[7,16],[8,17],[9,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,16],[6,15],[7,14],[8,17],[9,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,15],[7,16],[8,17],[9,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,21],[7,18],[8,17],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,10],[6,15],[7,16],[8,17],[9,18],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,10],[6,15],[7,18],[8,17],[9,16],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,21],[7,18],[8,17],[9,12],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,9],[7,18],[8,17],[10,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,9],[7,18],[8,17],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,9],[7,18],[8,17],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,18],[6,19],[7,20],[8,17],[9,14],[10,13],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,20],[8,15],[9,14],[10,13],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,20],[8,15],[9,14],[10,13],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,15],[7,16],[8,17],[9,18],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,15],[7,18],[8,17],[9,16],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,15],[7,14],[8,17],[9,18],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,18],[6,15],[7,16],[8,17],[9,14],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,15],[7,16],[8,17],[9,14],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,15],[7,16],[8,19],[9,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,15],[7,20],[8,19],[12,17],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,16],[6,15],[7,12],[8,19],[9,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,19],[7,18],[8,13],[9,12],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,19],[7,16],[8,13],[9,12],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,15],[7,18],[8,19],[9,20],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,15],[7,20],[8,19],[9,18],[12,17],[13,16]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,13],[7,10],[8,21],[9,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,10],[8,19],[9,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,17],[7,20],[8,21],[9,14],[10,13],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,10],[8,19],[9,18],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,19],[9,20],[10,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,21],[9,20],[10,19],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,15],[8,19],[9,20],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,15],[7,16],[8,19],[9,18],[10,17],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,15],[7,14],[8,19],[9,18],[10,17],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,15],[7,20],[8,19],[9,14],[10,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,18],[6,17],[8,13],[9,12],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,8],[6,17],[7,18],[9,14],[10,13],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,8],[6,19],[7,18],[9,14],[10,13],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,19],[7,18],[8,15],[9,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,8],[6,17],[7,18],[9,16],[10,15],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,19],[7,18],[8,15],[10,13],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,17],[7,18],[8,13],[9,12],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,17],[7,16],[8,13],[9,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,16],[6,17],[7,14],[8,13],[9,20],[12,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,10],[6,17],[7,16],[8,13],[9,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,9],[7,18],[8,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,17],[7,18],[8,13],[9,14],[10,15],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,17],[7,18],[8,15],[9,14],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,17],[7,16],[8,15],[9,18],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,17],[7,20],[8,13],[9,12],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,17],[7,18],[8,13],[9,12],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,17],[7,16],[8,13],[9,12],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,14],[6,17],[7,16],[8,15],[9,20],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,17],[7,14],[8,15],[9,16],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,20],[6,17],[7,16],[8,15],[9,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,10],[6,17],[7,18],[8,15],[9,14],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,10],[6,17],[7,16],[8,15],[9,18],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,17],[7,18],[8,21],[9,14],[10,13],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,17],[7,18],[8,15],[9,14],[10,13],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,17],[7,18],[8,19],[9,14],[10,13],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,19],[7,18],[8,17],[9,14],[10,13],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,20],[6,19],[7,18],[8,15],[9,14],[10,13],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,17],[7,16],[8,15],[9,18],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,18],[6,17],[7,14],[8,15],[9,16],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,17],[7,14],[8,15],[9,16],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,17],[7,18],[8,15],[9,14],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,18],[6,17],[7,16],[8,15],[9,14],[10,19],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,17],[7,16],[8,15],[9,14],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,21],[5,12],[6,17],[7,16],[8,19],[9,14],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,17],[7,20],[8,13],[9,12],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,20],[6,17],[7,18],[8,13],[9,12],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,20],[6,17],[7,16],[8,13],[10,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,8],[6,17],[7,16],[9,20],[10,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,17],[7,18],[8,21],[9,14],[10,13],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,21],[7,18],[8,19],[9,14],[10,13],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,17],[7,18],[8,19],[9,14],[10,13],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,19],[7,18],[8,17],[9,14],[10,13],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,8],[6,17],[7,16],[10,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,17],[7,18],[8,19],[9,16],[10,15],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,8],[6,17],[7,16],[10,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,8],[6,17],[7,16],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,16],[6,19],[7,14],[8,13],[9,18],[10,17],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,8],[6,17],[7,16],[12,19],[13,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,8],[6,17],[7,16],[12,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,19],[7,18],[8,15],[9,16],[10,17],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,19],[7,14],[8,15],[9,16],[10,17],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,19],[7,16],[8,15],[9,14],[10,17],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,20],[6,13],[7,16],[8,17],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,9],[7,16],[8,17],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,20],[6,17],[7,16],[8,13],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,16],[8,21],[9,14],[10,13],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,8],[6,17],[7,16],[9,20],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,16],[8,21],[9,14],[10,13],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,19],[7,16],[8,17],[9,18],[10,15],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,14],[6,19],[7,18],[8,17],[9,16],[10,15],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,21],[5,20],[6,19],[7,14],[8,17],[9,16],[10,15],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,14],[6,15],[8,19],[9,18],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,13],[9,20],[10,19],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,17],[9,18],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,15],[8,17],[9,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,15],[8,17],[9,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,15],[7,20],[8,19],[9,12],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,17],[7,20],[8,19],[9,12],[13,16],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,14],[6,15],[8,19],[9,18],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,15],[8,19],[9,18],[10,13],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,21],[7,18],[8,19],[9,12],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,21],[9,12],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,21],[9,12],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,17],[8,13],[9,20],[10,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,13],[9,20],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,18],[6,17],[8,15],[9,14],[10,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,17],[8,15],[9,18],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,18],[6,17],[8,15],[9,14],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,15],[9,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,15],[9,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,18],[6,17],[8,15],[9,20],[10,13],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,17],[8,19],[9,14],[10,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,7],[5,16],[6,17],[8,19],[9,14],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,7],[5,16],[6,17],[8,19],[9,20],[10,13],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,21],[7,16],[8,17],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,13],[7,18],[8,21],[12,17],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,13],[7,16],[8,21],[12,17],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,13],[7,20],[8,15],[12,17],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,13],[7,18],[8,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,13],[7,14],[8,17],[12,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,13],[7,14],[8,19],[12,17],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,15],[7,20],[8,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,20],[6,15],[7,16],[8,21],[12,17],[13,18],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,15],[7,18],[8,17],[10,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,18],[6,15],[7,16],[8,17],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,15],[7,18],[8,17],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,15],[7,16],[8,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,15],[7,20],[8,17],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,15],[7,16],[8,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,18],[6,17],[7,20],[8,15],[10,13],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,15],[7,18],[8,19],[10,21],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,15],[7,18],[8,13],[9,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,15],[7,18],[8,19],[12,21],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,15],[7,16],[8,19],[12,21],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,15],[7,18],[8,19],[10,13],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,16],[8,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,12],[8,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,12],[8,21],[13,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,18],[8,21],[10,13],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,8],[6,17],[7,18],[10,13],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,8],[6,17],[7,18],[10,13],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,18],[8,13],[10,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,17],[7,20],[8,13],[10,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,17],[7,18],[8,13],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,20],[8,13],[12,21],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,18],[8,13],[14,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,18],[8,13],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,18],[8,15],[10,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,17],[7,18],[8,15],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,18],[6,17],[7,16],[8,15],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,17],[7,18],[8,15],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,18],[8,15],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,17],[7,16],[8,15],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,20],[8,15],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,18],[8,15],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,17],[7,16],[8,15],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,20],[6,17],[7,18],[8,15],[10,13],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,14],[6,17],[7,16],[8,19],[10,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,17],[7,14],[8,19],[10,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,17],[7,16],[8,19],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,17],[7,14],[8,19],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,17],[7,14],[8,19],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,17],[7,18],[8,19],[10,13],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,19],[7,18],[8,17],[10,13],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,9],[5,16],[6,19],[7,18],[8,15],[10,13],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,19],[7,16],[8,21],[12,17],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,19],[7,14],[8,21],[12,17],[13,18],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,16],[6,19],[7,20],[8,15],[12,17],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,19],[7,20],[8,15],[12,17],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,18],[6,19],[7,14],[8,15],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,8],[6,17],[7,16],[9,14],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,17],[7,16],[8,19],[9,14],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,14],[6,19],[7,16],[8,17],[12,21],[13,20],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,9],[5,12],[6,19],[7,14],[8,17],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,21],[7,16],[8,17],[9,18],[10,19],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,21],[7,18],[8,17],[9,16],[10,19],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,15],[7,16],[8,19],[9,18],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,21],[7,18],[8,19],[9,16],[10,15],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,21],[7,16],[8,19],[9,18],[10,17],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,9],[7,18],[8,17],[10,19],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,20],[8,15],[9,14],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,20],[8,15],[9,12],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,9],[7,18],[8,19],[10,15],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,9],[7,18],[8,19],[10,15],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,9],[7,18],[8,19],[10,17],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,15],[7,20],[8,21],[9,16],[10,17],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,16],[8,19],[9,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,16],[8,19],[9,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,18],[8,21],[9,20],[10,19],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,15],[7,20],[8,19],[9,18],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,18],[8,17],[9,20],[10,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,18],[8,17],[9,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,15],[7,18],[8,17],[9,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,15],[7,16],[8,17],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,15],[7,16],[8,17],[9,18],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,15],[7,18],[8,17],[9,16],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,20],[8,17],[9,18],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,15],[7,18],[8,17],[9,14],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,15],[7,16],[8,17],[9,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,15],[7,16],[8,17],[9,18],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,15],[7,18],[8,17],[9,16],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,15],[7,18],[8,17],[9,12],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,15],[7,16],[8,17],[9,18],[10,19],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,15],[7,18],[8,17],[9,16],[10,19],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,20],[8,17],[9,18],[10,19],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,16],[8,17],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,14],[8,17],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,16],[8,19],[9,18],[10,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,18],[8,19],[9,16],[10,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,14],[8,19],[9,18],[10,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,18],[8,19],[9,20],[10,21],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,15],[7,18],[8,19],[9,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,18],[8,19],[9,16],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,15],[7,14],[8,19],[9,18],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,15],[7,16],[8,19],[9,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,15],[7,18],[8,19],[9,12],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,15],[7,18],[8,19],[9,16],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,15],[7,18],[8,19],[9,14],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,10],[8,19],[9,20],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,15],[7,16],[8,19],[9,18],[10,17],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,18],[8,19],[9,20],[10,17],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,15],[7,16],[8,19],[9,20],[10,17],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,15],[7,14],[8,19],[9,20],[10,17],[18,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,17],[7,18],[8,21],[9,12],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,17],[7,18],[8,21],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,10],[8,21],[9,20],[14,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,16],[8,21],[9,20],[10,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,14],[8,21],[9,20],[10,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,8],[6,17],[7,18],[9,14],[10,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,8],[6,17],[7,18],[9,14],[12,21],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,8],[6,17],[7,18],[9,20],[10,15],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,8],[6,17],[7,16],[9,18],[10,19],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,8],[6,17],[7,18],[9,16],[10,19],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,18],[8,15],[9,20],[10,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,17],[7,18],[8,15],[9,14],[10,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,18],[8,15],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,17],[7,16],[8,15],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,17],[7,16],[8,15],[9,18],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,17],[7,18],[8,15],[9,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,17],[7,18],[8,15],[9,14],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,17],[7,18],[8,15],[9,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,16],[8,15],[9,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,17],[7,16],[8,15],[9,18],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,17],[7,18],[8,15],[9,12],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,17],[7,18],[8,15],[9,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,17],[7,16],[8,15],[9,18],[10,19],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,16],[8,15],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,16],[8,19],[9,20],[10,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,18],[8,19],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,14],[8,19],[9,20],[10,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,18],[8,19],[9,14],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,17],[7,16],[8,19],[9,14],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,17],[7,16],[8,19],[9,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,17],[7,18],[8,19],[9,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,17],[7,14],[8,19],[9,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,17],[7,18],[8,19],[9,14],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,16],[8,19],[9,14],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,17],[7,18],[8,19],[9,12],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,17],[7,16],[8,19],[9,12],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,17],[7,16],[8,19],[9,12],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,17],[7,16],[8,19],[9,20],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,17],[7,18],[8,19],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,10],[8,19],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,18],[8,19],[9,20],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,17],[7,20],[8,19],[9,18],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,17],[7,16],[8,19],[9,20],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,17],[7,18],[8,19],[9,16],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,18],[8,19],[9,20],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,17],[7,20],[8,19],[9,18],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,19],[7,14],[8,21],[9,16],[10,17],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,8],[6,19],[7,18],[9,16],[10,15],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,17],[7,16],[9,18],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,19],[7,18],[8,15],[9,14],[10,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,17],[7,16],[9,18],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,19],[7,14],[8,15],[9,16],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,19],[7,18],[8,15],[9,14],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,19],[7,16],[8,15],[9,14],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,19],[7,18],[8,15],[9,12],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,18],[6,19],[7,16],[8,15],[9,12],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,19],[7,20],[8,15],[9,16],[10,17],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,19],[7,18],[8,15],[9,16],[10,17],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,19],[7,14],[8,15],[9,20],[10,17],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,16],[8,17],[9,18],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,18],[8,17],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,19],[7,18],[8,17],[9,14],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,19],[7,16],[8,17],[9,18],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,19],[7,16],[8,17],[9,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,14],[6,19],[7,18],[8,17],[9,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,19],[7,18],[8,17],[9,14],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,16],[6,19],[7,18],[8,17],[9,12],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,13],[5,20],[6,19],[7,16],[8,17],[9,12],[14,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,19],[7,16],[8,17],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,17],[7,16],[8,13],[9,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,10],[6,19],[7,18],[8,17],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,19],[7,14],[8,13],[9,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,16],[6,19],[7,18],[8,17],[9,20],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,19],[7,16],[8,17],[9,18],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,18],[6,19],[7,20],[8,17],[9,16],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,20],[6,19],[7,18],[8,17],[9,16],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,13],[5,14],[6,19],[7,18],[8,17],[9,20],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,21],[7,20],[8,13],[9,18],[12,19],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,21],[7,12],[8,17],[9,18],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,21],[7,20],[8,17],[9,14],[12,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,19],[7,20],[8,21],[9,18],[10,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,21],[7,12],[8,19],[9,18],[13,20],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,18],[8,19],[9,12],[16,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,21],[7,10],[8,19],[9,20],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,21],[7,18],[8,19],[9,20],[10,17],[13,16]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,21],[7,20],[8,19],[9,18],[10,17],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,9],[7,20],[8,19],[12,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,9],[7,18],[8,17],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,17],[7,14],[8,13],[9,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,9],[7,18],[8,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,9],[7,16],[8,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,9],[7,18],[8,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,9],[7,16],[8,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,9],[7,18],[8,19],[10,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,9],[7,20],[8,19],[10,21],[13,18],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,9],[7,18],[8,19],[12,21],[13,16],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,9],[7,18],[8,19],[12,17],[13,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,13],[7,18],[8,21],[9,20],[10,19],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,18],[8,17],[9,20],[10,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,18],[8,17],[9,20],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,20],[8,17],[9,18],[12,21],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,20],[6,13],[7,12],[8,17],[9,18],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,20],[8,17],[9,18],[10,19],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,18],[8,19],[9,16],[10,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,13],[7,18],[8,19],[9,20],[10,21],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,13],[7,20],[8,19],[9,18],[10,21],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,13],[7,18],[8,19],[9,16],[12,21],[17,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,13],[7,18],[8,19],[9,20],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,13],[7,20],[8,19],[9,18],[12,21],[14,17]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,13],[7,10],[8,19],[9,20],[14,17],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,18],[8,19],[9,20],[10,17],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,13],[7,16],[8,19],[9,20],[10,17],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,17],[7,18],[8,21],[9,20],[10,19],[13,16]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,14],[8,21],[9,20],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,8],[6,17],[7,18],[9,14],[10,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,8],[6,17],[7,18],[9,16],[10,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,17],[7,18],[9,14],[12,21],[13,20],[16,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,17],[7,18],[9,16],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,17],[7,18],[9,16],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,8],[6,17],[7,18],[9,20],[10,13],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,18],[8,13],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,18],[6,17],[7,16],[8,13],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,17],[7,18],[8,13],[9,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,17],[7,16],[8,13],[9,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,14],[8,13],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,17],[7,18],[8,19],[9,20],[10,21],[13,16]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,14],[6,17],[7,20],[8,19],[9,18],[10,21],[13,16]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,14],[8,19],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,18],[8,19],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,18],[6,17],[7,16],[8,19],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,17],[7,18],[8,19],[9,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,17],[7,20],[8,19],[9,18],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,17],[7,14],[8,19],[9,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,17],[7,18],[8,19],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,18],[6,17],[7,16],[8,19],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,18],[8,19],[9,20],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,17],[7,20],[8,19],[9,18],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,19],[7,18],[8,17],[9,20],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,17],[7,18],[8,19],[9,16],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,19],[7,20],[9,16],[12,17],[13,18],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,8],[6,19],[7,20],[9,14],[12,17],[13,18],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,8],[6,19],[7,18],[9,16],[10,13],[14,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,19],[7,14],[8,13],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,16],[6,19],[7,18],[8,17],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,14],[6,19],[7,18],[8,17],[9,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,15],[5,16],[6,19],[7,18],[8,17],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,19],[7,16],[8,17],[9,18],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,18],[6,19],[7,20],[8,17],[9,16],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,15],[5,20],[6,19],[7,18],[8,17],[9,16],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,21],[7,12],[8,15],[9,16],[13,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,21],[7,20],[8,15],[9,18],[10,13],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,21],[7,20],[8,15],[9,14],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,21],[7,14],[8,19],[9,18],[10,13],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,13],[7,20],[8,15],[9,16],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,13],[7,20],[8,15],[9,16],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,13],[7,14],[8,15],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,13],[7,14],[8,19],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,13],[7,14],[8,19],[9,16],[12,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,13],[7,14],[8,19],[9,20],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,14],[6,15],[7,16],[8,21],[9,20],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,15],[7,14],[8,21],[9,20],[10,19],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,15],[7,18],[8,13],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,15],[7,18],[8,13],[9,20],[12,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,14],[6,15],[7,16],[8,13],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,15],[7,14],[8,13],[9,20],[10,19],[18,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,14],[6,15],[7,16],[8,19],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,15],[7,14],[8,19],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,15],[7,18],[8,19],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,14],[6,15],[7,16],[8,19],[9,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,14],[6,15],[7,18],[8,19],[9,20],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,14],[6,15],[7,20],[8,19],[9,18],[12,21],[13,16]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,15],[7,14],[8,19],[9,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,16],[6,15],[7,18],[8,19],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,16],[6,15],[7,20],[8,19],[9,18],[10,13],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,20],[8,13],[9,14],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,20],[6,19],[7,18],[8,13],[9,14],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,14],[6,19],[7,20],[8,15],[9,16],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,14],[8,15],[9,16],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,17],[5,18],[6,19],[7,16],[8,15],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,14],[6,19],[7,20],[8,15],[9,16],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,19],[7,14],[8,15],[9,16],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,17],[5,18],[6,19],[7,16],[8,15],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,21],[7,14],[8,15],[9,16],[10,17],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,21],[7,16],[8,15],[9,14],[10,17],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,20],[6,21],[7,14],[8,17],[9,16],[10,15],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,13],[7,12],[8,17],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,14],[6,15],[7,20],[8,21],[9,16],[10,17],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,14],[6,15],[7,16],[8,17],[9,18],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,14],[6,15],[7,16],[8,17],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,14],[6,15],[7,18],[8,17],[9,16],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,15],[7,14],[8,17],[9,18],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,15],[7,14],[8,17],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,15],[7,16],[8,17],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,15],[7,16],[8,17],[9,18],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,15],[7,16],[8,17],[9,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,15],[7,18],[8,17],[9,16],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,15],[7,14],[8,17],[9,18],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,15],[7,14],[8,17],[9,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,15],[7,16],[8,17],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,8],[6,17],[7,18],[9,16],[10,13],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,17],[7,14],[8,13],[9,20],[10,21],[15,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,17],[7,14],[8,13],[9,20],[12,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,20],[8,13],[9,14],[10,15],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,14],[6,17],[7,16],[8,15],[9,18],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,14],[6,17],[7,16],[8,15],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,14],[8,15],[9,16],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,16],[6,17],[7,18],[8,15],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,11],[4,19],[5,18],[6,17],[7,16],[8,15],[9,14],[10,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,17],[7,16],[8,15],[9,18],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,14],[6,17],[7,16],[8,15],[9,20],[12,21],[13,18]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,17],[7,14],[8,15],[9,16],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,16],[6,17],[7,18],[8,15],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,10],[2,11],[4,19],[5,18],[6,17],[7,16],[8,15],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,8],[6,17],[7,18],[10,21],[11,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,17],[7,18],[8,21],[9,14],[15,20],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,21],[7,18],[8,19],[10,15],[11,14],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,11],[7,18],[8,15],[9,16],[10,17],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,11],[7,16],[8,17],[9,18],[10,15],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,11],[7,18],[8,17],[9,16],[10,15],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,10],[6,15],[7,16],[8,17],[9,18],[11,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,10],[6,15],[7,18],[8,17],[9,16],[11,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,8],[6,17],[7,18],[10,19],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,10],[6,17],[7,16],[8,15],[9,18],[11,20],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,16],[8,17],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,16],[8,17],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,18],[8,17],[9,16],[10,19],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,20],[8,17],[9,18],[10,19],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,16],[6,15],[7,14],[8,17],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,18],[6,19],[7,20],[8,21],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,20],[6,19],[7,18],[8,21],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,8],[6,17],[7,18],[10,15],[11,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,16],[8,19],[9,18],[10,17],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,20],[8,19],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,18],[8,19],[9,20],[10,17],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,15],[7,20],[8,19],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,17],[7,16],[8,15],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,18],[6,21],[7,20],[8,19],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,20],[6,17],[7,18],[8,19],[10,15],[11,14],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,17],[7,18],[8,19],[9,16],[10,15],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,17],[7,18],[8,19],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,16],[6,17],[7,18],[8,19],[9,20],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,16],[6,17],[7,20],[8,19],[9,18],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,17],[7,18],[8,19],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,19],[7,18],[8,15],[9,16],[10,17],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,19],[7,14],[8,15],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,19],[7,14],[8,15],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,16],[8,17],[9,18],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,18],[8,17],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,18],[6,19],[7,20],[8,17],[10,15],[11,14],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,20],[6,19],[7,18],[8,17],[10,15],[11,14],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,19],[7,16],[8,17],[9,18],[10,15],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,14],[6,19],[7,18],[8,17],[9,16],[10,15],[11,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,19],[7,14],[8,17],[9,16],[10,15],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,18],[6,19],[7,20],[8,17],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,19],[7,18],[8,17],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,16],[6,19],[7,18],[8,17],[9,20],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,18],[6,19],[7,20],[8,17],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,21],[5,20],[6,19],[7,18],[8,17],[9,16],[10,15],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,7],[5,16],[6,17],[8,21],[9,20],[10,15],[11,18],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,7],[5,16],[6,17],[8,21],[9,14],[10,19],[11,18],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,7],[5,16],[6,17],[8,21],[9,20],[10,19],[11,14],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,7],[5,16],[6,17],[8,15],[9,18],[10,19],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,7],[5,16],[6,17],[8,15],[9,20],[10,19],[11,18],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,7],[5,16],[6,17],[8,19],[9,20],[10,21],[11,14],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,10],[6,11],[7,18],[8,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,15],[7,20],[8,21],[10,17],[11,18],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,18],[6,15],[7,16],[8,17],[10,19],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,20],[6,17],[7,18],[8,15],[10,21],[11,14],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,17],[7,18],[8,15],[10,19],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,18],[6,17],[7,16],[8,15],[10,19],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,17],[7,18],[8,19],[10,21],[11,14],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,18],[6,17],[7,16],[8,19],[10,21],[11,14],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,17],[7,18],[8,19],[10,15],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,18],[6,17],[7,16],[8,19],[10,15],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,19],[7,14],[8,21],[10,17],[11,18],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,19],[7,20],[8,15],[10,17],[11,18],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,19],[7,18],[8,17],[10,21],[11,14],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,9],[5,16],[6,19],[7,18],[8,17],[10,15],[11,20],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,21],[7,16],[8,17],[9,18],[10,19],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,21],[7,18],[8,17],[9,16],[10,19],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,8],[6,17],[7,18],[9,16],[10,19],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,21],[7,16],[8,19],[9,18],[10,17],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,17],[7,18],[8,15],[9,20],[14,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,15],[7,20],[8,21],[9,16],[10,17],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,15],[7,16],[8,17],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,15],[7,16],[8,17],[9,18],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,15],[7,18],[8,17],[9,16],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,15],[7,16],[8,17],[9,18],[10,19],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,15],[7,18],[8,17],[9,16],[10,19],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,15],[7,18],[8,19],[9,16],[10,21],[17,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,15],[7,16],[8,19],[9,18],[10,17],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,17],[7,14],[8,21],[9,20],[10,19],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,17],[7,18],[8,15],[9,20],[10,21],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,17],[7,18],[8,15],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,17],[7,16],[8,15],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,17],[7,16],[8,15],[9,18],[10,21],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,17],[7,18],[8,19],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,17],[7,14],[8,19],[9,20],[10,21],[15,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,17],[7,18],[8,19],[9,14],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,17],[7,16],[8,19],[9,14],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,17],[7,18],[8,19],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,17],[7,18],[8,19],[9,20],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,17],[7,20],[8,19],[9,18],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,17],[7,18],[8,19],[9,16],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,19],[7,14],[8,21],[9,16],[10,17],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,19],[7,20],[8,15],[9,16],[10,17],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,19],[7,18],[8,15],[9,16],[10,17],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,19],[7,16],[8,17],[9,18],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,14],[6,19],[7,18],[8,17],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,19],[7,18],[8,17],[9,14],[10,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,19],[7,16],[8,17],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,10],[6,19],[7,18],[8,17],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,16],[6,19],[7,18],[8,17],[9,20],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,19],[7,16],[8,17],[9,18],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,18],[6,19],[7,20],[8,17],[9,16],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,11],[5,20],[6,19],[7,18],[8,17],[9,16],[10,15],[14,21]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,19],[7,20],[8,21],[9,18],[10,17],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,21],[7,18],[8,19],[9,20],[10,17],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,21],[7,20],[8,19],[9,18],[10,17],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,8],[6,17],[7,18],[9,20],[10,21],[11,14],[16,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,17],[7,18],[8,21],[9,20],[10,19],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,18],[6,17],[7,16],[8,21],[9,20],[10,19],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,17],[7,18],[8,19],[9,20],[10,21],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,17],[7,20],[8,19],[9,18],[10,21],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,20],[6,17],[7,18],[8,19],[9,16],[10,21],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,16],[6,19],[7,18],[8,17],[9,20],[10,21],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,18],[6,19],[7,20],[8,17],[9,16],[10,21],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,15],[5,20],[6,19],[7,18],[8,17],[9,16],[10,21],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,18],[6,21],[7,14],[8,15],[9,20],[10,19],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,18],[6,21],[7,20],[8,19],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,10],[6,15],[7,20],[8,21],[9,16],[11,18],[14,19]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,16],[6,15],[7,18],[8,21],[9,20],[10,19],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,10],[6,19],[7,14],[8,21],[9,16],[11,18],[15,20]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,18],[6,19],[7,20],[8,21],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,17],[5,20],[6,19],[7,18],[8,21],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,14],[8,15],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,14],[8,15],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,18],[8,15],[9,16],[10,17],[11,14]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,14],[8,17],[9,16],[10,15],[11,18]]).
lintel_com(11,[[0,3],[1,12],[2,13],[4,19],[5,20],[6,21],[7,18],[8,17],[9,14],[10,15],[11,16]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,11],[8,17],[9,14],[10,19],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,11],[8,19],[9,14],[10,17],[13,18],[15,20],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,13],[3,8],[4,15],[7,14],[9,18],[10,19],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,15],[3,8],[4,13],[7,14],[9,18],[10,19],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,13],[3,8],[4,15],[7,14],[9,20],[10,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,13],[3,8],[4,15],[7,14],[9,20],[10,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,15],[3,8],[4,13],[7,14],[9,20],[10,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,15],[3,8],[4,13],[7,14],[9,20],[10,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,11],[3,20],[4,13],[7,18],[8,15],[9,16],[10,17],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,13],[3,20],[4,11],[7,18],[8,15],[9,16],[10,17],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,11],[3,20],[4,13],[7,16],[8,17],[9,18],[10,15],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,11],[3,20],[4,13],[7,18],[8,17],[9,16],[10,15],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,13],[3,20],[4,11],[7,16],[8,17],[9,18],[10,15],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,13],[3,20],[4,11],[7,18],[8,17],[9,16],[10,15],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,11],[8,15],[9,20],[10,17],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,11],[8,17],[9,20],[10,15],[13,18],[14,19],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,7],[3,20],[4,15],[6,13],[8,19],[9,16],[10,17],[11,18],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,7],[3,20],[4,15],[6,13],[8,19],[9,18],[10,17],[11,16],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,7],[3,20],[4,15],[6,13],[8,17],[9,18],[10,19],[11,16],[14,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,10],[4,11],[8,17],[9,16],[12,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,11],[8,13],[9,18],[10,17],[14,19],[15,20],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,11],[8,17],[9,16],[10,21],[13,18],[14,19],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,7],[3,18],[4,15],[6,11],[8,17],[9,16],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,7],[3,18],[4,15],[6,11],[8,17],[9,16],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,21],[9,16],[10,17],[11,18],[12,19],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,21],[9,18],[10,17],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,21],[9,16],[10,19],[11,18],[12,17],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,15],[9,20],[10,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,15],[9,18],[10,19],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,15],[9,20],[10,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,17],[9,18],[10,19],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,17],[9,18],[10,19],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,19],[9,16],[10,17],[11,18],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,13],[8,19],[9,18],[10,17],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,19],[9,16],[10,17],[11,18],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,12],[4,13],[8,19],[9,18],[10,17],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,21],[9,16],[10,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,21],[9,16],[10,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,21],[9,16],[10,19],[11,18],[12,17],[13,20]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,21],[9,20],[10,19],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,13],[9,20],[10,17],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,13],[9,18],[10,19],[11,20],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,13],[9,20],[10,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,6],[2,7],[3,14],[4,15],[8,19],[9,20],[10,21],[11,16],[12,17],[13,18]]).
lintel_com(11,[[0,5],[1,8],[2,17],[3,10],[4,19],[6,13],[7,12],[9,18],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,8],[4,15],[6,21],[7,14],[9,16],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,16],[2,11],[3,18],[4,9],[6,15],[7,20],[8,13],[10,17],[12,19],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,8],[4,15],[6,19],[7,12],[9,16],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,16],[4,11],[6,13],[7,18],[8,19],[9,20],[10,15],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,16],[4,9],[6,13],[7,20],[8,15],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,16],[4,11],[6,13],[7,20],[8,19],[9,18],[10,15],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,19],[3,16],[4,13],[6,21],[7,14],[8,15],[9,20],[11,18],[12,17]]).
lintel_com(11,[[0,5],[1,14],[2,9],[3,10],[4,13],[6,15],[7,20],[8,19],[11,18],[12,17],[16,21]]).
lintel_com(11,[[0,5],[1,8],[2,9],[3,14],[4,13],[6,17],[7,18],[10,19],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,8],[2,9],[3,12],[4,13],[6,19],[7,18],[10,17],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,19],[3,18],[4,13],[6,21],[7,14],[8,15],[9,16],[10,17],[11,20]]).
lintel_com(11,[[0,5],[1,8],[2,11],[3,14],[4,17],[6,21],[7,20],[9,16],[10,15],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,19],[3,18],[4,11],[6,21],[7,14],[8,15],[9,16],[10,17],[13,20]]).
lintel_com(11,[[0,5],[1,8],[2,17],[3,14],[4,11],[6,21],[7,20],[9,16],[10,15],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,9],[3,18],[4,15],[6,21],[7,20],[8,13],[10,17],[11,16],[14,19]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,16],[4,15],[6,21],[7,14],[8,17],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,16],[4,15],[6,21],[7,14],[8,17],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,9],[3,18],[4,15],[6,21],[7,14],[8,19],[10,17],[11,16],[13,20]]).
lintel_com(11,[[0,5],[1,12],[2,19],[3,8],[4,15],[6,21],[7,14],[9,16],[10,17],[11,18],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,16],[4,15],[6,11],[7,18],[8,17],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,16],[4,15],[6,11],[7,18],[8,17],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,5],[1,8],[2,13],[3,14],[4,9],[6,17],[7,18],[10,15],[11,20],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,8],[4,15],[6,21],[7,14],[9,16],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,16],[4,15],[6,13],[7,20],[8,17],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,13],[3,14],[4,9],[6,17],[7,20],[8,15],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,9],[3,18],[4,15],[6,13],[7,20],[8,19],[10,17],[11,16],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,14],[4,15],[6,17],[7,20],[8,13],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,8],[2,13],[3,10],[4,15],[6,17],[7,18],[9,14],[11,20],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,10],[2,13],[3,8],[4,15],[6,17],[7,20],[9,14],[11,18],[12,19],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,19],[3,16],[4,9],[6,21],[7,14],[8,15],[10,17],[11,18],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,9],[3,16],[4,15],[6,19],[7,12],[8,17],[11,18],[13,20],[14,21]]).
lintel_com(11,[[0,5],[1,8],[2,17],[3,18],[4,9],[6,13],[7,12],[10,19],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,6],[2,9],[3,14],[4,17],[7,16],[8,15],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,6],[2,9],[3,14],[4,17],[7,16],[8,15],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,6],[2,9],[3,14],[4,17],[7,16],[8,15],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,5],[1,8],[2,9],[3,18],[4,17],[6,13],[7,14],[10,19],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,8],[2,19],[3,10],[4,17],[6,13],[7,14],[9,18],[11,16],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,18],[4,9],[6,15],[7,12],[8,19],[11,16],[13,20],[14,21]]).
lintel_com(11,[[0,5],[1,8],[2,9],[3,18],[4,19],[6,13],[7,12],[10,17],[11,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,16],[2,17],[3,10],[4,9],[6,15],[7,20],[8,13],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,11],[3,12],[4,13],[6,19],[7,16],[8,17],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,13],[3,12],[4,11],[6,19],[7,16],[8,17],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,10],[4,13],[6,19],[7,16],[8,17],[9,18],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,14],[2,11],[3,12],[4,13],[6,15],[7,20],[8,17],[9,18],[10,19],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,15],[7,20],[8,17],[9,18],[10,19],[16,21]]).
lintel_com(11,[[0,5],[1,14],[2,11],[3,12],[4,13],[6,15],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,19],[7,16],[8,17],[9,18],[10,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,11],[3,12],[4,13],[6,17],[7,18],[8,19],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,10],[4,13],[6,17],[7,18],[8,19],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,11],[7,20],[8,17],[9,18],[10,19],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,11],[7,20],[8,17],[9,18],[10,19],[16,21]]).
lintel_com(11,[[0,5],[1,14],[2,11],[3,12],[4,13],[6,19],[7,16],[8,17],[9,18],[10,21],[15,20]]).
lintel_com(11,[[0,5],[1,14],[2,11],[3,12],[4,13],[6,19],[7,18],[8,17],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,11],[3,12],[4,13],[6,19],[7,18],[8,17],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,10],[4,13],[6,19],[7,18],[8,17],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,11],[3,14],[4,15],[6,21],[7,16],[8,17],[9,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,16],[4,13],[6,21],[7,14],[8,15],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,16],[4,13],[6,21],[7,14],[8,15],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,16],[4,15],[6,21],[7,14],[8,17],[9,18],[10,19],[13,20]]).
lintel_com(11,[[0,5],[1,8],[2,17],[3,14],[4,11],[6,19],[7,18],[9,16],[10,15],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,6],[2,17],[3,14],[4,9],[7,16],[8,15],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,16],[4,15],[6,21],[7,14],[8,19],[9,18],[10,17],[13,20]]).
lintel_com(11,[[0,5],[1,8],[2,15],[3,14],[4,9],[6,17],[7,16],[10,21],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,16],[4,15],[6,13],[7,20],[8,17],[9,18],[10,19],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,16],[4,15],[6,13],[7,18],[8,19],[9,20],[10,17],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,11],[3,16],[4,15],[6,13],[7,20],[8,19],[9,18],[10,17],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,16],[4,11],[6,19],[7,14],[8,15],[9,20],[10,21],[13,18]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,16],[4,11],[6,13],[7,18],[8,15],[9,20],[10,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,17],[3,14],[4,9],[7,16],[8,15],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,5],[1,8],[2,15],[3,14],[4,9],[6,17],[7,16],[10,19],[11,20],[12,21],[13,18]]).
lintel_com(11,[[0,5],[1,8],[2,11],[3,16],[4,19],[6,13],[7,12],[9,18],[10,17],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,16],[4,9],[6,21],[7,14],[8,15],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,16],[4,9],[6,21],[7,14],[8,15],[11,20],[12,19],[13,18]]).
lintel_com(11,[[0,5],[1,8],[2,19],[3,16],[4,11],[6,13],[7,14],[9,18],[10,17],[12,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,16],[4,11],[6,19],[7,14],[8,15],[9,18],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,16],[4,11],[6,13],[7,20],[8,15],[9,18],[12,21],[14,19]]).
lintel_com(11,[[0,5],[1,6],[2,17],[3,14],[4,9],[7,16],[8,15],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,8],[2,13],[3,14],[4,9],[6,17],[7,18],[10,21],[11,16],[12,19],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,13],[3,12],[4,11],[6,17],[7,18],[8,19],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,10],[2,13],[3,12],[4,11],[6,19],[7,18],[8,17],[9,16],[14,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,15],[7,18],[8,19],[9,20],[10,17],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,15],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,15],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,17],[7,18],[8,19],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,19],[7,18],[8,17],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,17],[7,18],[8,19],[9,20],[10,15],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,11],[6,17],[7,20],[8,19],[9,18],[10,15],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,11],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,11],[7,20],[8,19],[9,18],[10,17],[16,21]]).
lintel_com(11,[[0,5],[1,14],[2,13],[3,12],[4,11],[6,19],[7,18],[8,17],[9,16],[10,21],[15,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,21],[7,16],[8,17],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,21],[7,16],[8,17],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,19],[7,20],[8,21],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,16],[8,17],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,18],[8,17],[9,16],[10,19],[11,20]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,16],[8,17],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,19],[7,20],[8,21],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,21],[7,16],[8,19],[9,18],[10,17],[11,20]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,21],[7,20],[8,19],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,21],[7,18],[8,19],[9,20],[10,17],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,21],[7,20],[8,19],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,16],[8,19],[9,18],[10,17],[11,20]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,20],[8,19],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,18],[8,19],[9,20],[10,17],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,21],[7,20],[8,19],[9,18],[10,17],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,17],[7,18],[8,21],[9,20],[10,19],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,19],[7,18],[8,17],[9,20],[10,21],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,17],[7,18],[8,19],[9,20],[10,21],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,17],[7,20],[8,19],[9,18],[10,21],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,17],[7,18],[8,19],[9,20],[10,21],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,17],[7,20],[8,19],[9,18],[10,21],[11,16]]).
lintel_com(11,[[0,5],[1,12],[2,13],[3,14],[4,15],[6,19],[7,20],[8,21],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,19],[7,20],[8,21],[9,16],[10,17],[11,18]]).
lintel_com(11,[[0,5],[1,12],[2,15],[3,14],[4,13],[6,17],[7,18],[8,21],[9,20],[10,19],[11,16]]).
lintel_com(11,[[0,5],[1,10],[2,15],[3,14],[4,11],[6,19],[7,16],[8,17],[9,18],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,15],[3,14],[4,11],[6,19],[7,18],[8,17],[9,16],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,15],[3,14],[4,11],[6,17],[7,18],[8,19],[9,16],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,8],[2,15],[3,14],[4,9],[6,17],[7,16],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,5],[1,16],[2,15],[3,10],[4,11],[6,17],[7,18],[8,19],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,16],[2,15],[3,10],[4,11],[6,19],[7,18],[8,17],[9,14],[12,21],[13,20]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,8],[4,15],[6,11],[7,18],[9,16],[12,21],[13,20],[14,19]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,8],[4,15],[6,11],[7,18],[9,16],[12,19],[13,20],[14,21]]).
lintel_com(11,[[0,5],[1,10],[2,17],[3,8],[4,15],[6,13],[7,20],[9,16],[11,18],[12,19],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,10],[4,15],[6,13],[7,18],[8,19],[9,20],[11,16],[14,21]]).
lintel_com(11,[[0,5],[1,12],[2,17],[3,10],[4,15],[6,13],[7,20],[8,19],[9,18],[11,16],[14,21]]).
lintel_com(11,[[0,7],[1,8],[2,9],[3,14],[4,15],[5,16],[6,17],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,7],[1,8],[2,9],[3,14],[4,17],[5,16],[6,15],[10,21],[11,18],[12,19],[13,20]]).
lintel_com(11,[[0,7],[1,8],[2,11],[3,14],[4,15],[5,16],[6,19],[9,18],[10,17],[12,21],[13,20]]).
lintel_com(11,[[0,7],[1,8],[2,11],[3,16],[4,15],[5,14],[6,19],[9,18],[10,17],[12,21],[13,20]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,14],[4,15],[5,16],[6,17],[8,21],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,14],[4,15],[5,16],[6,17],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,16],[4,15],[5,14],[6,17],[8,21],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,16],[4,15],[5,14],[6,17],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,14],[4,17],[5,16],[6,15],[8,21],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,14],[4,17],[5,16],[6,15],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,15],[3,16],[4,17],[5,14],[6,13],[8,19],[9,20],[10,21],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,17],[3,14],[4,15],[5,16],[6,13],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,14],[4,15],[5,16],[6,17],[8,19],[9,20],[10,21],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,16],[4,15],[5,14],[6,17],[8,19],[9,20],[10,21],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,13],[3,14],[4,17],[5,16],[6,15],[8,19],[9,20],[10,21],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,17],[3,14],[4,15],[5,16],[6,13],[8,19],[9,20],[10,21],[11,18]]).
lintel_com(11,[[0,7],[1,14],[2,13],[3,12],[4,17],[5,16],[6,15],[8,21],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,7],[1,14],[2,13],[3,12],[4,17],[5,16],[6,15],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,7],[1,14],[2,13],[3,12],[4,17],[5,16],[6,15],[8,19],[9,20],[10,21],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,15],[3,16],[4,17],[5,14],[6,13],[8,21],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,7],[1,12],[2,15],[3,16],[4,17],[5,14],[6,13],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,7],[1,12],[2,17],[3,16],[4,13],[5,14],[6,15],[8,21],[9,18],[10,19],[11,20]]).
lintel_com(11,[[0,7],[1,12],[2,17],[3,16],[4,15],[5,14],[6,13],[8,21],[9,20],[10,19],[11,18]]).
lintel_com(11,[[0,9],[1,12],[2,13],[3,14],[4,15],[5,16],[6,17],[7,18],[8,19],[10,21],[11,20]]).
lintel_com(11,[[0,9],[1,12],[2,13],[3,14],[4,15],[5,18],[6,17],[7,16],[8,19],[10,21],[11,20]]).
lintel_com(11,[[0,9],[1,12],[2,13],[3,14],[4,17],[5,16],[6,15],[7,18],[8,19],[10,21],[11,20]]).
lintel_com(11,[[0,9],[1,12],[2,13],[3,14],[4,15],[5,16],[6,19],[7,18],[8,17],[10,21],[11,20]]).
lintel_com(11,[[0,9],[1,12],[2,15],[3,14],[4,13],[5,16],[6,19],[7,18],[8,17],[10,21],[11,20]]).
lintel_com(11,[[0,9],[1,12],[2,13],[3,16],[4,15],[5,14],[6,19],[7,18],[8,17],[10,21],[11,20]]).
lintel_com(11,[[0,11],[1,12],[2,13],[3,14],[4,15],[5,16],[6,17],[7,18],[8,19],[9,20],[10,21]]).
 


