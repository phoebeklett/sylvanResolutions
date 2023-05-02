-------------------------------------------------------------------------------------
-- Method description. (Map_1): 
-- This method is for iterating over degree choices (a,b)
-- Inputs: C, List, C, (List), contains all pairs of degrees (a,b) where a,b 
--                   have non-zero Betti # in homology degree k-1, k (respectively)
--         i, degree for iterating over elements of C
--         Rs, list with
--             R, polynomial ring w/grading
--             F, polynomial ring w/o grading
--         I, Ideal in question
-- Outputs: Ka, simplicial Complex K^aI
--          Kb, simplicial Complex K^bI
--          Lambda, List of paths from a to b
-------------------------------------------------------------------------------------
Map_1 = method()
Map_1(List,ZZ,List,Ideal):= (C,i,Rs,I) ->(
    -- simply call functions --
    p = pathS(toString(C#i#0#0),toString(C#i#1#0),Rs#0);
    Lambda = lambdaGen(toString(C#i#0#0),toString(C#i#1#0),Rs#0);
    Lambda,p
)
-------------------------------------------------------------------------------------
-- Method description. (Map_2): 
-- This method in for interating over path choices (from a to b)
-- Inputs: F, polynomial ring w/o grading
--         R, polynomial ring w/ grading
--        I, ideal in question
--        L, List including: (this is necessary bc we can have only <=4 total parameters)
--           k, homology degree
--           j, index of Lambda to use (i.e. which path from a to b to use)
--           Lambda, List of paths from a to b  
--           paths
-- Outputs: G, Matrix, resulting sylvan matrix 

-------------------------------------------------------------------------------------
Map_2 = method()
Map_2(Ring,Ring,Ideal,List):=(F,R,I,L) ->(
    -- establish objects --
    k = L#0;
    j = L#1;
    Lambda = L#2;
    ps = L#3;
    -- select path --
    if Lambda != {} then lambda = Lambda#j;
    if Lambda != {} then l = #lambda ;
    pth = ps#j;
    -- calculate Koszul along chosen path --
    Ks = new MutableHashTable;
    for i in 0..#(pth)-1 do Ks#i = upperKoszul(F,I,monomialIdeal(pth#i));
    -- get homology in terms of the generators of R --
    Kb = Ks#(max(keys(Ks)));
    h = homology(k,Kb,F);
    hom1 = generators h;
    -- represent it in terms of all faces in appropriate degree --
    h2 = faces(k,Kb); 
    h7 = h2*hom1;

    -- based on conditions finish map in 1 of 3 ways --       
    if h !=0 then H = matrix{flatten(entries(faces(k,Kb)))} * generators h else H =0;
    if flatten Lambda == {} then G = 0;
    if flatten Lambda != {} and #(ps#j) != 2 then G = Map_3({F,R},I,L,{H,Ks});
    if flatten Lambda != {} and #(ps#j) == 2 then G = Map_4({F,R},I,L,{H,Ks});
    h7,G
)
---------------------------------------------------------------------------
-- Method description. (Map_3): 
-- This method is for computing the middle and ending part of the Map in Theorem 1.11
-- Inputs: Rs, List including: 
--            F, polynomial ring w/o grading
--            R, polynomial ring w/ grading
--         I, ideal in question
--         L, List including: (this is necessary bc we can have only <=4 total parameters)
--           k, homology degree
--           j, index of Lambda to use (i.e. which path from a to b to use)
--           Lambda, List of paths from a to b  
--           paths
--         L2, List including: 
--             H, Matrix, basis for homology of K^bI
--             Ks, list of Koszul simplicial complexes along the path lambda
-- Outputs: G, Matrix, resulting sylvan matrix 
---------------------------------------------------------------------------
Map_3 = method()
Map_3(List,Ideal,List,List):= (Rs,I,L,L2) -> (
    -- initialize objects --
    F = Rs#0;
    R = Rs#1;
    k = L#0;
    j = L#1;
    Lambda = L#2;
    ps = L#3;
    H = L2#0;
    Ks = L2#1;
    -- select path --
    lambda = Lambda#j;
    l = #lambda ;
    -- following the formula in Thm 1.11, calculate middle part of map--
    H1 = flatten entries H;
    J = new MutableHashTable;
    -- iteratively compute delPlus(dLambda(basis for homK^bI)) for j =1,..ell --
    for i in 1..#(ps#j)-2 do for j in 0..#H1-1 do J#i = delPlus(R,(hedge_trimmer(Ks#(i),k),Ks#(i),k,(dLambda(R,lambda,{i,k},matrix{{H1#j}}))));
    -- take product
    P = product(values(J));
    D = 1_F;
    scan(0..#J-1, i -> D = D *J#((keys(J))#i));
    -- ind = ell --
    ind = -1;
    -- calc last step in map dLambda_ell --
    try U = dLambda(R,lambda,{ind,k},matrix{{D}}) then  U = dLambda(R,lambda,{ind,k},matrix{{D}}) else U = 0;
    -- get basis for homK^aI --
    Ka = Ks#(min(keys(Ks)));
    hom = homology(k-1,Ka,F);
    hom1 = generators hom;
    -- represent basis in terms of all faces of appropriate degree --
    
    if (flatten entries U)#0 != -1 and (flatten entries U)#0 != 1 and (flatten entries U)#0 != 0 then ret = Helper(U,Ka) else ret = (U,hom1);
    ret)
------------------------------------------------------------------------------------
-- Method description. (Map_4): 
-- This method is for computing the ending part of the map in Theorem 1.11 (when there is no middle map to compute)
-- Inputs: Rs, List including: 
--            F, polynomial ring w/o grading
--            R, polynomial ring w/ grading
--         I, ideal in question
--         L, List including: (this is necessary bc we can have only <=4 total parameters)
--           k, homology degree
--           j, index of Lambda to use (i.e. which path from a to b to use)
--           Lambda, List of paths from a to b  
--           paths
--         L2, List including: 
--             H, Matrix, basis for homology of K^bI
--             Ks, list of Koszul simplicial complexes along the path lambda
-- Outputs: G, Matrix, resulting sylvan matrix 
------------------------------------------------------------------------------------
Map_4 = method()
Map_4(List,Ideal,List,List):= (Rs,I,L,L2) -> (
    -- initialize objects --
    F = Rs#0;
    R = Rs#1;
    k = L#0;
    j = L#1;
    Lambda = L#2;
    ps = L#3;
    H = L2#0;
    Ks = L2#1;
    -- select path --
    lambda = Lambda#j;
    l = #lambda ;
    -- last index --
    ind = -1;
    -- calc dLambda_ell --
    U = dLambda(R,lambda,{ind,k},H);
    -- get basis for homology of K^aI --
    Ka = Ks#(min(keys(Ks)));
    hom = homology(k-1,Ka,F);
    hom1 = generators hom;

    if (flatten entries U)#0 != -1 and (flatten entries U)#0 != 1 and (flatten entries U)#0 != 0 then ret = Helper(U,Ka) else ret = (U,hom1);
    ret)
-------------------------------------------------------------------------------------
-- Method description. (Helper): 
-- This method finishes the computation of the sylvan map by expressing the result 
--    of the mappings as a linear comb. of elements in the basis for homology
-- Inputs: U, matrix, output of sylvan mappings
--         Ka, Kozsul simplicial complex in degree a 
-- Outputs: sylvan map, basis elts for homK^aI
-------------------------------------------------------------------------------------
Helper =method()
Helper(Matrix,SimplicialComplex) := (U,Ka) -> (
    -- transform result from dLambda into coefs --
    U2 = listForm((flatten entries U)_0);
    U3 = apply(U2, i-> i#1*i#0);
    U4 = sum(U3);
    -- represent basis in terms of all faces in appropriate degree (i.e. x,y,z instead of y,z)--
    h2 = faces(k-1,Ka);
    h3 = h2*hom1;
    h4 = apply(flatten entries h3, i->listForm i);
    h5 = apply(h4, j-> apply(j, i->i#1*i#0));
    h6 = apply(h5, k->sum(k));
    -- lift coefs into same ring --
    H2 = lift(matrix(h6),ZZ);
    U5 = lift(matrix{U4},ZZ);
    -- solve lin eq --
    if U != 0 then G = solve(transpose(H2),transpose(U5)) else G =0;
    G,h3
)

-------------------------------------------------------------------------------------
-- Method description. (sylvanMap): 
-- This method iterates over all choices (a,b) and choices of paths between a and b
-- Inputs: R, polynomial ring w/grading 
--         F, w/o grading
--         I, ideal
--         k, homology degree
-- Outputs: Q4, Hashtable where Q4#(degree a, degree b) = (basis elts for homK^aI, map between homology, basis elts for homK^bI)
-------------------------------------------------------------------------------------
sylvanMap = method()
sylvanMap(Ring,Ring,Ideal,ZZ):= (R,F,I,k)-> (
    -- initialize objects --
    Q = new MutableHashTable;
    Q2 = new MutableHashTable;
    Q3 = new MutableHashTable;
    Q4 = new MutableHashTable;
    -- get Bettis --
    Cs = bettiDs(F,I,k);   
    -- get paths between a,b --
    for i in 0..#Cs-1 do for j in 0..(#((Map_1(Cs,i,{R,F},I))#0))-1 do Q#(i,j,Cs#i) = Map_1(Cs,i,{R,F},I);
    -- calculate sylvanMap between each a,b for each lattice path --
    for ii in keys(Q) do Q2#ii= Map_2(F,R, I,{k, ii#1, Q#ii#0, Q#ii#1});
    -- sum over different lattice paths --
    for k in 0..#Cs-1 do Q3#k = sum(apply(delete(null,apply(keys(Q2), i -> if i#0 == k then i else null)), j-> (j,Q2#j)));
    -- organize into a final output hashTable
    for ii in values(Q3) do Q4#(take(ii#0,{2,3})) = ii#1;
    for ii in keys(Q4) do Q4#ii = deepSplice Q4#ii;
    -- remove pairs w/o a path --
    for ii in keys(Q4) do if #(Q4#ii)== 2 then remove(Q4,ii);
    for ii in keys(Q4) do Q4#ii = reverse(Q4#ii);
    Q4
)