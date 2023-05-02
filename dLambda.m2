-------------------------------------------------------------------------------------
-- Method description. (dLambda):
-- This method computes the value of the function labelled d_1^(lambda_j) of a given chain 
-- Inputs: R, polynomial ring
--         L, List of lists (degrees), (path lambda from degree a to degree b) 
--         L2, List with:
--            j, Integer, (index of interest) goes 1..l
--            k, homology degree
--         M, Matrix, the chain Tau
-- Output: Chain, the result of d^lambda_j(chain Tau) as defined in the paper
-------------------------------------------------------------------------------------
dLambda = method()
dLambda(Ring,List,List, Matrix) := (R,L,L2,M) -> (
    j = L2#0;
    k = L2#1;
    if k ==0 then ret = dLambda2(R,L,j,M);
    if k > 0 then ret = dLambda1(R,L,j,M);
    ret
)

dLambda1 = method()
dLambda1(Ring,List, ZZ, Matrix) := (R,L,j,M) -> (
    -- get direction moving in degree form --
    E0 = L#j;
    -- translate to an index --
    E = position(E0, i -> i != 0);
    -- record relevant info --
    M2 = substitute(M,F);
    m = flatten entries M2;
    n = (degree m_0)#0;
    Tau={};
    t = entries(M);
    t2 = apply(t, i-> listForm(i_0));
    t3 = apply(t2, i->apply(i,j-> j#1*j#0));
    Tau = flatten t3;
    -- get complexes and boundary maps --
    s = squareFree(n+1,F);
    s1 = monomialIdeal(s);
    S = simplicialComplex(s1);
    -- determine how to apply boundary map --
    bdy = boundary(n-1,S);
    b2 = apply(entries bdy, i-> apply(i,j->abs(j)));
    testTau = apply(Tau, i-> apply(i,j->abs(j)));

    holder = apply(testTau, i-> position(b2, j-> j == i));
    -- remove face in position lambda_j if there, if absent send to 0--
    holds = new MutableHashTable;
    for ii in 0..#holder-1 do holds#ii = (Tau#ii,entries bdy_(holder#ii));
    for ii in 0..#values(holds)-1 do if holds#ii#0#E ==0 then remove(holds,ii);
    for ii in keys(holds) do holds#ii = (holds#ii#0,replace(E,0,holds#ii#1));

    -- give the right sign -- 
    if bdy == 0 then bdy = matrix{new List from #(generators R):0_R};

    G = {};
    for i in keys(holds) do G = append(G, faces(n-2,S)*transpose(matrix{holds#i#1}));

    sum(G)
)

dLambda2 = method()
dLambda2(Ring,List, ZZ, Matrix) := (R,L,j,M) -> (
    -- get direction moving in degree form --
    E0 = L#j;
    -- translate to an index --
    E = position(E0, i -> i != 0);
   
    -- get correct degree --
    M2 = substitute(M,F)
    m = flatten entries M2;
    n = (degree m_0)#0; 
    Tau={};

    t = entries(M);
    t2 = apply(t, i-> listForm(i_0));
    t3 = apply(t2, i->apply(i,j-> j#1*j#0));
    Tau = flatten t3;  
    Tau2 ={};
    for ii in 0..#Tau-1 do if Tau#ii#E != 0 then Tau2 = append(Tau2,Tau#ii);

    s = squareFree(n+1,F);
    s1 = monomialIdeal(s);
    S = simplicialComplex(s1);

    s2 = squareFree(n,F);
    s3 = monomialIdeal(s2);
    S2 = simplicialComplex(s3);

    bdy = boundary(n-1,S);

    -- give the right sign -- 
    if bdy == 0 then bdy = matrix{new List from #(generators R):0_R};

    if Tau2 != {} then G = apply(Tau2, i-> bdy*transpose(matrix{i}));
    if Tau2 != {} then G2 = apply(G, i -> faces(n-2,S2)* i);
    try G2#0 else 0
)