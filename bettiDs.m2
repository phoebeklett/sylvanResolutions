-------------------------------------------------------------------------------------
-- Method description. (bettiDs): 
-- This method produces all pairs of degrees (a,b) s.t. a has nonzero Betti no. in homological degree k-1 and b has nonzero Betti no. in homological degree k
-- Inputs: F, (Polynomial Ring), Poly Ring over which you want to work (w/o Degree specification)
--        I, (Monomial Ideal), Ideal in question
--        k, (integer), degrees of homology of interest are k, k-1
-- Output: C, (List), contains all pairs of degrees (a,b) where a,b 
--                   have non-zero Betti # in homology degree k-1, k (respectively)
-------------------------------------------------------------------------------------
bettiDs = method()
bettiDs(Ring,Ideal, ZZ) := (F,I,k) -> (
    -- establish objects --
    M = I;
    LM = lcmLattice M;
    H = new MutableHashTable;
    As = new MutableHashTable;
    Bs = new MutableHashTable;
    -- check for non-zero homology in degrees k, k-1 --
    for i in 0..(#(LM_*))-1 do if homology(k,upperKoszul(F,M,monomialIdeal(LM_i)),F) != 0 then Bs#(LM_i) = numgens prune homology(k,upperKoszul(F,M,monomialIdeal(LM_i)),F);
    for i in 0..(#(LM_*))-1 do if homology(k-1,upperKoszul(F,M,monomialIdeal(LM_i)),F) != 0 then As#(LM_i) = numgens prune homology(k-1,upperKoszul(F,M,monomialIdeal(LM_i)),F);
    C ={};
    k1 = keys(As);
    k2 = keys(Bs);
    -- pass back all the combinations of (a,b) --
    for i in 0..#As-1 do for j in 0..#Bs-1 do C = append(C,(k1#i,k2#j));
    unique(C);
    -- make sure no a's are 1 --
    D = {};
    for ii in 0..#C-1 do if C#ii#0 != 1 then D = append(D,C#ii);
    D
)