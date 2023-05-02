-------------------------------------------------------------------------------------
-- Method description. (upperKoszul): 
-- This method computes the upper Koszul Simplicial Complex of given Ideal and degree
-- Inputs: F, polynomial ring -- NOT MULTIGRADED 
--        I, Ideal in question
--        b, monomial Ideal containing the one monomial degree in question   
-- Outputs: List of faces in Koszul Simplicial Complex (empty face is implicitly included)
-------------------------------------------------------------------------------------
upperKoszul = method()
upperKoszul(Ring,Ideal,Ideal) := (F,J,b) -> (
    -- establish objects --
    I = substitute(J,F);
    D = {};
    K = {};
    c = numgens F;
    irrelevant = simplicialComplex monomialIdeal gens F; -- empty complex --
    -- get all possible faces (square free) --
    for i in 1..c  do D = append(D, squareFree(i,F));

    -- make sure Rings match --
    d ={};
    C ={};
    e  =flatten(exponents b_0);
    for i in 0..#e-1 do d= append(d, e#i:(generators F)#i);
    for i in 0..#d-1 do for j in 0..#d#i-1 do C= append(C,F_(toString(d#i#j)));
    f = product(C);

    -- test if the resulting face (stepped backwards) is in I, add if yes, skip if no --
    for i in 0..#D-1 do for j in 0..numgens(D#i)-1 do if liftable(f/D#i_j,F) and isSubset(ideal(lift(f/D#i_j,F)),I) then K = append(K,D#i_j);
    -- return complex of all faces which passed --
    if K != {} then simplicialComplex K else irrelevant
)