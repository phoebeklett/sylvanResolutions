-------------------------------------------------------------------------------------
-- Method description. (pathS): 
-- This method computes all paths between two given degrees
-- Inputs: aD, string representing monomial degree a
--         bD, string representing monomial degree b
--         R: polynomial Ring w/grading
-- Outputs: paths, List of lists (of monomials), each list is a path (of monomials) between a and b 
-------------------------------------------------------------------------------------
pathS = method()
pathS(String,String,Ring) := (aD,bD,R) ->(
    -- establish objects --
    g = generators R;
    a = monomialIdeal aD;
    b = monomialIdeal bD;

    a1 = substitute(a,R);
    b1 = substitute(b,R);

    -- get difference --
    c = b1_0/a1_0;
    -- get degree corresponding to monomial c -- 
    if liftable(c,R) then d = flatten exponents lift(c,R) else d = {};
    -- flatten out into single steps in one degree (direction) at a time --
    e ={};
    for i in 0..#d-1 do e = append(e, d#i:g#i);
    f = deepSplice(e);
    -- permute to get all possible sequences --
    paths = unique(permutations(f));
    p= new MutableHashTable;
    for i in 0..#paths-1 do p#i = {};
    for i in 0..#paths-1 do for j in 0..#paths#i-1 do p#i = append(p#i,product(take(paths#i,{0,j})));
    for i in 0..#p-1 do p#i = reverse(apply(p#i, i-> b1_0/i));
    for i in 0..#p-1 do p#i = prepend(a1_0,p#i);
    for i in 0..#p-1 do p#i = append(p#i,b1_0);
    for i in 0..#p-1 do p#i = apply(p#i, j-> lift(j,R));
    for i in 0..#p-1 do p#i = unique(p#i);
    values(p)
)