-------------------------------------------------------------------------------------
-- Method description. (lambdaGen): 
-- This method computes all paths between two given degrees
-- Inputs: aD, string representing monomial degree a
--         bD, string representing monomial degree b
--         R: polynomial Ring w/grading
-- Outputs: paths, List of lists, each list is a path between a and b 
-------------------------------------------------------------------------------------
lambdaGen = method()
lambdaGen(String,String,Ring) := (aD,bD,R) ->(
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
    Da = degree a1_0;
    Db = degree b1_0;
    paths1 = apply(paths, j->apply(j,i -> degree i));

    paths1
)