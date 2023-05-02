-------------------------------------------------------------------------------------
-- Method description. (hedge_trimmer): 
-- This method computes Hedge ST_I (in specified degree i)
-- Inputs: K, SimplicialComplex, (in most cases upper Kozsul simplicial complex)
--         i, homological degree 
-- Outputs: Shrubbery (Ti) in dimension i (first entry in output)
--          Stake Set (S(i1)) in dimension i-1 (second entry in output)
-------------------------------------------------------------------------------------
hedge_trimmer = method()
hedge_trimmer(SimplicialComplex, ZZ) := (K,i) -> (
    -- get shrubbery --
    bi = boundary(i,K);
    r = reducedRowEchelonForm bi;
    p = pivots(r);
    p1 = apply(p, i -> i#0);
    p2 = unique(p1);

    f = flatten(entries(faces(i,K)));
    v = new MutableHashTable;
    scan(0 .. #f-1, i -> v#i = f#i);

    Ti = apply(p2, i -> v#i);

    -- get stake set --
    bi1 = transpose(bi); -- same map transposed --
    -- flip matrix to take pivots from right to left --
    n ={};
    for i in 0..#(entries bi1)-1 do n = append(n,reverse(entries bi1)#i);
    r0 = matrix n;
    r1 = reducedRowEchelonForm r0;
    p3 = pivots(r1);
    p4 = apply(p3, i -> i#0);
    p5 = unique(p4);

    f1 = reverse(flatten(entries(faces(i-1,K))));
    v1 = new MutableHashTable;
    scan(0 .. #f1-1, i -> v1#i = f1#i);

    Si1 = apply(p5, i -> v1#i);

    Ti,Si1
)