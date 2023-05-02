-------------------------------------------------------------------------------------
-- Method description. (delPlus): 
-- This method computes the hedge splitting of the differential, given a Hedge. See Definition 1.12. 
-- Inputs: R, multigraded polynomial ring
--         S, sequence of:
--            H, (Hedge) Sequence of two lists, (shrubbery in dim i, stake set in dimension i-1)
--            K, SimplicialComplex, (upper Kozsul simplicial complex in appropriate degree )
--            i, integer, degree of splitting
--            d, Matrix, chain to apply splitting 
-- Outputs: Ring element, (Chain) - result of of Del^+_i (b) as given in Definition 1.12 
-------------------------------------------------------------------------------------
delPlus = method()
delPlus(Ring, Sequence) :=(R,S) -> (
    H = S#0;
    K = S#1;
    i = S#2;
    d = S#3;

    T = H#0;
    S = H#1;

    -- take boundary of faces in shrubbery --
    B = boundary(i,simplicialComplex(T)); -- matrix form --
    try Bs = flatten(entries(matrix{generators R} * B)) then Bs = flatten(entries(matrix{generators R} * B)) else Bs = flatten(entries(transpose(matrix{generators R}) * B));
    -- in list/ring elt form --

    -- get elements of complement of stake set --
    A = flatten(entries(faces(i-1,K)));
    if A#0 == 1 then Sc = {0} else Sc = apply(A, i -> if any(S, j -> R_(toString(j)) == R_(toString(i))) then null else i);
    Scf = delete(null,Sc);
    b0 ={};
    C= {};
    try for i in 0..#Scf-1 do for j in 0..#(Scf#i)-1 do b0 = append(b0, characters(toString(Scf#i#j))) else C={};
    try for i in 0..#b0-1 do C = append(C,apply(b0#i, j -> degree(R_(toString(j))))) else C={};
    if C != {} then D = transpose(matrix(apply(C, i->sum(i)))) else D =matrix{{0}};

    -- concatenate 2 matrices --
    P = B | D;

    -- represent x as linear comb of above two --
    t = entries(d);
    t2 = apply(t, i-> listForm(i_0));
    t3 = apply(t2, i->apply(i,j-> j#1*j#0));
    t4 = sum(flatten t3);
    if t4 == toList(#t4:0) then t4 = flatten t;

    P1 = lift(P,ZZ);
    d1 = lift(matrix{t4},ZZ);
    if d1 !=0 then w = solve(P1,transpose(d1)) else w =0;

    -- evaluate w in its new form  -- 
    if w != 0 then t = flatten(entries(w)) else t = {};
    if t != {} then step1 = take(t,#Bs) else step1 = {0};
    if t != {}  then step2 = take(t,{#Bs,#t}) else step2 ={0};

    q = {};
    for i in 0..#step1-1 do if step1#i != 0 then q = append(q,(step1#i)*T#i);
    for i in 0..#step2-1 do if step2#i != 0 then q = append(q,(step2#i)*Scf#i);
    sum(q) 
)