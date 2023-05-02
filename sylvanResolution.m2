-------------------------------------------------------------------------------------
-- Method description. sylvanResolution():
-- This function computes the entire sylvan resolution (I.e. computes the differentials for all homology degrees)
-- Inputs: R, multigraded polynomial ring
--         I, ideal 
-- Outputs: H, List, where H#i = output Hashtable from sylvanMap(R,F,I,k)
-------------------------------------------------------------------------------------
sylvanResolution = method()  
sylvanResolution(Ring,Ring,Ideal):=(R,F,I) ->(
    -- iterate over all homology degrees in the resolution --
    -- By Hilbert Syzygy Thm we know the resolution is at most of length N (as computed below) --
    N = numgens R;
    SR ={};
    for i in 0..N-1 do SR = append(SR,(i,sylvanMap(R,F,I,i))); 
    SR
)
