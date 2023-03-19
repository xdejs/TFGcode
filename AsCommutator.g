################################################################################
##
##  This file contains an implementation of an algorithm that writes any even 
##  permutation as a commutator of two even permutations.
##
##  Created by Xabier de Juan Soriano on 2022
##  This file is part of the author's final degree dissertation.
##

DeclareGlobalFunction("CyclesToList");
DeclareGlobalFunction("CommutatorEvenPair");
DeclareGlobalFunction("CommutatorOddCycle");
DeclareGlobalFunction("AsCommutatorLists");

################################################################################
##
#M  AsCommutator( permutation )
##
##  This is the function that the user must call in order to write any even
##  permutation as a commutator of two even permutations.
##  
##  input: 
##      permutation: an even permutation, $r \in A_n$ (the value of n is assumed 
##                      to be the smallest such thatr \in A_n)
##      If the permutation is not even an error message is raised.
##
##  output: 
##      <list>[1]: even permutation $\phi \in A_n$
##      <list>[2]: even permutation $\psi \in A_n$
##      r = [\phi,\psi]
##
AsCommutator := function(permutation)
    local list;
    if SignPerm(permutation) = -1 then Error("permutation must be an even permutation"); fi;
    list := CyclesToList(permutation);
    return AsCommutatorLists(list[1],list[2],list[3]);
end;

################################################################################
##
##  AsCommutatorLists( cycles, cycles2, cycles3 )
##
##  This is function is not supposed to be used by the user
##  
##  input: 
##      cycles  : a list containing cycles of odd order
##      cycles2 : a list containing pairs of cycles of even order
##      cycles3 : a list containing 3-cycles
##          The cycle (a,b,c) corresponds to the list [ a , b , c ]      
##          in this setting.
##
##  output: 
##      The same as the main function
##
InstallGlobalFunction(AsCommutatorLists, function(cycles, cycles2, cycles3)
    local a, b, phi, psi, c, l, l1, l2, m, k, aux, max;

    # the particular cases
    aux := 0; # we will use this later
    # when we only have a cycle of order 3
    if  Length(cycles) = 0 and Length(cycles2) = 0 and Length(cycles3) = 1 then
        a := cycles3[1];
        max := Maximum(a);
        if max < 5 then max := 5; fi;
        b := [1..max];
        RemoveSet(b, a[1]);
        RemoveSet(b, a[2]);
        RemoveSet(b, a[3]);
        a := Concatenation(a, [b[Length(b)-1], b[Length(b)]]);
        return [(a[1] ,a[5], a[2]),(a[3], a[4], a[2])];
    fi;
    # when we only have a pair of a 2-cycle and a 4-cycle
    if Length(cycles) = 0 and Length(cycles3) = 0 and Length(cycles2) = 1 then
        # we know that Length(cycles2[1][1]) <= Length(cycles2[1][2])
        # this is because we are applying the function "CylesToList"
        if Length(cycles2[1][1]) = 2 and Length(cycles2[1][2]) = 4 then
            a := Concatenation(cycles2[1][2], cycles2[1][1]);
            return [(a[1],a[6],a[2],a[4],a[3]), (a[1],a[2],a[5],a[4],a[6])];
        fi;
    fi;
    # when we only have a pair of 2-cycles
    if Length(cycles) = 0 and Length(cycles3) = 0 and Length(cycles2) = 1 then
        if Length(cycles2[1][1]) = 2 and Length(cycles2[1][2]) = 2 then
            a := Concatenation(cycles2[1][1], cycles2[1][2]);
            return [ (a[1],a[3])(a[2],a[4]) , (a[1],a[4],a[3])  ];
        fi;
    fi;

    # the general case
    phi := ();
    psi := ();
    # the output will be: [phi,psi]
    for c in cycles do 
        l := CommutatorOddCycle(c);
        phi := phi*l[1];
        psi := psi*l[2];
    od;
    # divide cases, if there are zero 3-cycles or >=2
    if Length(cycles3) <> 1 then
        for c in cycles2 do 
            l := CommutatorEvenPair(c[1],c[2]);
            phi := phi*l[1];
            psi := psi*l[2];
        od;
        for c in cycles3 do 
            l := CommutatorOddCycle(c);
            phi := phi*l[1];
            psi := psi*l[2];
        od;
    else # if there is only one 3-cycle
        if cycles <> [] then
            for c in cycles2 do 
                l := CommutatorEvenPair(c[1],c[2]);
                phi := phi*l[1];
                psi := psi*l[2];
            od;
            l := CommutatorOddCycle(cycles3[1]);
            phi := phi*l[1];
            psi := psi*l[2];
            # from here we jump to "if SignPerm(phi) = -1 then"
        elif cycles2 <> [] then # redundant?
            for c in cycles2 do
                a := c[1];
                b := c[2];
                k := Length(a)/2;
                m := Length(b)/2 + k;
                if m >= 4 then
                    for c in cycles2 do 
                        l := CommutatorEvenPair(c[1],c[2]);
                        phi := phi*l[1];
                        psi := psi*l[2];
                    od;
                    l := CommutatorOddCycle(cycles3[1]);
                    phi := phi*l[1];
                    psi := psi*l[2];
                    aux := 1;
                    break;
                    # from here we jump to "if SignPerm(phi) = -1 then"
                fi;
            od;
            # if we end up here that means that we are in the situation of the final part of the proof
            if aux = 0 then
                c := cycles3[1];
                a := cycles2[1][1];
                b := cycles2[1][2];
                if Length(b) = 2 then #2x2
                    a := Concatenation(c,a,b);
                    l1 := [a[4], a[5], a[6]];
                    l2 := [a[4], a[7], a[6]];
                    phi := phi * (a[1],a[2]) * MappingPermListList(l2,Reversed(l1));
                    psi := psi * (a[1],a[3],a[2]) * CycleFromList(l2);
                    if SignPerm(phi) = -1 then 
                        phi := (a[1],a[4])*(a[3],a[7])*(a[2],a[6])*phi;
                    fi; 
                else # 2x4
                    a := Concatenation(c,a,b);
                    phi := phi*(a[1],a[2] ) * (a[4], a[8], a[6], a[5], a[9], a[7]);
                    psi := psi*(a[1], a[3], a[2]) *( a[4], a[5], a[9], a[8], a[6]);
                fi;
                # compute the rest in any case
                for c in cycles2{[2..Length(cycles2)]} do 
                        l := CommutatorEvenPair(c[1],c[2]);
                        phi := phi*l[1];
                        psi := psi*l[2];
                od;
            fi;
        fi; 
    fi;

    #in order to ensure that phi \in An
    if SignPerm(phi) = -1 then
        # if there is some odd cycle it is easy to ensure phi \in An
        # we wil assume that the number of 3-cycles != 1
        if cycles <> [] then
            a := cycles[1];
            m := QuoInt(Order(CycleFromList(a)),2);
            # as it is said in the proof of the thm
            if m mod 2 = 0 then
                return [ (a[2],a[3])*phi, psi];
            else 
                return [ (a[3],a[4])*phi, psi];
            fi;
        fi;
        # if there is some pair of even permutations to whom we have applied the lemma is easy to see phi \in An
        if cycles2 <> [] then
            for c in cycles2 do
                a := c[1];
                b := c[2];
                k := Length(a)/2;
                m := Length(b)/2 + k;
                if m >= 4 then
                    a := Concatenation(a,b);
                    # as in the proof
                    if m mod 2 = 0 then
                        return [(a[2],a[m])*phi, psi];
                    else
                        return [(a[4],a[m+1])*phi, psi];
                    fi;
                fi;
            od;
        fi;
        # if there is an odd number of 3-cycles
        if Length(cycles3) mod 2 = 1 then
            a := Concatenation(cycles3[1],cycles3[2]);
            return [(a[1],a[4])*(a[3],a[6])*(a[2],a[5])*phi,psi];
        fi;
    fi;
    return [phi, psi];
end);

################################################################################
##
##  CommutatorOddCycle( cycle )
##
##  "cycle" is a list
##  Writes a cycle of odd length as a product of two cycles of odd length 
##
InstallGlobalFunction(CommutatorOddCycle, function(cycle)
    # cycles is a list
    local m, l1, l2, phi;
    m := QuoInt(Order(CycleFromList(cycle)),2);
    if m mod 2 = 0 then
        l1 := cycle{[1..m+1]};
        l2 := Concatenation([cycle[1]], cycle{[m+2..2*m+1]});
    elif m = 1 then
        return [ (cycle[1],cycle[2]) , (cycle[1],cycle[3],cycle[2])  ];
    else # m odd and m>=5
        l1 := Concatenation([cycle[1]], [cycle[m+2]], cycle{[2..m+1]});
        l2 := Concatenation([cycle[1]], [cycle[m+2]], [cycle[2]], cycle{[m+3..2*m+1]});
    fi;
    phi := MappingPermListList(l2, Reversed(l1));
    return [phi, CycleFromList(l2)];
end);

################################################################################
##
##  CommutatorEvenPair( t1, t2 )
##
##  t1 and t2 are lists. It writes a product of two cycles of even length as a 
##  product of two cycles of odd length 
##
InstallGlobalFunction(CommutatorEvenPair, function(t1, t2)
    # t1 and t2 are lists
    local k, m, t, cycle, l1, l2, phi;
    # we can suppose that Length(t1) <= Length(t2)
    k := Length(t1)/2;
    m := Length(t2)/2 + k;
    cycle := Concatenation(t1, t2);
    # some particular cases
    if m = 3 then
        cycle := Concatenation(t2,t1);
        return [(cycle[1],cycle[6],cycle[2],cycle[4],cycle[3]),(cycle[1],cycle[2],cycle[5],cycle[4],cycle[6])];
    elif m = 2 then
        return [ (cycle[1], cycle[3])*(cycle[2], cycle[4]) , (cycle[1], cycle[4], cycle[3])];
    fi;
    # the general case
    if m mod 2 = 0 then
        l1 := cycle{[1..m+1]};
        l2 := Concatenation([cycle[1]], cycle{[m+2..2*m]},[cycle[2*k+1]]);
    else 
        l1 := Concatenation([cycle[1], cycle[m+2]], cycle{[2..m+1]});
        l2 := Concatenation([cycle[1], cycle[m+2], cycle[2]], cycle{[m+3..2*m]},[cycle[2*k+1]]);
    fi;
    phi := MappingPermListList(l2, Reversed(l1));
    return [phi, CycleFromList(l2)];
end);

InstallGlobalFunction(CyclesToList, function(permutation)
    # outputs a list with the disjoint cycles of "permutation"
    local cycles, cycles2, cycles22, cycles3, lista, l, j, c, e, N;
    N := Length(ListPerm(permutation));
    cycles := [];
    cycles2 := [];
    cycles22 := [];
    cycles3 := [];
    l := [1..N];
    while l <> [] do
        c := Cycle(permutation,l[1]);
        for e in c do
            RemoveSet(l,e);
        od;
        # cycles of order dont appear in the disjoint cycle decomposition
        if Length(c) >= 2 then
            # we want to divide the cycles of odd order, even order and 3-cycles 
            if Length(c) mod 2 = 0 then # cycles of even order
                cycles2 := Concatenation(cycles2,[c]);
            elif Length(c) = 3 then # 3-cycles
                cycles3 := Concatenation(cycles3, [c]);
            else # cycles of odd order
                cycles := Concatenation(cycles,[c]); 
            fi;
        fi;
    od;
    # write in pairs the cycles of even order
    if Length(cycles2) mod 2 = 0 then
        for e in [1,3..Length(cycles2)-1] do
            # in order to ensure that the one with smallest order appears in the left
            if Length(cycles2[e]) > Length(cycles2[e+1]) then
                cycles22 := Concatenation(cycles22,[ [cycles2[e+1], cycles2[e] ] ]);
            else
                cycles22 := Concatenation(cycles22,[ [cycles2[e], cycles2[e+1] ] ]);
            fi;
        od;
    fi;
    return [cycles, cycles22, cycles3];
end);