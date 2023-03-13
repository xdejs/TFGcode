################################################################################################################
##
##  This file contains an implementation of an algorithm that checks whether in a group all elements 
##  are commutators
##
##  Created by Xabier de Juan Soriano on 2023
##  This file is part of the author's final degree dissertation.
##

################################################################################################################
##
##  OreTest2( G )
##          the program halts if and only if evert element of G is a commutator
##  
##  input:
##      G   : ordinary character table of the group G as a matrix with values with values in a cyclotomic field
##
##  output:
##      returns true if all the elements of G are commutators
##
OreTest2 := function(G)
    local g, x, repr, order, index_cent, new_repr;
    order := Order(G);
    if IsPermGroup(G) = false then G := Image(IsomorphismPermGroup(G)); fi; # we want permutations groups
    repr := [()]; # to store the different representative of the classes
    index_cent := 1; # cummulative sum of the index of the centralizers
    while order <> index_cent do
        new_repr := true;
        g := Comm(Random(G),Random(G));
        if g <> () then
            for x in repr do
            # first cheap conjugation test
            if CycleStructurePerm(x) = CycleStructurePerm(g) then
                if IsConjugate(G, x, g) then
                    new_repr := false;
                    break;
                fi;
            fi;
            od;
            if new_repr then
                Print(Length(repr),"\n");
                Append(repr,[g]);
                index_cent := index_cent + order/Size(Centralizer(G, g));
            fi;
        fi;
    od;
    return true;
end;