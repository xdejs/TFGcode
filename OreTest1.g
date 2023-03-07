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
##  OreTest1( CT )
##  
##  input:
##      CT  : ordinary character table of the group G as a matrix with values with values in a cyclotomic field
##          https://docs.gap-system.org/doc/ref/chap18.html
##
##  output:
##      returns true if all the elements of G are commutators and false otherwise
##
OreTest1 := function(CT)
    local i, j, r;
    r := Length(CT);
    CT := TransposedMat(CT);
    for i in [2..r] do
        if Sum([1..r], j->CT[i,j]/CT[1,j]) = 0 then
            return false;
        fi;
    od;
    return true;
end;