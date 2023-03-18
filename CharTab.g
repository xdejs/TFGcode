################################################################################
##
##  This file contains an implementation of an algorithm which computes computes
##  the table of irreducible characters of any finite group.  
##
##  Created by Xabier de Juan Soriano on 2023
##  This file is part of the author's final degree dissertation.
##

DeclareGlobalFunction("NewPrint");
DeclareGlobalFunction("FieldToMod");
DeclareGlobalFunction("BestMat");
DeclareGlobalFunction("ClassMap");
DeclareGlobalFunction("ClassMatrixColumn");
DeclareGlobalFunction("ClassMatrix");

################################################################################
##
##  CharTab( G, permRepr[, mode] )
##
##  Computes the table of irreducible characters of G using a simplified version
##  of the Burnside/Dixon/Schneider algorihm.
##  
##  input: 
##      G             : finite group.
##      permRepr      : if equal to true, a permutation representation of G is
##                          computed so all the computations are performed in
##                          this permutation group.
##                          Otherwise, the computations are performed in a matrix
##                          group or in the structure that the given group has.
##      mode(optional): when mode="silent" the program doesn't print any text
##                          regarding the progress of the computation. 
##                          Omiting this argument can be helpful when dealing 
##                          with large groups as it can help the user to 
##                          estimate how much time of computation is left.
##
##  output: 
##      <list>[1]: table of characters of G as a matrix 
##                  (the rows are sorted by the degree)
##      <list>[2]: representatives of the conjugacy classes of G in the same
##                  order as the columns of the character table.
##
##  remarks: if the user is only interested in the values of the character 
##              table, it is recommended to call the function with
##              true as a second argument, since the computations
##              will be performed faster in that case.
##
CharTab := function(G, permRepr, mode...)
    local CT, i, j, k, l, m, v, d2, x, sqrtt, Bv, K, A, s, V_i, V_, B_, b, h, D_, pol, I, q, prev;

    # we want permutation groups
    if permRepr = true and IsPermGroup(G) = false then G := Image(IsomorphismPermGroup(G)); fi;
    if IsPermGroup(G) then permRepr := true; fi;

    CT := rec();

    NewPrint(mode, "computing conjugacy classes...");
    CT.order := Size(G);
    CT.C := ConjugacyClasses(G);
    CT.CO := List(CT.C, c -> Size(c));
    CT.g := List(CT.C, c -> Representative(c));
    CT.r := Length(CT.C);
    CT.gO := List(CT.g, x -> Order(x));
    CT.e := Lcm(CT.gO);
    NewPrint(mode, "complete");
    NewPrint(mode, " " );

    CT.invClassMap := List([1..CT.r],j->ClassMap(CT.g[j]^-1, CT.C, permRepr));
    CT.powClassMap := List([1..CT.r],j->List([0..CT.gO[j]-1],l->ClassMap(CT.g[j]^l, CT.C, permRepr)));
    

    NewPrint(mode, "finding the prime number p...");
    CT.p := 2*Int(CT.order^0.5)+1;
    while IsPrimeInt(CT.p) = false or RemInt(CT.p-1,CT.e) <> 0 do
        CT.p := CT.p + 2;
    od;
    NewPrint(mode, "complete");
    NewPrint(mode, " ");

    NewPrint(mode, "computing the eigenvalues of the matrices M_j...");
    CT.M := List([1..CT.r], x-> IdentityMat(CT.r)-IdentityMat(CT.r));
    CT.TM := List([1..CT.r], x-> IdentityMat(CT.r)-IdentityMat(CT.r));
    CT.M[1] := IdentityMat(CT.r);
    j := PositionMinimum(List(CT.C{[2..CT.r]}, c -> Size(c))) + 1;
    
    CT.M[j] := ClassMatrix(CT.C, CT.g, j, CT.r, permRepr);
    CT.TM[j] := Z(CT.p)^0 * CT.M[j];
    
    CT.V := Eigenspaces(GF(CT.p), CT.TM[j]);
    CT.D := List(CT.V, v -> Dimension(v));
    CT.B := List(CT.V, v -> Basis(v));

    while CT.D <> List(CT.D, v -> 1) do
        NewPrint(mode, "-----");
        NewPrint(mode, "Dimension of the eigenspaces (we want a list full of 1s):");
        NewPrint(mode, String(CT.D));
        i := Difference([1..Length(CT.D)],Positions(CT.D,1)); # list of the V_i with dim V_i > 1
        Bv := List(i, v -> BasisVectors(CT.B[v])); # bases of the V_i
        I := Length(i); # V_1,...,V_I
        s := List([1..I], v -> Length(Bv[v]));
        K := List([1..I], v -> [1..s[v]]); # the columns of M_j we need to compute
        for v in [1..I] do
            for m in [1..s[v]] do
                K[v,m] := PositionNot(Bv[v,m],0*Z(CT.p));
            od;
        od;
        j := BestMat(K,CT.g,CT.r,CT.CO,CT.C,permRepr); 
        A := ShallowCopy(TransposedMat(CT.M[j]));
        for k in K do
            for l in k do
                if A[l] = List([1..CT.r],x->0) then 
                    # we only compute the ones that have not been computed yet
                    # if a row is all 0 means that it has not been computed yet
                    A[l] := ClassMatrixColumn(CT.C, CT.g, j, CT.r, l, permRepr);
                fi;
            od;
        od;
        # we do not compute the whole matrix M_j, only the columns we need
        CT.M[j] := TransposedMat(A);
        # compute the eigenvalues of the action of TM[j] on V_i for each V_i
        prev:=0;
        for v in [1..I] do
            A := List([1..s[v]], x -> (Bv[v,x]*CT.M[j]){K[v]});
            V_i := Eigenspaces(GF(CT.p), A);
            h := Length(V_i);
            V_ := [1..h];
            for q in [1..h] do
                b := BasisVectors(Basis(V_i[q]));
                V_[q] := VectorSpace(GF(CT.p), List(b, x -> x*Bv[v]  ) );
            od;
            B_ := List(V_, q -> Basis(q));
            D_ := List(V_, q -> Dimension(q));
            # update the V, B and D vectors
            Remove(CT.V,i[v]+prev);
            CT.V := Concatenation(V_,CT.V);
            Remove(CT.B,i[v]+prev);
            CT.B := Concatenation(B_,CT.B);
            Remove(CT.D,i[v]+prev);
            CT.D := Concatenation(D_,CT.D);
            prev := prev + Length(D_)-1;
        od;
    od;
    NewPrint(mode, "complete");
    NewPrint(mode, " ");

    # convert the eigenvectors of F_p to integers mod p
    CT.B := List(CT.B, v -> FieldToMod(v[1]));
    # normalize the eigenvectors to ensure that the first component equals 1
    CT.B := List(CT.B, v -> PowerModInt(v[1],-1,CT.p) * v);
    NewPrint(mode, "computing Theta[X]");
    # compute Theta(X)
    CT.TX := IdentityMat(CT.r);
    for i in [1..CT.r] do
        d2 := CT.order * PowerModInt(Sum([1..CT.r],j -> Size(CT.C[j]) * CT.B[i,j] * CT.B[i, CT.invClassMap[j]] mod CT.p ), -1, CT.p);
        sqrtt:= RootMod(d2, CT.p);
        if 2*sqrtt >= CT.p then 
            CT.TX[i] := AbsInt(sqrtt-CT.p)*CT.B[i] mod CT.p;
        else
            CT.TX[i] := sqrtt*CT.B[i] mod CT.p;
        fi;
    od;
    NewPrint(mode, "complete");

    NewPrint(mode, "recovering X from Theta X...");
    CT.omega := IntFFE(Z(CT.p)^((CT.p-1)/CT.e)); # element with multiplicative order e (as an integer < p)
    CT.m := List([1..CT.e], x -> IdentityMat(CT.r) );
    # pre-compute some values
    CT.powOrder := List([1..CT.r],j->PowerModInt(CT.gO[j],-1,CT.p));
    for i in [1..CT.r] do
        for j in [1..CT.r] do
            s := CT.gO[j]; # order of g[j]
            for k in [1..CT.e] do
                if (k-1) mod (CT.e/s) = 0 then 
                    CT.m[i,j][k] := ( CT.powOrder[j] * Sum([0..s-1],l-> PowerModInt(CT.omega,-(k-1)*l,CT.p) * CT.TX[i, CT.powClassMap[j,l+1]] mod CT.p  )) mod CT.p;
                else
                    CT.m[i,j][k] := 0;
                fi;
            od;
        od;
    od;
    NewPrint(mode, "complete");
    NewPrint(mode, "writing the character table...");
    # write the character table
    CT.X := IdentityMat(CT.r)-IdentityMat(CT.r);
    CT.Zeta := E(CT.e);
    for i in [1..CT.r] do
        for j in [1..CT.r] do
            #pol := List([1..CT.e], k-> CT.m[i,j][k]);
            CT.X[i,j] := ValuePol(CT.m[i,j], CT.Zeta);
        od;
    od;
    NewPrint(mode, "sorting the rows of the table");
    # sort the table by degrees
    SortBy(CT.X, x -> x[1]);
    # first character must be the trivial one
    j := Position(CT.X, List([1..CT.r],x->1));
    CT.X_ := ShallowCopy(CT.X);
    CT.X_[1] := CT.X[j];
    CT.X_[j] := CT.X[1];
    return [CT.X_, CT.g];
end;

################################################################################
##
##  ClassMatrix( C, g, j, r )
##
##  Computes the class matrix M_j.
##
##  input: 
##      C : conjugacy classes of G
##      g : representatives of the conj. classes 
##          (it is assumed that it is given in the same order as C)
##      j : integer with 1<=j<=r 
##      r : # of conj. classes
##
InstallGlobalFunction(ClassMatrix, function(C, g, j, r, permRepr)
    local l, M;
    M := IdentityMat(r);
    for l in [1..r] do
        M[l] := ClassMatrixColumn(C, g, j, r, l, permRepr);
    od;
    return TransposedMat(M);
end);

################################################################################
##
##  ClassMatrixColumn( C, g, j, r, l, permRepr )
##
##  Computes the l-th column of the class matrix M_j. It is returned as a row
##
InstallGlobalFunction(ClassMatrixColumn, function(C, g, j, r, l, permRepr)
    local x, y, z, k, c, v;
    z := g[l];
    v := List([1..r], x -> 0);
    # the first column is easy to compute
    if l = 1 then
        v[ClassMap(g[j]^-1, C, permRepr)] := Size(C[j]);
        return v;
    fi;
    for x in C[j] do
        y := x^-1*z;
        k := ClassMap(y,C,permRepr);
        v[k] := v[k] + 1;
    od;
    return v; # this is a row
end);

################################################################################
##
##  ClassMap( g, C )
##
##  Computes the image of g under the class map
##  C is a list of all the conjugacy classes
##
InstallGlobalFunction(ClassMap, function(g, C, permRepr)
    local c, j, possible, x; 
    if permRepr = true then
        possible := Filtered([1..Length(C)], x->CycleStructurePerm(Representative(C[x]))=CycleStructurePerm(g));
    else # this is way we prefer permutation groups
        possible := Filtered([1..Length(C)], x->Order(Representative(C[x]))=Order(g));
    fi;
    if Length(possible) = 1 then return possible[1]; fi;
    j := 1;
    while j < Length(possible) do
        if g in C[possible[j]] then
            return possible[j];
        else
            j := j+1;
        fi;
    od;
    return possible[j];
end);

################################################################################
##
##  BestMat( K, g, r, CO, C )
##
##  Returns the value j such that computing the matrix M_j is the best option
##
InstallGlobalFunction(BestMat, function(K, g, r, CO, C, permRepr)
    local j, j_, k, best, val, columns;
    best := [1,0];
    columns := [];
    for j in [2..r] do
        columns := [];
        j_ := ClassMap(g[j]^-1, C, permRepr);
        val := 0;
        for k in K do
            UniteSet(columns,k);
            if Position(k,j_) <> fail then
                val := val + 1;
            fi;
        od;
        val := val/CO[j];
        val := val/Size(columns);
        if best[2] < val then
            best[2] := val;
            best[1] := j;
        fi;
    od;
    return best[1];
end);

InstallGlobalFunction(FieldToMod, function(V)
    local x;
    return List(V, x -> IntFFE(x));
end);

InstallGlobalFunction(NewPrint, function(mode, str)
    if mode = [] then
        Info(InfoWarning,1,str);
    fi;
end);