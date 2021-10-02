using Hecke

#=
The quadratic triple QT = [Q, L, c] is an n-dimensional ellipsoid with rational coefficients.
Where,
Q is an nxn symmetric matrix of the quadratic form , 
L is a rational column vector of length n &
c is a rational number
=#

#EXAMPLE 1a: 3-dimensional sphere
Q1 = matrix(QQ,3,3,[1 0 0; 0 1 0; 0 0 1]);
L1 = matrix(QQ,3,1,[1,1,1]);
c1 = 1;

#EXAMPLE 1b: 4-dimensional sphere
Q2 = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
L2 = matrix(QQ, 4, 1 ,[1,1,1,1]);
c2 = 3;

#EXAMPLE 1c: 6-dimensional sphere
Q3 = matrix(QQ,6,6,[1 0 0 0 0 0; 0 1 0 0 0 0; 0 0 1 0 0 0; 0 0 0 1 0 0; 0 0 0 0 1 0; 0 0 0 0 0 1]);
L3 = matrix(QQ,6,1,[1,0,1,0,2,0]);
c3 = fmpq(4//3);

#----------------------------------------------------------------------------------
#EXAMPLE 2: This is an example where the finite set is empty, i.e. there are no integers for which the inhomogeneous quadratic function is <= 0 
#Example of a quadratic triple that has no real solutions. So we will get an error message instead
Q4 = matrix(QQ,4,4,[1 0 0 0; 0 2 0 0; 0 0 3 0; 0 0 0 4]);
L4 = matrix(QQ,4,1,[1, 0, 1, 0]);
c4 = fmpq(13//5);

#----------------------------------------------------------------------------------
#EXAMPLE 3a: A random 7x7 symmetric metrix and the corresponding quadratic triple 
#This example has no real solutions
Q5 = matrix(QQ,7,7,[7//3 2//5 3//2 1//4 4 2//3 5//2; 2//5 6//11 1//4 3 2//5 5 1//6; 3//2 1//4 5//2 1 4//3 3 6; 1//4 3 1 4//8 7 11//4 9; 4 2//5 4//3 7 3//9 3//7 2//3; 2//3 5 3 11//4 3//7 2 1//13; 5//2 1//6 6 9 2//3 1//13 1//5]);
L5 = matrix(QQ,7,1,[1//14, 2//13, 3//12, 4//11, 5//10, 6//9, 7//8]);
c5 = fmpq(29//19);

#----------------------------------------------------------------------------------
#EXAMPLE 3b: A random 7x7 symmetric metrix and the corresponding quadratic triple 
#Q6 is not a positive definite matrix
Q6 = matrix(QQ,7,7,[1 0 1 0 1 0 1; 0 1 0 1 0 1 0; 1 0 1 0 1 0 1; 0 1 0 1 0 1 0; 1 0 1 0 1 0 1; 0 1 0 1 0 1 0; 1 0 1 0 1 0 1]);
L6 = matrix(QQ,7,1,[1//14, 0, 0, 1, 0, 0, 0]);
c6 = fmpq(2//9);

#-----------------------------------------------------------------------------
#-----------------------------------------------------------------------------
#Examples for closest_vectors()
#Example 1:
Lat1 = Zlattice(gram = matrix(QQ,3,3,[1,0,0,0,1,0,0,0,1]));
v1 = convert(Array{Union{RingElem, AbstractFloat, Integer, Rational},1},[-1,0,0]);
u1 = fmpq(3//5);

#Example 1:
Lat2 = Zlattice(gram = matrix(QQ,4,4,[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]));
v2 = convert(Array{Union{RingElem, AbstractFloat, Integer, Rational},1},[-1,-1,-1,-1]);
u2 = fmpq(41//11);

#Example 1:
Lat3 = Zlattice(gram = matrix(QQ,6,6,[1,0,0,0,0,0, 0,1,0,0,0,0, 0,0,1,0,0,0, 0,0,0,1,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1]));
v3 = convert(Array{Union{RingElem, AbstractFloat, Integer, Rational},1},[-1,0,-1,0,-2,0]);
u3 = fmpq(14//3);
