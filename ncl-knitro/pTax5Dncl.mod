# pTax5Dncl.mod	
# An NLP to solve a taxation problem with 5-dimensional types of tax payers.
# 
# 29 Mar 2005: Original AMPL coding for 2-dimensional types by K. Judd and C.-L. Su.
# 20 Sep 2016: Revised by D. Ma and M. A. Saunders.
# 08 Nov 2016: 3D version created.
# 08 Dec 2016: 4D version created.
# 10 Mar 2017: Piece-wise smooth utility function created.
# 12 Nov 2017: pTax5Dncl.mod derived from pTax5D.mod.
# 08 Dec 2017: pTax5Dncl files added to multiscale website.

# Define parameters for agents (taxpayers)
param na;                # number of types in wage
param nb;                # number of types in eta
param nc;                # number of types in alpha
param nd;                # number of types in psi
param ne;                # number of types in gamma
set A := 1..na;          # set of wages
set B := 1..nb;          # set of eta
set C := 1..nc;          # set of alpha
set D := 1..nd;          # set of psi
set E := 1..ne;          # set of gamma
set T = {A,B,C,D,E};     # set of agents

# Define wages for agents (taxpayers)
param wmin;              # minimum wage level
param wmax;              # maximum wage level
param w {A};             # i, wage vector
param mu{B};             # j, mu = 1/eta# mu vector
param mu1{B};            # mu1[j] = mu[j] + 1
param alpha{C};          # k, ak vector for utility 
param psi{D};            # g
param gamma{E};          # h
param lambda{A,B,C,D,E}; # distribution density 
param epsilon; 
param primreg     default 1e-8;  # Small primal regularization

var c{(i,j,k,g,h) in T} >= 0.1;  # consumption for tax payer (i,j,k,g,h)
var y{(i,j,k,g,h) in T} >= 0.1;  # income      for tax payer (i,j,k,g,h) 
var R{(i,j,k,g,h) in T, (p,q,r,s,t) in T:
      !(i=p and j=q and k=r and g=s and h=t)};  # >= -1e+20, <= 1e+20;

param kmax      default 20;         # limit on NCL itns
param rhok      default 1e+2;       # augmented Lagrangian penalty parameter
param rhofac    default 10.0;       # increase factor
param rhomax    default 1e+8;       # biggest rhok
param etak      default 1e-2;       # opttol for augmented Lagrangian loop
param etafac    default  0.1;       # reduction factor for opttol
param etamin    default 1e-8;       # smallest etak
param rmax      default    0;       # max r (for printing)
param rmin      default    0;       # min r (for printing)
param rnorm     default    0;       # ||r||_inf
param rtol      default 1e-6;       # quit if biggest |r_i| <= rtol

param nT        default    1;       # nT = na*nb*nc*nd*ne
param m         default    1;       # nT*(nT-1) = no. of nonlinear constraints
param n         default    1;       # 2*nT      = no. of nonlinear variables

param ck{(i,j,k,g,h) in T} default 0;        # current variable c
param yk{(i,j,k,g,h) in T} default 0;        # current variable y
param rk{(i,j,k,g,h) in T, (p,q,r,s,t) in T: # current variable r = - (c(x) - s)
   !(i=p and j=q and k=r and g=s and h=t)} default 0;
param dk{(i,j,k,g,h) in T, (p,q,r,s,t) in T: # current dual variables (y_k)
   !(i=p and j=q and k=r and g=s and h=t)} default 0;

minimize f:
   sum{(i,j,k,g,h) in T}
   (
      (if c[i,j,k,g,h] - alpha[k] >= epsilon then
          - lambda[i,j,k,g,h] *
               ((c[i,j,k,g,h] - alpha[k])^(1-1/gamma[h]) / (1-1/gamma[h])
                - psi[g]*(y[i,j,k,g,h]/w[i])^mu1[j] / mu1[j])
       else
          - lambda[i,j,k,g,h] *
         (-   0.5/gamma[h] * epsilon^(-1/gamma[h]-1) * (c[i,j,k,g,h] - alpha[k])^2
          + ( 1+1/gamma[h])* epsilon^(-1/gamma[h]  ) * (c[i,j,k,g,h] - alpha[k])
          + (1/(1-1/gamma[h]) - 1 - 0.5/gamma[h]) * epsilon^(1-1/gamma[h])
                - psi[g]*(y[i,j,k,g,h]/w[i])^mu1[j] / mu1[j])
      )
   + 0.5 * primreg * (c[i,j,k,g,h]^2 + y[i,j,k,g,h]^2)
   )
 + sum{(i,j,k,g,h) in T, (p,q,r,s,t) in T: !(i=p and j=q and k=r and g=s and h=t)}
       (dk[i,j,k,g,h,p,q,r,s,t] * R[i,j,k,g,h,p,q,r,s,t]
                   + 0.5 * rhok * R[i,j,k,g,h,p,q,r,s,t]^2);

subject to

Incentive{(i,j,k,g,h) in T, (p,q,r,s,t) in T:
          !(i=p and j=q and k=r and g=s and h=t)}:
   (if c[i,j,k,g,h] - alpha[k] >= epsilon then
      (c[i,j,k,g,h] - alpha[k])^(1-1/gamma[h]) / (1-1/gamma[h])
       - psi[g]*(y[i,j,k,g,h]/w[i])^mu1[j] / mu1[j]
    else
       -  0.5/gamma[h] *epsilon^(-1/gamma[h]-1)*(c[i,j,k,g,h] - alpha[k])^2
       + (1+1/gamma[h])*epsilon^(-1/gamma[h]  )*(c[i,j,k,g,h] - alpha[k])
       + (1/(1-1/gamma[h]) - 1 - 0.5/gamma[h])*epsilon^(1-1/gamma[h])
       - psi[g]*(y[i,j,k,g,h]/w[i])^mu1[j] / mu1[j]
   )
 - (if c[p,q,r,s,t] - alpha[k] >= epsilon then
      (c[p,q,r,s,t] - alpha[k])^(1-1/gamma[h]) / (1-1/gamma[h])
       - psi[g]*(y[p,q,r,s,t]/w[i])^mu1[j] / mu1[j]
    else
       -  0.5/gamma[h] *epsilon^(-1/gamma[h]-1)*(c[p,q,r,s,t] - alpha[k])^2
       + (1+1/gamma[h])*epsilon^(-1/gamma[h]  )*(c[p,q,r,s,t] - alpha[k])
       + (1/(1-1/gamma[h]) - 1 - 0.5/gamma[h])*epsilon^(1-1/gamma[h])
       - psi[g]*(y[p,q,r,s,t]/w[i])^mu1[j] / mu1[j]
   )
 + R[i,j,k,g,h,p,q,r,s,t] >= 0;

Technology:
   sum{(i,j,k,g,h) in T} lambda[i,j,k,g,h]*(y[i,j,k,g,h] - c[i,j,k,g,h]) >= 0;
