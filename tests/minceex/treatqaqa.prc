#procedure treatqaqa
*
*   Treat routine for d_(ka,la)-P(ka)*P(la)/P.P on gluonic currents
*   Insertion is a photon current.
*
*  #[ Physics :
*
#ifndef `ONLYINTEGRAL'
Multiply,g_(1,P);
#if `PROJ' == 2
Multiply P(MU)*P(NU)/Q.Q;
#else
Multiply d_(MU,NU);
#endif
*
*Print +f +s;
.sort:Physics;
*
*  #] Physics :
*  #[ feynman :
sum mu,mu1,nu,nu1,mu2,nu2,mu3,nu3,mu4,nu4,ro,ro1,si,si1,ka,ka1,la,la1;
sum mu5,nu5,mu6,nu6,mu7,nu7,mu8,nu8,mu9,nu9,mu10,nu10;
*
Multiply i_;
*
#call intpow(`TOPO')

id  fp(ii1?,p?) = i_*g_(ii1,p)/p.p;
id  vqg(ii1?,mu?) = i_*g_(ii1,mu);
id  fp(ii1?,p?,1) = i_*g_(ii1,p)/p.p*quark1*epexp(p,1);
id  fp(ii1?,p?,2) = i_*g_(ii1,p)/p.p*quark2*epexp(p,2);
id  fp(ii1?,p?,3) = i_*g_(ii1,p)/p.p*quark3*epexp(p,3);
id  vgh(p?,mu?) = i_*p(mu);
id  Dg(ii1?,ii2?,p?,1) = DL(ii1,ii2,p)*gluon1*epexp(p,1);
id  Dg(ii1?,ii2?,p?,2) = DL(ii1,ii2,p)*gluon2*epexp(p,2);
id  Dg(ii1?,ii2?,p?,3) = DL(ii1,ii2,p)*gluon3*epexp(p,3);
id  Dgh(p?,1) = Dgh(p)*ghost1*epexp(p,1);
id  Dgh(p?,2) = Dgh(p)*ghost2*epexp(p,2);
id  Dgh(p?,3) = Dgh(p)*ghost3*epexp(p,3);
id  Dgh(p?) = i_/p.p;

id	epexp( p?pp[x1],x?) = (epppp[x1])^x/epQ^x;
id	epexp(-p?pp[x1],x?) = (epppp[x1])^x/epQ^x;

id  DL(ii1?,ii2?,p?) = -i_*(d_(ii1,ii2)-p(ii1)*p(ii2)/p.p)/p.p;
.sort
#call vertsubm
#ifdef `GAUGE'
#if ( `GAUGE' >= 0 )
    if ( count(xi,1) > `GAUGE' ) discard;
#endif
#endif
.sort:Vertex substitutions;

id  g_(ii1?,P,Q,[P+Q]) = [P+Q].[P+Q]*g_(ii1,P);
id	g_(ii1?,[P+Q],Q,P) = [P+Q].[P+Q]*g_(ii1,P);
id  P.P = 0;

.sort:Vertex identities;

tracen,3;
tracen,2;
tracen,1;
id  P.P = 0;
id D = rat(4-2*ep,1);
id [D-4] = rat(-2*ep,1);

.sort:Traces;
#endif

*  #] feynman :
*  #[ Psub :
#do i = 1,8
id  [P+p`i'] = P+p`i';
id  [P-p`i'] = P-p`i';
#enddo
id  [P+Q] = P+Q;
id  [P-Q] = P-Q;
id  P.P = 0;

.sort:moms0;
#call symtopo(`TOPO')
.sort:symtopo;
#call momsubs(`TOPO')
.sort:momsubs;
id  P.P = 0;
#call scalars(`TOPO')
id  P = proexp*P;
if ( count(proexp,1) > {`POW'+`PROJ'} ) discard;
id  epexp([P+Q],x?) = epexp( proexp*2*P.Q/Q.Q,x);
id  epexp([P-Q],x?) = epexp(-proexp*2*P.Q/Q.Q,x);
id  epexp(p?[pp18][D],x?)  = epppp[D]^x/epQ^x
    *epexp( 2*proexp*P.pp18[D]/pp18[D].pp18[D],x);
id  epexp(p?[-pp18][D],x?) = epppp[D]^x/epQ^x
    *epexp(-2*proexp*P.pp18[D]/pp18[D].pp18[D],x);
#do i = 1,8
if ( count([P+p`i'].[P+p`i'],1) < 0 );
    repeat;
      id,once,proexp^x?/[P+p`i'].[P+p`i'] = (
        sum_(k,0,{`POW'+`PROJ'}-x,2^k*proexp^k*P.p`i'^k/p`i'.p`i'^k*sign_(k))
      )*proexp^x/p`i'.p`i';
    endrepeat;
endif;
if ( count([P-p`i'].[P-p`i'],1) < 0 );
    repeat;
      id,once,proexp^x?/[P-p`i'].[P-p`i'] = (
        sum_(k,0,{`POW'+`PROJ'}-x,2^k*proexp^k*P.p`i'^k/p`i'.p`i'^k)
      )*proexp^x/p`i'.p`i';
    endrepeat;
endif;
#enddo
if ( count([P+Q].[P+Q],1) < 0 );
    repeat;
      id,once,proexp^x?/[P+Q].[P+Q] =
        (sum_(k,0,{`POW'+`PROJ'}-x,2^k*proexp^k*P.Q^k/Q.Q^k*sign_(k)))*proexp^x/Q.Q;
    endrepeat;
endif;
if ( count([P-Q].[P-Q],1) < 0 );
    repeat;
      id,once,proexp^x?/[P-Q].[P-Q] =
        (sum_(k,0,{`POW'+`PROJ'}-x,2^k*proexp^k*P.Q^k/Q.Q^k))*proexp^x/Q.Q;
    endrepeat;
endif;

repeat;
    id,once,proexp^x?*epexp(y?,D?) =
    sump_(k,0,{`POW'+`PROJ'}-x, y*rat((-D*ep-k+1),k))*proexp^x;
    if ( count(P.P,1) > 0 ) discard;
    if ( count(proexp,1) > {`POW'+`PROJ'} ) discard;
endrepeat;
if ( count(proexp,1) != {`POW'+`PROJ'} ) discard;
id  proexp^{`POW'+`PROJ'} = 1;
.sort:Expand in P;
*
*   Now convert the metric:
*
id,many,P?.Q?^D?=sign_(D)*P.Q^D;
#call momsubs(`TOPO')
#call sym2(`TOPO')
.sort:sym2;
*
#call harmproj(P,Q,ftensor)
.sort:harmonics;
*  #] Psub :
#endprocedure
