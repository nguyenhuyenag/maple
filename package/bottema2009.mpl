#lprint(` (1)BOTTEMA USER GUIDE ---`):
#lprint(` `):
#lprint(`    JUST TYPE  prove(ineq) or xprove(ineq) or yprove(ineq) `):
#lprint(`    WHERE ineq IS THE INEQUALITY TO BE PROVEN`):
#lprint(` `):
#lprint(` (2)Dictionary for Geometric Invariants of a Triangle`):
#lprint(` `):
#lprint(`    a, b, c,            lengths of sides of the triangle`):
#lprint(`    s,                  s:=(a+b+c)/2, half the perimeter`):
#lprint(`    x, y, z,            x:=s-a, y:=s-b, z:=s-c,`):
#lprint(`    R,                  circumradius`):
#lprint(`    r,                  radius of the incircle`):
#lprint(`    ra, rb, rc,         radii of excircles, respectively`):
#lprint(`    ha, hb, hc,         altitudes respectively`):
#lprint(`    ma, mb, mc,         lengths of medians, respectively`):
#lprint(`    wa, wb, wc,         bisectors of angles, respectively`):
#lprint(`    S,                  Area of the triangle`):
#lprint(`    d,                  distance from circumcenter to incenter`):
#lprint(`    p,                  p:=4*r*(R-2*r)`):
#lprint(`    q,                  q:=s^2-16*R*r+5*r^2`):
#lprint(`    A, B, C,            angles of the triangle, respectively`):
#lprint(`    sin(A),             sines of the angles, respectively`):
#lprint(`   `):
#lprint(`    other trigonometric functions denoted analogously`):
#lprint(`    abs( ),                absolute value (used in Maple)`):
#lprint(` `):

#lprint(` Warning...`):
#lprint(`    These geometric invariants are protected in BOTTEMA!`):
#lprint(`    It's a demo version of BOTTEMA.`):

################################################################################
protect(a,b,c,x,y,z,p,q,s,T,A,B,C,ra,rb,rc,ha,hb,hc,ma,mb,mc,wa,wb,wc,HA,HB,HC,
        IA,IB,IC,Ha,Hb,Hc,S,R,r,Ra,Rb,Rc,GA,GB,GC,JA,JB,JC,ca,cb,cc,Ja,Jb,Jc,Q):

AcuteAngle:=(x-1)*(y-1)*(z-1)>0:
ObtuseAngle:=(x-1)*(y-1)*(z-1)<0:
CGR:=0:
TURNOFFCGR:=0:
################################################################################

turnoff:=proc()
	global TURNOFFCGR;
	TURNOFFCGR:=1:
	print(`Warning: user turns off the cgr class determination on the input inequality.`);
end:

turnon:=proc()
	global TURNOFFCGR;
	TURNOFFCGR:=0:
	print(`Warning: user turns on the cgr class determination on the input inequality.`);
end:

prove:=proc(ineq)
   local tt,iq,xl,yl,temp,neq,iqlst,i,lst:
   global gg,hh,aa;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:

xl:={x=y,y=z,z=x,a=b,b=c,c=a,ra=rb,rb=rc,rc=ra,ha=hb,hb=hc,hc=ha,
ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:

	if whattype(args[1])=`=` then RETURN(`The input argument should be inequality.`);fi;

   if nargs>2 then RETURN(`invalid arguments`);fi;
   if nargs=2 and not type(args[2],list) then RETURN(`invalid second argument`);fi;
   if nargs=2 then dprove(args);RETURN();fi;
   if iscgr(args[1])<>1 then dprove(args);RETURN();fi;

   lst:=parseABC(args);
   if lst[1]=1 then prove(op(lst[2]));Assume(lst[3]);RETURN();fi;

   iqlst:=[args[1]]; #ineq
   if nargs=2 then
      for i to nops(args[2]) do
         if not (type(args[2][i],`<`) or type(args[2][i],`<=`)) then
            iqlst:=[op(iqlst),args[2][i]>=0];
         else
            iqlst:=[op(iqlst),args[2][i]];
         fi;
      od;
   fi;
   yl:=[];
   for i to nops(iqlst) do
      if has(iqlst[i],abs) then 
         yl:=[op(yl),deleteabs(lhs(iqlst[i]))<=deleteabs(rhs(iqlst[i]))];
      else yl:=[op(yl),iqlst[i]];
      fi;
   od;
   iqlst:=yl;

   temp:=1;
   for i to nops(iqlst) while temp=1 do
      temp:=cyclicornot(iqlst[i]);
      if i>1 then
         if hastype(iqlst[i],radical) then temp:=-1;fi;
      fi;
   od;

   iq:=iqlst[1];
   if temp=1 then
      iq:=[subs(s=x+y+z,iq)]:
print(iq[1]);
      if nargs=2 then
         tt:=ctest(lhs(iq[1]),rhs(iq[1]),subsop(1=NULL,iqlst))
      else tt:=test(lhs(iq[1]),rhs(iq[1]))
      fi:
      if tt=`less` then print(`The inequality holds`,time());#RETURN(+1)
      elif tt=`greater` then print(`The inequality inversely holds`,time());
      fi:
   else

xl:=data():
      print(`The original inequality`);
print(args[1]);
      print(`is equivalent to the following inequalities:`);
      iqlst:=[op(iqlst),x*y>1];
      iqlst:=map(expand,iqlst);
      iqlst:=subs(aa=(x-1)*(y-1)*(z-1),iqlst);
      iqlst:=subs(xl,iqlst);
      iqlst:=subs(z=(x+y)/(x*y-1),iqlst);
print(iqlst);      
      xprove(iqlst[1],subsop(1=NULL,iqlst));
   fi;
end:

parseABC:=proc(inargs)
   local lstIn,lstOut,i,n,iq,its,cs,iqlst,cqlst,exit,nA,hasABC;
   
   iq:=args[1];
   its:=indets(iq);
   lstOut:=[];cs:={};exit:=0;hasABC:=1;
   if not has(its,{A,B,C}) then 
      hasABC:=0;lstOut:=[0];
      if nargs=1 then RETURN(lstOut);fi;
   fi;
   its:=its minus {A,B,C};
   if has(its,{A,B,C}) then lstOut:=[0];RETURN(lstOut);fi;
   
   if hasABC=1 then cs:={lhs(iq),rhs(iq)};iq:=map(cos,lhs(iq)>=rhs(iq));fi;
   iqlst:=[iq];
   if nargs=1 then lstOut:=[1,iqlst,[op(cs)]];RETURN(lstOut);fi;
   
   lstIn:=args[2];
   n:=nops(lstIn);
   cqlst:=[];exit:=0;nA:=0;
   for i to n do
      iq:=lstIn[i];
      its:=indets(iq);
      if not has(its,{A,B,C}) then nA:=nA+1;cqlst:=[op(cqlst),iq];next;fi;

      its:=its minus {A,B,C};
      if has(its,{A,B,C}) then cqlst:=[op(cqlst),iq];exit:=1;break;fi;
      
      cs:={op(cs),lhs(iq),rhs(iq)};
      iq:=map(cos,lhs(iq)>=rhs(iq));
      cqlst:=[op(cqlst),iq];
   od;
   iqlst:=[op(iqlst),cqlst];
   lstOut:=[1,iqlst,[op(cs)]];
   if nA=n and hasABC=0 then exit:=1;fi;
   if exit=1 then lstOut:=[0,[args],[]];fi;
   lstOut;
end:

Assume:=proc(cs)
   local str,cslst;
   
   cslst:={op(cs)} minus {A,B,C,0,Pi,Pi/2};
   cslst:=[op(cslst)];
   if cslst=[] then RETURN();fi;
   
   str:=cat(`Assume that each member of the list `,convert(cslst,string),` lies in the interval `,convert([0,Pi],string),`.`);
   lprint(str);
end:

dprove:=proc(ineq)
   local tt,iq,ex,i,p1,p2,ep1,ep2,temp,xl,its1,its2,its,iqlst,yl:
   global gg,hh,aa;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:
#data base

if whattype(args[1])=`=` then RETURN(`The input argument should be inequality.`);fi;
   if nargs>2 then RETURN(`invalid arguments`);fi;
   if nargs=2 and not type(args[2],list) then RETURN(`invalid second argument`);fi;

xl:=data():
   iqlst:=[ineq];
   if nargs=2 then
      for i to nops(args[2]) do
         if not (type(args[2][i],`<`) or type(args[2][i],`<=`)) then
            iqlst:=[op(iqlst),args[2][i]>=0];
         else iqlst:=[op(iqlst),args[2][i]];
         fi;
      od;
   fi;
print(iqlst);
   yl:=[];
   for i to nops(iqlst) do
      if has(iqlst[i],abs) then 
         yl:=[op(yl),deleteabs(lhs(iqlst[i]))<=deleteabs(rhs(iqlst[i]))];
      else yl:=[op(yl),iqlst[i]];
      fi;
   od;
   iqlst:=yl;

   temp:=1;
   for i to nops(iqlst) while temp=1 do
      temp:=cyclicornot(iqlst[i]);
      if i>1 then
         if hastype(iqlst[i],radical) then temp:=-1;fi;
      fi;
   od;
print(iqlst);
   iq:=iqlst[1];
   if temp<>1 then
      iqlst:=[op(iqlst),x*y>1];
      iqlst:=subs(aa=(x-1)*(y-1)*(z-1),iqlst);
      iqlst:=map(expand,iqlst);
      iqlst:=subs(xl,iqlst);
      iqlst:=subs(z=(x+y)/(x*y-1),iqlst);
      xprove(iqlst[1],subsop(1=NULL,iqlst));
      RETURN();
   fi;

print(iq);
   ep1:=lhs(iq);
   ep2:=rhs(iq);

   ep1:=subs(xl,expand(ep1));ep2:=subs(xl,expand(ep2));
   if nargs=2 then
      tt:=ctest(lhs(iq),rhs(iq),subsop(1=NULL,iqlst),ep1,ep2)
   else tt:=test(lhs(iq),rhs(iq),ep1,ep2)
   fi:
   if tt=`less` then print(`The inequality holds`,time())
   elif tt=`greater` then print(`The inequality inversely holds`,time());
   fi:
end:

findsamp:=proc(a,var)
   local b,c,m,i,n,k,xl,yl,inf,sup,temp,range;
   
   b:=a;
   m:=nops(b);
   k:=34;
   readlib(realroot);
   xl:=[];yl:=[];
   for i to m do
      temp:=realroot(b[i],2^(-k));
      if temp<>[] then
         xl:=[op(xl),op(realroot(b[i],2^(-k)))];
         yl:=[op(yl),b[i]];
      fi;
   od;
   n:=nops(xl);
   inf:=[]; sup:=[];
   for i to n do
      inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
   od;
   inf:=sort(inf);sup:=sort(sup);

   range:=[[inf[1]-2,inf[1]]];
   temp:=1;
   for i to n-1 while temp=1 do
      range:=[op(range),[sup[i],inf[i+1]]];
      if sup[i]>=inf[i+1] then temp:=-1;fi;
   od;
   range:=[op(range),[sup[n],sup[n]+2]];

   b:=yl;m:=nops(b);
   while temp=-1 do
      k:=k+33;
      xl:=[];
      for i to m do
         xl:=[op(xl),op(realroot(b[i],2^(-k)))];
      od;
      n:=nops(xl);
      inf:=[]; sup:=[];
      for i to n do
         inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
      od;
      inf:=sort(inf);sup:=sort(sup);

      range:=[[inf[1]-2,inf[1]]];
      temp:=1;
      for i to n-1 while temp=1 do
         range:=[op(range),[sup[i],inf[i+1]]];
         if sup[i]>=inf[i+1] then temp:=-1;fi;
      od;
      range:=[op(range),[sup[n],sup[n]+2]];
   od;

   xl:=[];
   for i to n+1 do
      xl:=[op(xl),(range[i][1]+range[i][2])/2];
   od;

   n:=nops(xl); inf:=[];
   k:=13:
   for i to n do
      m:=1:
      temp:=convert(evalf(xl[i],k),fraction,m);
      while temp<=range[i][1] or temp>=range[i][2] do
         m:=m+1;
         k:=k+1:
         temp:=convert(evalf(xl[i],k),fraction,m);
      od;
      inf:=[op(inf),temp];
   od;
   inf;
end:

mdp:=proc(a,b)
   if a+b mod 2=0 then RETURN((a+b)/2);
   else RETURN((a+b-1)/2);
   fi;
end:

deleteabs:=proc(expr)
   local i,its,ex;
   
   ex:=expr;
   its:=indets(ex):
   while has(ex,abs)=true do
      for i to nops(its) do
         if op(0,its[i])=abs
         then ex:=subs(its[i]=sqrt(op(1,its[i])^2),ex)
         fi
      od:
      its:=indets(ex):
   od:
   ex;
end:

cyclicornot:=proc(ineq)
   local ep,xl,xl1,xl2,xl3,A1,A2,A3,A4;

xl:={x=y,y=z,z=x,a=b,b=c,c=a,ra=rb,rb=rc,rc=ra,ha=hb,hb=hc,hc=ha,
ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:
xl1:={x=y,y=x,a=b,b=a,ra=rb,rb=ra,ha=hb,hb=ha,ma=mb,mb=ma,wa=wb,wb=wa,
HA=HB,HB=HA,IA=IB,IB=IA,Ha=Hb,Hb=Ha,A=B,B=A,Ra=Rb,Rb=Ra,GA=GB,GB=GA,
JA=JB,JB=JA,ca=cb,cb=ca,Ja=Jb,Jb=Ja}:
xl2:={x=z,z=x,a=c,c=a,ra=rc,rc=ra,ha=hc,hc=ha,ma=mc,mc=ma,wa=wc,wc=wa,
HA=HC,HC=HA,IA=IC,IC=IA,Ha=Hc,Hc=Ha,A=C,C=A,Ra=Rc,Rc=Ra,GA=GC,GC=GA,
JA=JC,JC=JA,ca=cc,cc=ca,Ja=Jc,Jc=Ja}:
xl3:={z=y,y=z,c=b,b=c,rc=rb,rb=rc,hc=hb,hb=hc,mc=mb,mb=mc,wc=wb,wb=wc,
HC=HB,HB=HC,IC=IB,IB=IC,Hc=Hb,Hb=Hc,C=B,B=C,Rc=Rb,Rb=Rc,GC=GB,GB=GC,
JC=JB,JB=JC,cc=cb,cb=cc,Jc=Jb,Jb=Jc}:

   if hastype(ineq,`<`) or hastype(ineq,`<=`) then
      ep:=lhs(ineq)-rhs(ineq);
      if has(ineq,mid) then ep:=subs(mid=min,ep);fi;
      A1:=expand(subs(xl1,ep)-ep);
      A2:=expand(subs(xl2,ep)-ep);
      A3:=expand(subs(xl3,ep)-ep);

      if A1=0 and A2=0 and A3=0 then RETURN(1)
      else
         A4:=expand(subs(xl,ep)-ep);
         if A4=0 then RETURN(0);else RETURN(-1);fi;
      fi;
   else
      ep:=ineq;
      if has(ineq,mid) then ep:=subs(mid=min,ep);fi;
      A1:=expand(subs(xl1,ep)-ep);
      A2:=expand(subs(xl2,ep)-ep);
      A3:=expand(subs(xl3,ep)-ep);
      if A1=0 and A2=0 and A3=0 then RETURN(1)
      else
         A4:=expand(subs(xl,ep)-ep);
         if A4=0 then RETURN(0);else RETURN(-1);fi;
      fi;
   fi;
end:

solvecubic:=proc(x,y,z)
   local _l,_m,_n,_xa,_xb,_xc,_x1,_x2,_x3;
   
   _l:=x;_m:=y;_n:=z;
   _xa:=simplify(2/3*(_l^2-3*_m)^(1/2));
   _xb:=simplify(1/2*(2*_l^3-9*_l*_m+27*_n)/(_l^2-3*_m)^(3/2));
   _xc:=simplify(-_l/3);
   _x1:=_xa*cos(1/3*Pi-1/3*arccos(_xb))+_xc:
   _x2:=-_xa*cos(1/3*arccos(_xb))+_xc:
   _x3:=_xa*sin(1/6*Pi-1/3*arccos(_xb))+_xc:
   [_x1,_x2,_x3];
end:

########################################################
##                                                    ##
##   PROGRAM `test` USER GUIDE:                       ##
##                                                    ##
##     JUST TYPE `test(expr1,expr2):`                 ##
##                                                    ##
##       WHERE `expr1`,`expr2` AS ORIGINAL AS GIVEN   ##
##                                                    ##
########################################################
test:=proc(expr1,expr2)
   local po1,po2,p1,p2,ret:

   if nargs=2 then
      print(`Start to solve the left polynomial  `,time());
      po1:=psTpoly(expr1):
      print(`Start to solve the right polynomial  `,time());
      po2:=psTpoly(expr2):
   elif nargs=4 then
      print(`Start to solve the left polynomial  `,time());
      po1:=psTpoly(expr1,x);
      print(`Start to solve the right polynomial  `,time());
      po2:=psTpoly(expr2,x);
   else
   	print(`invalid arguments in test procedure.`);
   fi;

   p1:=subs(s=sqrt(4*p+q+27),po1):
   p2:=subs(s=sqrt(4*p+q+27),po2):
   p1:=collect(expand(p1),T);p2:=collect(expand(p2),T);

   if type(p1,polynom)=true and type(p2,polynom)=true then
      print(`LpolypqT:  length= `,nops(p1),` T degree := `,degree(p1,T));
      print(`RpolypqT:  length= `,nops(p2),` T degree := `,degree(p2,T));
      if nargs=2 then ret:=ie2(p1,p2,p,q,T,hh);
      elif nargs=4 then ret:=ie2(p1,p2,p,q,T,hh,args[3],args[4]);
      fi;
   else
      if has(po1,{q}) then po1:=subs(q=s^2-4*p-27,po1);po1:=collect(expand(po1),T);fi;
      if has(po2,{q}) then po2:=subs(q=s^2-4*p-27,po2);po2:=collect(expand(po2),T);fi;

      print(`LpolypsT:  length= `,nops(po1),` T degree := `,degree(po1,T));
      print(`RpolypsT:  length= `,nops(po2),` T degree := `,degree(po2,T));

      if nargs=2 then ret:=ie2(po1,po2,p,s,T,gg);
      elif nargs=4 then ret:=ie2(po1,po2,p,s,T,gg,args[3],args[4]);
      fi;
   fi:
   RETURN(ret)
end:


#################################################
##                                             ##
## subprogram `maxmidmin` eliminating radicals ##
##         and trigonometric functions         ##
##                                             ##
#################################################
maxmidmin:=proc(expr)
   local ex,rp,i,p1,p2,temp:
   
   ex:=expr:
   if has(ex,{max,mid,min})=false  then rp:=ex
   elif op(0,ex)=max or op(0,ex)=min or op(0,ex)=mid then
      rp:=ex
   elif op(0,ex)=`*` and has(ex,{max,min,mid}) and nops(ex)=2 then
      p2:=1;
      for i to 2 do
         temp:=op(i,ex);
         if has(temp,{max,min,mid}) then p1:=temp;
         else p2:=p2*temp;
         fi;
      od;
      if not hastype(p2,string) and min(p2,0)=0 then
         ex:=op(0,p1)(p2*op(1,p1),p2*op(2,p1),p2*op(3,p1));
         rp:=ex;
      else RETURN(`please use standard input`);
      fi;
   else RETURN(`please use standard input`);
   fi:
   rp:
end:


##################################################
##                                              ##
##   a loop `rads` eliminating multi-radicals   ##
##                                              ##
##################################################
rads:=proc(expr)
   local ep,np,i,nq,j,rad,nr,rp,ob,ob1,ob2,tmp1,tmp2:

   ep:=expand(expr);
   rad:=efindrads(expr);

   if rad={} then RETURN(ep)
   else 
      rad:=[op(rad)]:
      rad:=ord(rad):
      nr:=nops(rad):

      for i from nr to 1 by -1 do ep:=subs(rad[i]=uu[i],ep):od;
      ep:=simplify(ep,radical,symbolic);
      while hastype(ep,radical) do
         tmp1:=indets(ep);tmp1:=[op(tmp1)];
         for i to nops(tmp1) do
            ob:=tmp1[i];
            if hastype(ob,radical) then
               for j to nr do 
                  if op(1,rad[j])=op(1,ob) then ep:=subs(ob=uu[j]^numer(op(2,ob)),ep) fi;
               od;
            fi;
         od;
      od;

      for i to nr do  
         if i<>nr then 
            for j from i+1 to nr do 
               if hastype(rad[i],name) then
                  rad[j]:=subs(op(1,rad[i])=uu[i]^denom(op(2,rad[i])),rad[j]):
                  if member(uu[i],indets(rad[j])) then 
                     tmp1:=op(1,rad[j]);tmp2:=op(2,rad[j]);
                     rad[j]:=expand(simplify(tmp1,radical,symbolic))^tmp2;
                     rad[j]:=subs(csgn(uu[i])=1,rad[j]);
                  fi;
               else  rad[j]:=subs(rad[i]=uu[i],rad[j]);
               fi;
            od;
         fi;
      od:
      ep:=simplify(ep,radical,symbolic);
      ep:=numer(ep);
      for i from nr to 1 by -1 do
         ob1:=op(1,rad[i]):  ob2:=op(2,rad[i]):
         ob:=ob1^numer(ob2)-uu[i]^denom(ob2):
         ob:=numer(ob);
         ep:=resultant(ep,ob,uu[i]):
      od:
   fi:
   if whattype(ep)=`^` then ep:=op(1,ep) fi;
   ep
end:

efindrads:=proc(expr)
   local ep,np,rad,i,j,ob,nq;

   ep:=expand(expr): np:=nops(ep): rad:={}: 
#print(ep):
   if type(ep,radical) then 
      if hastype(ep,name) then
         rad:={op(1,ep)^(1/denom(op(2,ep)))} union efindrads(op(1,ep));
      else
         rad:={ep} union efindrads(op(1,ep));
      fi;
      RETURN(rad);
   fi;

   for i to np do
      ob:=op(i,ep):
      if type(ob,radical) then 
      if hastype(ob,name) then
         rad := rad union {op(1,ob)^(1/denom(op(2,ob)))} union efindrads(op(1,ob)): 
      else
         rad := rad union {ob} union efindrads(op(1,ob)):
      fi;
      else 
         nq:=nops(ob):
         for j to nq do
            if type(op(j,ob),radical) then 
               rad:=rad union efindrads(op(j,ob));
            fi;
         od
      fi:
   od:
   rad
end:

ord:=proc(lst1)
   local lst,tmp,n,i,j,m,k;

   lst:=lst1;n:=nops(lst);
   for i to n-1 do
      for j from i+1 to n do
         m:=denom(op(2,lst[j]));
         if hastype(lst[j],name) then
            for k to m-1 do
               if has(lst[i],op(1,lst[j])^(k/m)) then tmp:=lst[i]; lst[i]:=lst[j]; lst[j]:=tmp fi;
            od;
         else
            if has(lst[i],lst[j]) then tmp:=lst[i]; lst[i]:=lst[j]; lst[j]:=tmp fi;
         fi;
      od;
   od;   
   lst
end:

###################################################
##                                               ##
##   subprogram `psTpoly` creating polynomial(s) ##
##       with standard parameters `p`,`s`        ##
##                                               ##
###################################################
psTpoly:=proc(expr)
   local ex,m,n,nn,i,j,k,_A,_B,_C,xl,yl,t,tt,co,temp;

   ex:=expr;
if   ex=wa+wb+wc then ex:=waT
elif ex=ma+mb+mc then ex:=maT
elif ex=GA+GB+GC then ex:=subs(T=3/2*T,maT)
elif ex=IA+IB+IC then ex:=IAT

elif ex=ga+gb+gc then ex:=gaT
elif ex=NA+NB+NC then ex:=NAT
elif ex=KA+KB+KC then ex:=KAT
elif ex=JA+JB+JC then ex:=JAT


elif ex=1/wa+1/wb+1/wc then ex:=dwaT
elif ex=1/ma+1/mb+1/mc then ex:=dmaT
elif ex=1/IA+1/IB+1/IC then ex:=dIAT

elif ex=1/ga+1/gb+1/gc then ex:=dgaT
elif ex=1/NA+1/NB+1/NC then ex:=dNAT

elif ex=wb*wc+wc*wa+wa*wb then ex:=wbmwcT
elif ex=mb*mc+mc*ma+ma*mb then ex:=mbmmcT

elif ex=GB*GC+GC*GA+GA*GB then ex:=subs(T=9/4*T,mbmmcT)

elif ex=a*wa+b*wb+c*wc then ex:=amwaT
elif ex=a*ma+b*mb+c*mc then ex:=ammaT
elif ex=ma*wa+mb*wb+mc*wc then ex:=mamwaT

elif ex=kb*kc+kc*ka+ka*kb then ex:=kbmkcT
elif ex=KB*KC+KC*KA+KA*KB then ex:=KBmKCT
elif ex=JB*JC+JC*JA+JA*JB then ex:=JBmJCT
elif ex=cb*cc+cc*ca+ca*cb then ex:=cbmccT
elif ex=NB*NC+NC*NA+NA*NB then ex:=NBmNCT
elif ex=nb*nc+nc*na+na*nb then ex:=nbmncT

elif ex=ha*IA+hb*IB+hc*IC then ex:=hamIAT
elif ex=ha*ma+hb*mb+hc*mc then ex:=hammaT
elif ex=HA*ma+HB*mb+HC*mc then ex:=HAmmaT
elif ex=HA*IA+HB*IB+HC*IC then ex:=HAmIAT

elif ex=1/wb/wc+1/wc/wa+1/wa/wb then ex:=dwbdwcT
elif ex=1/mb/mc+1/mc/ma+1/ma/mb then ex:=dmbdmcT
elif ex=1/ma/wa+1/mb/wb+1/mc/wc then ex:=dmadwaT
elif ex=1/ra/wa+1/rb/wb+1/rc/wc then ex:=dradwaT
elif ex=1/wa^2+1/wb^2+1/wc^2 then ex:=dwap2T

elif ex=ra*ma*wa+rb*mb*wb+rc*mc*wc then ex:=rammamwaT

elif ex=a/wa+b/wb+c/wc then ex:=adwaT
elif ex=a/ma+b/mb+c/mc then ex:=admaT
elif ex=ma/a+mb/b+mc/c then ex:=madaT
elif ex=wa/a+wb/b+wc/c then ex:=wadaT
elif ex=ma/wa+mb/wb+mc/wc then ex:=madwaT
elif ex=wa/ma+wb/mb+wc/mc then ex:=wadmaT
elif ex=ra*wa+rb*wb+rc*wc then ex:=ramwaT
elif ex=wa/ha+wb/hb+wc/hc then ex:=wadhaT
elif ex=ha/wa+hb/wb+hc/wc then ex:=hadwaT
elif ex=ha*wa+hb*wb+hc*wc then ex:=hamwaT
elif ex=ha/ma+hb/mb+hc/mc then ex:=hadmaT
elif ex=ma/ha+mb/hb+mc/hc then ex:=madhaT
elif ex=wa/IA+wb/IB+wc/IC then ex:=wadIAT
elif ex=IA/a+IB/b+IC/c then ex:=IAdaT
elif ex=a/IA+b/IB+c/IC then ex:=adIAT
elif ex=ma/ra+mb/rb+mc/rc then ex:=madraT
elif ex=ra/ma+rb/mb+rc/mc then ex:=radmaT
elif ex=wa/ra+wb/rb+wc/rc then ex:=wadraT
elif ex=IA/ra+IB/rb+IC/rc then ex:=IAdraT
elif ex=ra/IA+rb/IB+rc/IC then ex:=radIAT
elif ex=IA/ha+IB/hb+IC/hc then ex:=IAdhaT
elif ex=ha/IA+hb/IB+hc/IC then ex:=hadIAT
elif ex=IA/ma+IB/mb+IC/mc then ex:=IAdmaT
elif ex=ma/IA+mb/IB+mc/IC then ex:=madIAT
elif ex=HA/IA+HB/IB+HC/IC then ex:=HAdIAT
elif ex=ra/wa+rb/wb+rc/wc then ex:=radwaT
elif ex=rb*rc/wb/wc+rc*ra/wc/wa+ra*rb/wa/wb then ex:=rbmrcdwbdwcT
elif ex=b*c/mb/mc+c*a/mc/ma+a*b/ma/mb then ex:=bmcdmbdmcT
elif ex=mb*mc/b/c+mc*ma/c/a+ma*mb/a/b then ex:=mbmmcdbdcT
elif ex=b*c/wb/wc+c*a/wc/wa+a*b/wa/wb then ex:=bmcdwbdwcT
elif ex=wb*wc/b/c+wc*wa/c/a+wa*wb/a/b then ex:=wbmwcdbdcT
elif ex=b*c/IB/IC+c*a/IC/IA+a*b/IA/IB then ex:=bmcdIBdICT
elif ex=IB*IC/b/c+IC*IA/c/a+IA*IB/a/b then ex:=IBmICdbdcT
elif ex=rb*rc/mb/mc+rc*ra/mc/ma+ra*rb/ma/mb then ex:=rbmrcdmbdmcT
elif ex=mb*mc/rb/rc+mc*ma/rc/ra+ma*mb/ra/rb then ex:=mbmmcdrbdrcT
elif ex=HB*HC/IB/IC+HC*HA/IC/IA+HA*HB/IA/IB then ex:=HBmHCdIBdICT
elif ex=Hb*Hc/IB/IC+Hc*Ha/IC/IA+Ha*Hb/IA/IB then ex:=HbmHcdIBdICT
elif ex=hb*hc/mb/mc+hc*ha/mc/ma+ha*hb/ma/mb then ex:=hbmhcdhbdhcT
elif ex=mb*mc/hb/hc+mc*ma/hc/ha+ma*mb/ha/hb then ex:=mbmmcdhbdhcT
elif ex=hb*hc/IB/IC+hc*ha/IC/IA+ha*hb/IA/IB then ex:=hbmhcdIBdICT
elif ex=mb*mc/wb/wc+mc*ma/wc/wa+ma*mb/wa/wb then ex:=mbmmcdwbdwcT
elif ex=wb*wc/mb/mc+wc*wa/mc/ma+wa*wb/ma/mb then ex:=wbmwcdmbdmcT
elif ex=HB*HC/mb/mc+HC*HA/mc/ma+HA*HB/ma/mb then ex:=HBmHCdmbdmcT
elif ex=mb*mc/IB/IC+mc*ma/IC/IA+ma*mb/IA/IB then ex:=mbmmcdIBdICT
elif ex=IB*IC/mb/mc+IC*IA/mc/ma+IA*IB/ma/mb then ex:=IBmICdmbdmcT
elif ex=Hb*Hc/mb/mc+Hc*Ha/mc/ma+Ha*Hb/ma/mb then ex:=HbmHcdmbdmcT
elif ex=HB*HC/wb/wc+HC*HA/wc/wa+HA*HB/wa/wb then ex:=HBmHCdwbdwcT
elif ex=wb*wc/IB/IC+wc*wa/IC/IA+wa*wb/IA/IB then ex:=wbmwcdIBdICT
elif ex=IB*IC/wb/wc+IC*IA/wc/wa+IA*IB/wa/wb then ex:=IBmICdwbdwcT
elif ex=rb*rc/IB/IC+rc*ra/IC/IA+ra*rb/IA/IB then ex:=rbmrcdIBdICT
elif ex=IB*IC/rb/rc+IC*IA/rc/ra+IA*IB/ra/rb then ex:=IBmICdrbdrcT
elif ex=Hb*Hc/wb/wc+Hc*Ha/wc/wa+Ha*Hb/wa/wb then ex:=HbmHcdwbdwcT
elif ex=hb*hc/mb/mc+hc*ha/mc/ma+ha*hb/ma/mb then ex:=hbmhcdmbdmcT
elif ex=Ha^2/wa^2+Hb^2/wb^2+Hc^2/wc^2 then ex:=Hap2dwap2T
elif ex=HA^2/wa^2+HB^2/wb^2+HC^2/wc^2 then ex:=HAp2dwap2T
elif ex=ha^2/wa^2+hb^2/wb^2+hc^2/wc^2 then ex:=hap2dwap2T
elif ex=hb*hc/wb/wc+hc*ha/wc/wa+ha*hb/wa/wb then ex:=hbmhcdwbdwcT
elif ex=wa^2/IA^2+wb^2/IB^2+wc^2/IC^2 then ex:=wap2dIAp2T
elif ex=ra^2/wa^2+rb^2/wb^2+rc^2/wc^2 then ex:=rap2dwap2T
elif ex=IA^2/wa^2+IB^2/wb^2+IC^2/wc^2 then ex:=IAp2dwap2T
elif ex=IB*IC/hb/hc+IC*IA/hc/ha+IA*IB/ha/hb then ex:=IBmICdhbdhcT
elif ex=wb*wc/hb/hc+wc*wa/hc/ha+wa*wb/ha/hb then ex:=wbmwcdhbdhcT
elif ex=wa^2/ha^2+wb^2/hb^2+wc^2/hc^2 then ex:=wap2dhap2T
elif ex=ma^2/wa^2+mb^2/wb^2+mc^2/wc^2 then ex:=map2dwap2T

elif ex=HA/ma+HB/mb+HC/mc then ex:=HAdmaT
elif ex=wb*wc/rb/rc+wc*wa/rc/ra+wa*wb/ra/rb then ex:=wbmwcdrbdrcT

###uns
elif ex=(ma-wa)^2+(mb-wb)^2+(mc-wc)^2 then ex:=mamwap2T

elif ex=cos(A/2)+cos(B/2)+cos(C/2) then ex:=cosAd2T
elif ex=cos(A/2)^3+cos(B/2)^3+cos(C/2)^3 then ex:=cosAd2p3T
elif ex=cos(A/2)^5+cos(B/2)^5+cos(C/2)^5 then ex:=cosAd2p5T
elif ex=sin(A/2)+sin(B/2)+sin(C/2) then ex:=sinAd2T
elif ex=sin(A/2)^3+sin(B/2)^3+sin(C/2)^3 then ex:=sinAd2p3T
elif ex=sin(A/2)^5+sin(B/2)^5+sin(C/2)^5 then ex:=sinAd2p5T
elif ex=sin(A/2)^7+sin(B/2)^7+sin(C/2)^7 then ex:=sinAd2p7T
elif ex=cos(B/2)*cos(C/2)+cos(C/2)*cos(A/2)+cos(A/2)*cos(B/2) then 
   ex:=cosBd2mcosCd2T
elif ex=sin(B/2)*sin(C/2)+sin(C/2)*sin(A/2)+sin(A/2)*sin(B/2) then 
   ex:=sinBd2msinCd2T
elif ex=sec(B/2)*sec(C/2)+sec(C/2)*sec(A/2)+sec(A/2)*sec(B/2) then 
   ex:=secBd2msecCd2T
elif ex=cos((B-C)/2)+cos((C-A)/2)+cos((A-B)/2) then 
   ex:=cosBsCd2T
else

xl:={x=y,y=z,z=x,a=b,b=c,c=a,s=s,ra=rb,rb=rc,rc=ra,ha=hb,hb=hc,hc=ha,
ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,IC=IA,
Ha=Hb,Hb=Hc,Hc=Ha,sin(A)=sin(B),sin(B)=sin(C),sin(C)=sin(A),cos(A)=cos(B),
cos(B)=cos(C),cos(C)=cos(A),sin(A/2)=sin(B/2),sin(B/2)=sin(C/2),sin(C/2)=sin(A/2),
cos(A/2)=cos(B/2),cos(B/2)=cos(C/2),cos(C/2)=cos(A/2),r=r,R=R,S=S,Ra=Rb,Rb=Rc,
Rc=Ra,GA=GB,GB=GC,GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja
}:

   if indets(ex)={} then ex:=poly2(rpol(ex));fi;
   if indets(ex) minus {p,q,s,T,_xk}<>{} then
      ex:=maxmidmin(ex);
      if op(0,ex)=max or op(0,ex)=min or op(0,ex)=mid then
         ex:=product('(op(k,ex)-T)','k'=1..nops(ex));
         if nargs=1 then ex:=poly2(rpol(ex));
         else ex:=poly2(rpol(ex),x);
         fi;
      else
         if whattype(ex)=`+` then
            ex:=expand(ex);
            if nops(ex)=3 then
               nn:=nops(ex);
               co:=[];
               tt:=-1;
               for j to nn while tt=-1 do
                  t:=op(j,ex);
                  if whattype(t)=`*` then
                     yl:=[op(t)];
                     n:=nops(yl);
                     m:=1;
                     for i to n do
                        if type(yl[i],numeric) or (whattype(yl[i])=`^` and type(op(1,yl[i]),numeric)) then
                           m:=m*yl[i];
                        fi;
                     od;
                     co:=[op(co),m];
                  else co:=[op(co),-1];tt:=1;
                  fi;
               od;
               if tt=-1 and changenum(co)=0 and min(co[1],0)=0 and co[1]<>1 then
                  m:=co[1];
                  ex:=sum((op(k,ex)/m),'k'=1..nn);
                  n:=psTpoly(m);
                  n:=subs(T=T2,n);
                  m:=psTpoly(ex);
                  m:=subs(T=T1,m);
                  ex:=resultant(T-T1*T2,m,T1);
                  ex:=resultant(ex,n,T2);
                  if nargs=1 then ex:=poly2(ex);fi;
               else
                  if nargs=1 then ex:=poly2(rpol(ex));
                  else ex:=poly2(rpol(ex),x);
                  fi;
               fi;
            else
               yl:=fsplit([op(ex)],[]);
               n:=nops(yl);
               temp:=1:
               for i to n while temp=1 do
                  if cyclicornot(sum('yl[i][k]','k'=1..nops(yl[i])))<>1 then temp:=0;fi;
               od;
               if temp=1 then
                  t:=T-sum('T||k','k'=1..n);
                  for i to n do
                     t:=resultant(t,subs(T=T||i,psTpoly(sum('yl[i][k]','k'=1..nops(yl[i])))),T||i);
                  od:
                  ex:=t;
                  if nargs=1 then ex:=poly2(rpol(ex));fi;
               else
                  if nargs=1 then ex:=poly2(rpol(ex));else ex:=poly2(rpol(ex),x);fi;
               fi;
            fi;

         elif whattype(ex)=`*` then
            yl:=fsplit([op(ex)],[]);
            n:=nops(yl);
            temp:=1;
            for i to n while temp=1 do
               if cyclicornot(product('yl[i][k]','k'=1..nops(yl[i])))<>1 then temp:=0;fi;
            od;
   
            if temp=1 then
               t:=T-product('T||k','k'=1..n);
               for i to n do
                  if nops(yl[i])=1 then
                     t:=resultant(t,subs(T=T||i,psTpoly(yl[i][1])),T||i);
                  else
                     if nargs=1 then
                        t:=resultant(t,subs(T=T||i,poly2(rpol(product('yl[i][k]','k'=1..nops(yl[i]))))),T||i);
                     else
                        t:=resultant(t,subs(T=T||i,poly2(rpol(product('yl[i][k]','k'=1..nops(yl[i]))),x)),T||i);
                     fi;
                  fi;
               od:
               ex:=t;
               if nargs=1 then ex:=poly2(rpol(ex));fi;
               else
                  if nargs=1 then ex:=poly2(rpol(ex));else ex:=poly2(rpol(ex),x);fi;
               fi;
   
         elif whattype(ex)=`^` then
            m:=op(1,ex);
            n:=op(2,ex);
            if n>0 then
               t:=subs(T=X,psTpoly(m));
               ex:=resultant(T^denom(n)-X^numer(n),t,X);
               if nargs=1 then ex:=poly2(ex); fi;
            else
               if nargs=1 then ex:=poly2(rpol(ex)):
               else ex:=poly2(rpol(ex),x);
               fi;
            fi;
         else
            if nargs=1 then ex:=poly2(rpol(ex));
            else ex:=poly2(rpol(ex),x);
            fi;
         fi;
      fi;
   elif not has(ex,T) then ex:=poly2(rpol(ex));
   fi;
fi;
ex;
end:

rpol:=proc(expr)
   local re,ex,fa,np,pr,i,its,s:
        
   ex:=expr:
   its:=indets(ex):
   while has(ex,abs)=true do
      for i to nops(its) do
         if op(0,its[i])=abs then 
            ex:=subs(its[i]=sqrt(op(1,its[i])^2),ex)
         fi
      od:
      its:=indets(ex):
   od:

   if member(T,indets(ex))=true then ex:=numer(ex);
   else ex:=numer(ex-T):
   fi:
   ex:=subs(a=y+z,b=z+x,c=x+y,ex):

   if has(ex,{A,B,C}) then
      ex:=expand(ex);
      ex:=subs({sec(A)=1/cos(A),sec(B)=1/cos(B),sec(C)=1/cos(C),sec(A/2)=1/cos(A/2),
               sec(B/2)=1/cos(B/2),sec(C/2)=1/cos(C/2),csc(A)=1/sin(A),csc(B)=1/sin(B),
               csc(C)=1/sin(C),csc(A/2)=1/sin(A/2),csc(B/2)=1/sin(B/2),csc(C/2)=1/sin(C/2)},ex);
print(ex):
      ex:=subs({tan(A/2)=1/x,tan(B/2)=1/y,tan(C/2)=1/z,cot(A/2)=x,cot(B/2)=y,cot(C/2)=z,
            sin(A/2)=sqrt(y*z/(x+y)/(x+z)),sin(B/2)=sqrt(x*z/(x+y)/(y+z)),sin(C/2)=sqrt(y*x/(z+y)/(x+z)),
            cos(A/2)=sqrt(x*(x+y+z)/(x+y)/(x+z)),cos(B/2)=sqrt(y*(x+y+z)/(x+y)/(y+z)),cos(C/2)=sqrt(z*(x+y+z)/(z+y)/(x+z)),
            tan(A)=2*x/(x^2-1),tan(B)=2*y/(y^2-1),tan(C)=2*z/(z^2-1),
            cot(A)=(x^2-1)/2/x,cot(B)=(y^2-1)/2/y,cot(C)=(z^2-1)/2/z,
            sin(A)=2*(y+z)/(y*z+z*x+x*y-1),sin(B)=2*(x+z)/(y*z+z*x+x*y-1),sin(C)=2*(x+y)/(y*z+z*x+x*y-1),
            cos(A)=1-2*y*z/(x+y)/(x+z),cos(B)=1-2*z*x/(y+z)/(y+x),cos(C)=1-2*x*y/(x+z)/(y+z)},ex);
print(ex):
      ex:=combine(ex,radical,symbolic):
      ex:=simplify(ex,radical,symbolic):
      ex:=numer(ex):

   fi:

   while hastype(ex,`radical`)=true do ex:=rads(ex) od:

   ex:=numer(ex):
   if type(ex,polynom) then
      readlib(factors):
      fa:=factors(ex)[2]:
      np:=nops(fa):
      pr:=1:
      for i to np do if has(fa[i],T)=true then pr:=pr*fa[i][1] fi;od;
      ex:=pr:
   fi;
   ex
end:

poly2:=proc(expr)
   local np,vs,ns,ex,nq,i,j,c0,pr,ps,po,pf,co,mv,dg,c,fa:
   global gg;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:

   if not (has(expr,s) and (has(expr,p) or has(expr,q))) then
      ex:=subs(s=x+y+z,expr);
   else ex:=expr;
   fi;

   if member(T,indets(ex))=true then ex:=numer(ex) else ex:=numer(ex-T) fi:
   vs:=[op(indets(ex) minus {x,y,z,p,q,s,T,_xk})]:
   ns:=nops(vs):
   for i to ns do ex:=resultant(ex,h(vs[i]),vs[i]); od:

   if whattype(ex)=`^` and denom(op(2,ex))=1 then 
      ex:=op(1,ex);
   elif whattype(ex)=`*` then
      readlib(factors): fa:=factors(ex)[2]: np:=nops(fa): pr:=1:
      for i to np do if has(fa[i],T)=true then pr:=pr*fa[i][1] fi; od:
      ex:=pr:
   fi;

   ex:=collect(ex,T):
   if indets(ex) minus {x,y,z,T,p,q,s,_xk}<>{} then 
      ERROR(`please input new data in data base`,ex);
   fi;
   if has(ex,{x,y,z})=true then 
      dg:=degree(ex,T):
      for i from 0 to dg do
         c||i:=coeff(ex,T,i):
         if has(c||i,{x,y,z})=true then c||i:=x_sort(c||i);fi;
      od:
      ex:=sum('c||i*T^i','i'=0..dg):
   fi:
   ex:=primpart(ex,T):
   if nargs=1 then
      if not has(ex,_xk) then
         pf:=pwrfr(ex,{T}):
         nq:=nops(pf):
         ps:=[]:
         for j to nq do
            ex:=op(j,pf):
            ex:=collect(ex,T):
            ex:=map(factor,ex):
            c0:=subs(T=0,ex):
            ex:=ex-c0+factor(c0):
            ex:=sort(ex,T):
            ps:=[op(ps),ex]:
         od:
         po:=ps[1]:
         if nq>1 then 
            for j to nq-1 do
               co:=ie2(po,ps[j+1],p,s,T,gg):
               if co=greater then 
                  po:=po
               elif co=less then 
                  po:=ps[j+1]
               else po:=po*ps[j+1]
               fi
            od
         fi:
      else po:=ex;
      fi;
   elif nargs=2 then po:=ex;
   fi;
   po:=numer(po);
   po;
end:

pwrfree:=proc(poly,vset)
   local pw,np,pr,i:
   
   pw:=pwrfr(poly,vset):
   np:=nops(pw):
   pr:=product(pw[i],i=1..np):
   RETURN(pr):
end:

pwrfr:=proc(poly,vset)
   local fa,np,ps,i:
   
   readlib(factors):
   fa:=factors(poly)[2]:
   np:=nops(fa):
   ps:=[]:
   for i to np do
      if has(fa[i][1],vset)=true then ps:=[op(ps),fa[i][1]] fi
   od:
   ps:=map(numer,ps);
   RETURN(ps):
end:

pqTpoly:=proc(expr) map(factor,subs(s=sqrt(q+4*p+27),psTpoly(expr))) end:

#######################################################
##                                                   ##
## given two polynomials with parameters `p`,`s`/'q' ##
##      which one has a greater greatest root ?      ##
##                                                   ##
#######################################################
ie2:=proc(poly1,poly2,par1,par2,var,cond)
   local p1,p2,po1,po2,res,su,fa,rs,i,fb,bz,dt,fac,fc,j,fd,ret,k,F,nd,
         xfp,ff,cs,fs,nf,n,df,tp,tps,fq,rr,nr,rs1,rs2,t,N,r1,r2,xp,
         np,fg,ng,ns,eq1,eq2,ep1,ep2,lc,temp,co:
   global gg,hh,aa;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:

   po1:=poly1:
   po2:=poly2:

   p1:=subs(var=sqrt(var),po1):
   p2:=subs(var=sqrt(var),po2):
   p1:=collect(p1,T);
   p2:=collect(p2,T);

   while type(p1,polynom) and type(p2,polynom) do
      po1:=p1;po2:=p2;
      p1:=subs(var=sqrt(var),po1):
      p2:=subs(var=sqrt(var),po2):
      p1:=collect(p1,var);p2:=collect(p2,var);
   od;

   print(`Start to eliminate T    `);
   if degree(po1,var)=1 then res:=prem(po2,po1,var);
   elif degree(po2,var)=1 then res:=prem(po1,po2,var);
   else   res:=resultant(po1,po2,var);
   fi;

   if res=0 then
      gcd(po1,po2,'po1');
      if degree(po1,var)=1 then res:=prem(po2,po1,var);
      elif degree(po2,var)=1 then res:=prem(po1,po2,var);
      else   res:=resultant(po1,po2,var);
      fi;
   fi;

   su:=numer(normal(res)):
   readlib(factors):
   fa:=factors(su)[2]:
print(`finding the border curve(s)    `,time()):
   ff:=[cond];
   for i to nops(fa) do
      fb:=fa[i][1]:
      cs:=[coeffs(fb)]:
      ret:=1:
      for j from 2 to nops(cs) while ret=1 do
         if sign(cs[j])<>sign(cs[1]) then ret:=-1 fi
      od:
      if ret=-1 and (divide(cond,fb)=false or divide(fb,cond)=false) then
         ff:=[op(ff),fb]:
         print(`OK`):
      fi:
      print(`all right`):
   od:

   lc:=[lcoeff(po1,var),lcoeff(po2,var)]:
   for i to 2 do
      fb:=expand(lc[i]):
      cs:=[coeffs(fb)]: ret:=1:
      if nops(cs)>1 then
         for j from 2 to nops(cs) while ret=1 do
            if sign(cs[j])<>sign(cs[1]) then ret:=-1 fi
         od:
         if ret=-1 then
            ff:=[op(ff),fb]:
            print(`OK`):
         fi:
         print(`all right`):
      fi
   od:


print(`found the border curve(s) `):
   fs:=subsop(1=NULL,ff):
   nf:=nops(ff):
#print(nf-1):
print(`finding the intersection point(s)    `,time()):
   fg:=[]:
   for i to nf-1 do
      for j from i+1 to nf do
         dt:=resultant(ff[i],ff[j],par2):
         fac:=factors(dt):
print(i,j,`Good`):
         fc:=fac[2]:
         for k to nops(fc) do
            fd:=fc[k][1]:
            ret:=1:
            for n from 0 to degree(fd,par1)-1 while ret=1 do
               if sign(lcoeff(fd,par1))<>sign(coeff(fd,par1,n)) then ret:=-1 fi
            od:
            if ret=-1 then fg:=[op(fg),fd]: fi;
         od:
         print(`OK`):
      od:
      print(`all right`):
   od:
print(`finding the critical point(s)    `,time()):
   if nf>1 then
      for i from 2 to nf do
         df:=resultant(ff[i],diff(ff[i],par2),par2);
         fc:=pwrfr(df,{par1}):
         for k to nops(fc) do
            fd:=fc[k]:
            ret:=1:
            for n from 0 to degree(fd,par1)-1 while ret=1 do
               if sign(lcoeff(fd,par1))<>sign(coeff(fd,par1,n)) then ret:=-1 fi
            od:
            if ret=-1 then fg:=[op(fg),fd]: fi:
            print(`OK`):
         od:
         print(`all right`):
      od
   fi:

   rs:=[]:
   F:=product('fg[k]','k'=1..nops(fg));
   fg:=map(numer,[op({op(pwrfr(F,{par1}))} minus {par1})]);
   if fg=[] then tp:=[1];
   else tp:=samplepoint(fg,par1);
   fi:

print(`output one-dimension test point(s):`);
print(tp):

print(`setting the test point(s) and doing test `,time()):

   tps:=[]:
   np:=nops(tp):
   for i to np do
      fq:=subs(par1=tp[i],ff):
      F:=product('fq[k]','k'=1..nops(fq));
      fg:=pwrfr(F,{par2});
      fg:=map(numer,fg);
      fg:=[op({op(fg)} minus {par2})];
      rr:=samplepoint(fg,par2);
      nd:=nops(rr);
      for j to nd do
         if subs(par2=rr[j],fq[1])>=0 then tps:=[op(tps),[tp[i],rr[j]]];fi;
      od;
   od:

print(tps);
print(`The test result follows ---`):
print(`Either always 1 or always -1 means the inequality holds accordingly`):
   np:=nops(tps):
print(`the number of test point(s) is`, np):
if np=0 then RETURN(`less`);fi; #The inequality holds for ever.
   ret:=0;
   if nargs=8 then
#       print(`please go on waiting `.(np*50).` seconds or so..in pentium 586/75`);
   fi;
   readlib(realroot):
   temp:=0;co:=[];
   for i to np while temp=0 do
      if nargs=6 then
         eq1:=numer(subs(par1=tps[i][1],par2=tps[i][2],po1)):
         eq2:=numer(subs(par1=tps[i][1],par2=tps[i][2],po2)):

         rr:=realroot(eq1*eq2);

         nr:=nops(rr):
         rs1:=[];rs2:=[];
         for j to nr do
            rs1:=[op(rs1),rr[j][1]];rs2:=[op(rs2),rr[j][2]];
         od;
         rs1:=sort(rs1);rs2:=sort(rs2);
         r1:=rs1;r2:=rs2;

         if subs(var=r1[nr],eq1)*subs(var=r2[nr],eq1)<0 then
            ret:=ret+1; co:=[op(co),1];print(1);
            N:={par1=tps[i][1],par2=tps[i][2]};
         else
            if r1[nr]=r2[nr] and subs(var=r1[nr],eq1)=0 then
               ret:=ret+1; co:=[op(co),1]; print(1);
               N:={par1=tps[i][1],par2=tps[i][2]};
            else print(-1): ret:=ret-1;co:=[op(co),-1];
            fi;
         fi:
         temp:=changenum(co);
         if temp<>0 then
            if {args[4]} minus {s}={} then
               xfp:=subs(N,t^3-par2*t^2+(par1+9)*t-par2):
            elif {args[4]} minus {q}={} then
               xfp:=subs(N,t^3-(4*par1+par2+27)^(1/2)*t^2+(par1+9)*t-(4*par1+par2+27)^(1/2));
            fi;
            xp:=solvecubic(coeff(xfp,t,2),coeff(xfp,t,1),coeff(xfp,t,0));
            print(`output a counter-example`);
            lprint([xp[1]+xp[2],xp[2]+xp[3],xp[3]+xp[1]]);
            print(`whose approximate value is the following:`);
            lprint(`a=`,evalf(xp[1]+xp[2]),`b=`,evalf(xp[2]+xp[3]),`c=`,evalf(xp[3]+xp[1]));
         fi;

      elif nargs=8 then
         if {args[4]} minus {s}={} then
            xfp:=subs({par1=tps[i][1],par2=tps[i][2]},t^3-par2*t^2+(par1+9)*t-par2):
         elif {args[4]} minus {q}={} then
            xfp:=subs({par1=tps[i][1],par2=tps[i][2]},t^3-(4*par1+par2+27)^(1/2)*t^2+(par1+9)*t-(4*par1+par2+27)^(1/2));
         fi;
         xp:=solvecubic(coeff(xfp,t,2),coeff(xfp,t,1),coeff(xfp,t,0));
         ep1:=subs({x=xp[1],y=xp[2],z=xp[3]},args[7]);
         ep2:=subs({x=xp[1],y=xp[2],z=xp[3]},args[8]);

         if op(0,ep1)=mid then ep1:=x_mid(op(ep1));fi;
         if op(0,ep2)=mid then ep2:=x_mid(op(ep2));fi;
         if op(0,ep1)=min then ep1:=min(op(ep1));
         elif op(0,ep1)=max then ep1:=max(op(ep1));
         fi;
         if op(0,ep2)=min then ep2:=min(op(ep2));
         elif op(0,ep2)=max then ep2:=max(op(ep2));
         fi;

         if max(ep1-ep2,0)=0 then ret:=ret-1;print(-1);co:=[op(co),-1];
         else
            ret:=ret+1;co:=[op(co),1];print(1);
            N:={par1=tps[i][1],par2=tps[i][2]};
         fi;
         temp:=changenum(co);
         if temp<>0 then
            if {args[4]} minus {s}={} then
               xfp:=subs(N,t^3-par2*t^2+(par1+9)*t-par2):
            elif {args[4]} minus {q}={} then
               xfp:=subs(N,t^3-(4*par1+par2+27)^(1/2)*t^2+(par1+9)*t-(4*par1+par2+27)^(1/2));
            fi;
            xp:=solvecubic(coeff(xfp,t,2),coeff(xfp,t,1),coeff(xfp,t,0));
            print(`output a counter-example`);
            lprint([xp[1]+xp[2],xp[2]+xp[3],xp[3]+xp[1]]);
            print(`whose approximate value is the following:`);
            lprint(`a=`,evalf(xp[1]+xp[2]),`b=`,evalf(xp[2]+xp[3]),`c=`,evalf(xp[3]+xp[1]));
         fi;

      fi;
   od:


   if ret=np then ret:=`greater`
   elif ret=-np then ret:=`less`
   else ret:=`The inequality doesn't hold.`
   fi:
   print(ret):

   RETURN(ret)
end:

#########################################################
##                                                     ##
##   data base for translating geometric expressions   ##
##             into standard parameters                ##
##                                                     ##
#########################################################
aa:=2*s-p-10:
h(_xk):=_xk-T:

h(r) := r-1:
h(S) := S-x-y-z:
h(R) := 4*R-y*z-z*x-x*y+1:
h(Q) := Q-2*(x^2+y^2+z^2-x*y-y*z-z*x):                ## Q: = (b-c)^2+(c-a)^2+(a-b)^2:
h(K) := K-(x^2+y^2+z^2+3*x*y+3*y*z+3*z*x):            ## K: = b*c + c*a + a*b:
h(H) := H-(x^2+y^2+z^2+x*y+y*z+z*x):                  ## H: = (1/2)*(a^2+b^2+c^2):

h(a):= a-y-z:
h(b):= b-z-x:
h(c):= c-x-y:
h(s):=s-x-y-z:

h(ra):=ra-y*z:
h(rb):=rb-z*x:
h(rc):=rc-x*y:

h(ha) := (y+z)*ha-2*(x+y+z):
h(hb) := (z+x)*hb-2*(x+y+z):
h(hc) := (x+y)*hc-2*(x+y+z):

h(ma) := 4*ma^2-(y-z)^2-4*x*(x+y+z):
h(mb) := 4*mb^2-(z-x)^2-4*y*(x+y+z):
h(mc) := 4*mc^2-(x-y)^2-4*z*(x+y+z):

h(wa) := (2*x+z+y)^2*wa^2-4*x*(x+y)*(x+z)*(x+y+z):
h(wb) := (2*y+x+z)^2*wb^2-4*y*(x+y)*(y+z)*(x+y+z):
h(wc) := (2*z+y+x)^2*wc^2-4*z*(x+z)*(y+z)*(x+y+z):

h(Oa):=3*(y+z)*Oa-2*(x+y+z):
h(Ob):=3*(z+x)*Ob-2*(x+y+z):
h(Oc):=3*(x+y)*Oc-2*(x+y+z):

h(HA):=2*x*HA-(y+z)*(x^2-1):
h(HB):=2*y*HB-(z+x)*(y^2-1):
h(HC):=2*z*HC-(x+y)*(z^2-1):
h(Ha):=2*(y+z)*Ha+x*(y^2+z^2-2)-(y+z)*(y*z+1):
h(Hb):=2*(z+x)*Hb+y*(z^2+x^2-2)-(z+x)*(z*x+1):
h(Hc):=2*(x+y)*Hc+z*(x^2+y^2-2)-(x+y)*(x*y+1):

h(GA):=9*GA^2-(y-z)^2-4*x*(x+y+z):
h(GB):=9*GB^2-(z-x)^2-4*y*(x+y+z):
h(GC):=9*GC^2-(x-y)^2-4*z*(x+y+z):

h(IA):=IA^2-x^2-1:
h(IB):=IB^2-y^2-1:
h(IC):=IC^2-z^2-1:

h(JA):= 14*y^2+28*y*z+14*z^2+4*y^3*z+12*y^2*x^2+8*y^3*x+8*z^3*x+4*z^3*y+12*z^2*x
^2+4*y^2*z^2+32*x*y+32*x*z+18*x^2+x^2*z^4+2*x^3*z^3+y^4*z^2-2*y^3*z^3+y^2*z^4+
x^4*y^2+2*x^3*y^3+x^4*z^2+x^2*y^4+2*z^4+2*y^4+2*x^4+8*x^3*y+8*x^3*z-4*(x*y+x*z
+y*z)^2*JA^2:
h(JB):= 18*y^2+32*y*z+14*z^2+8*y^3*z+12*y^2*x^2+8*y^3*x+4*z^3*x+8*z^3*y+4*z^2*x^
2+12*y^2*z^2+32*x*y+28*x*z+14*x^2+x^2*z^4-2*x^3*z^3+y^4*z^2+2*y^3*z^3+y^2*z^4+
x^4*y^2+2*x^3*y^3+x^4*z^2+x^2*y^4+2*z^4+2*y^4+2*x^4+8*x^3*y+4*x^3*z-4*(x*y+x*z
+y*z)^2*JB^2:
h(JC):= 14*y^2+32*y*z+18*z^2+8*y^3*z+4*y^2*x^2+4*y^3*x+8*z^3*x+8*z^3*y+12*z^2*x^
2+12*y^2*z^2+28*x*y+32*x*z+14*x^2+x^2*z^4+2*x^3*z^3+y^4*z^2+2*y^3*z^3+y^2*z^4+
x^4*y^2-2*x^3*y^3+x^4*z^2+x^2*y^4+2*z^4+2*y^4+2*x^4+4*x^3*y+8*x^3*z-4*(x*y+x*z
+y*z)^2*JC^2:

h(ca):=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*y^2*z^2*(x+y+z))-(2*y*z+z*x+x*y)^2*ca^2:
h(cb):=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*x^2*z^2*(x+y+z))-(y*z+2*z*x+x*y)^2*cb^2:
h(cc):=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*y^2*x^2*(x+y+z))-(y*z+z*x+2*x*y)^2*cc^2:

h(Ja):=Ja*(y*z+z*x+x*y)-x*(x+y+z):
h(Jb):=Jb*(y*z+z*x+x*y)-y*(x+y+z):
h(Jc):=Jc*(y*z+z*x+x*y)-z*(x+y+z):

h(ga):=(y+z)*ga^2-x^2*(y+z)+4*(x+y+z):
h(gb):=(z+x)*gb^2-y^2*(z+x)+4*(x+y+z):
h(gc):=(x+y)*gc^2-z^2*(x+y)+4*(x+y+z):
h(MA):=(y*z+z*x+x*y)^2*MA^2-x^2*(y+z)*(x^2*(y+z)+4*(x+y+z)):
h(MB):=subs({x=y,y=z,z=x,MA=MB},h(MA)):
h(MC):=subs({x=y,y=z,z=x,MB=MC},h(MB)):
h(Ma):=2*x*(y+z)*(y*z+z*x+x*y)*Ma-(x+y+z)^2:
h(Mb):=subs({x=y,y=z,z=x,Ma=Mb},h(Ma)):
h(Mc):=subs({x=y,y=z,z=x,Mb=Mc},h(Mb)):

h(na):=(y+z)*na^2-x^2*(y+z)-2*x*(y^2+z^2)-(y+z)*(y-z)^2:
h(nb):=subs({x=y,y=z,z=x,na=nb},h(na)):
h(nc):=subs({x=y,y=z,z=x,nb=nc},h(nb)):
h(NA):=(x+y+z)^2*NA^2-(y+z)*(x^2*(y+z)+2*x*(y^2+z^2)+(y+z)*(y-z)^2):
h(NB):=subs({x=y,y=z,z=x,NA=NB},h(NA)):
h(NC):=subs({x=y,y=z,z=x,NB=NC},h(NB)):
h(Na):=2*(y+z)*Na-x:
h(Nb):=2*(z+x)*Nb-y:
h(Nc):=2*(x+y)*Nc-z:

h(ka):=x^2*(2*x*(x+y+z)+y^2+z^2)^2*ka^2-(x+y+z)^2*(x^2+1)^2*(4*x*(x+y+z)+(y-z)^2):
h(kb):=subs({x=y,y=z,z=x,ka=kb},h(ka)):
h(kc):=subs({x=y,y=z,z=x,kb=kc},h(kb)):
h(KA):=4*x^2*((x+y+z)^2-2*(y*z+z*x+x*y))^2*KA^2-(x+y+z)^2*(x^2+1)^2*(4*x*(x+y+z)+(y-z)^2):
h(KB):=subs({x=y,y=z,z=x,KA=KB},h(KA)):
h(KC):=subs({x=y,y=z,z=x,KB=KC},h(KB)):
h(Ka):=4*((x+y+z)^2-2*(y*z+z*x+x*y))*Ka-(y+z)*(x+y+z):
h(Kb):=subs({x=y,y=z,z=x,Ka=Kb},h(Ka)):
h(Kc):=subs({x=y,y=z,z=x,Kb=Kc},h(Kb)):

h(ca):=x^2*(2*y*z+z*x+x*y)^2*ca^2-(x^2+1)*(x^2*(y+z)^2+(y-z)^2)*(x+y+z)^2:
h(cb):=subs({x=y,y=z,z=x,ca=cb},h(ca)):
h(cc):=subs({x=y,y=z,z=x,cb=cc},h(cb)):
h(JA):=4*x^2*(y*z+z*x+x*y)^2*JA^2-(x^2+1)*(x^2*(y+z)^2+(y-z)^2)*(x+y+z)^2:
h(JB):=subs({x=y,y=z,z=x,JA=JB},h(JA)):
h(JC):=subs({x=y,y=z,z=x,JB=JC},h(JB)):
h(Ja):=4*(y*z+z*x+x*y)*Ja-x*(x+y+z):
h(Jb):=4*(y*z+z*x+x*y)*Jb-y*(x+y+z):
h(Jc):=4*(y*z+z*x+x*y)*Jc-z*(x+y+z):

h(kk):=(kk^2-2*(y+z)^2-2*(z+x)^2-2*(x+y)^2)^2-192*(x+y+z)^2:
h(fa):=(x+y+z)^2*(kk-4*fa)^2-3*fa^2*(y+z)^4:
h(fb):=subs({x=y,y=z,z=x,fa=fb},h(fa)):
h(fc):=subs({x=y,y=z,z=x,fb=fc},h(fb)):
h(FA):=3*(kk*FA-(z+x)^2-(x+y)^2+(y+z)^2)^2-16*(x+y+z)^2:
h(FB):=subs({x=y,y=z,z=x,FA=FB},h(FA)):
h(FC):=subs({x=y,y=z,z=x,FB=FC},h(FB)):
h(Fa):=3*(y+z)^2*(kk^2*Fa-4*(x+y+z)*(y+z))^2-(4*(z+x)^2*(x+y)^2+(x+y)^2*(y+z)^2+(y+z)^2*(z+x)^2+(y+z)^4-2*(z+x)^4-2*(x+y)^4)^2:
h(Fb):=subs({x=y,y=z,z=x,Fa=Fb},h(Fa)):
h(Fc):=subs({x=y,y=z,z=x,Fb=Fc},h(Fb)):



h(pa):=(v5+w5)^2*pa^2-(v5+w5)*(w5*(z+x)^2+v5*(x+y)^2)+v5*w5*(y+z)^2:
h(pb):=subs({x=y,y=z,z=x,u5=v5,v5=w5,w5=u5,fa=fb},h(pa)):
h(pc):=subs({x=y,y=z,z=x,u5=v5,v5=w5,w5=u5,fb=fc},h(pb)):
h(PA):=(u5+v5+w5)^2*PA^2-(v5+w5)*(w5*(z+x)^2+v5*(x+y)^2)+v5*w5*(y+z)^2:
h(PB):=subs({x=y,y=z,z=x,u5=v5,v5=w5,w5=u5,PA=PB},h(PA)):
h(PC):=subs({x=y,y=z,z=x,u5=v5,v5=w5,w5=u5,PB=PC},h(PB)):
h(Pa):=2*(y+z)*(u5+v5+w5)*Pa-u5*(x+y+z):
h(Pb):=2*(z+x)*(u5+v5+w5)*Pb-v5*(x+y+z):
h(Pc):=2*(x+y)*(u5+v5+w5)*Pc-w5*(x+y+z):
h(u5):=(y+z)^2*((z+x)^2+(x+y)^2)+((z+x)^2-(x+y)^2)^2-u5:
h(v5):=(z+x)^2*((x+y)^2+(y+z)^2)+((x+y)^2-(y+z)^2)^2-v5:
h(w5):=(x+y)^2*((y+z)^2+(z+x)^2)+((y+z)^2-(z+x)^2)^2-w5:

h(Ra) := x^2*Ra-(x+z)*(x+y):
h(Rb) := y^2*Rb-(x+y)*(y+z):
h(Rc) := z^2*Rc-(y+z)*(x+z):


##poly((ma-wa)^2+(mb-wb)^2+(mc-wc)^2)
mamwap2T := -31828335089156096*s^38-14622515716423680*s^38*p+
14951341207068103122562842624*p-37539823616*s^40*p^4+4968677376*s^46-\
15736859262976*s^42+1183012640506846722048*s^16*p^9+72300509364641255936*s^16*
p^10+3369643845888057856*s^16*p^11+1363307397120*s^44+1631957592205344768*s^32
*p^4-808418039206939124552957952*s^2+285175651358073389318144*s^26+
3108463823467838439424*s^30+34786225506285915734016*s^28+
2165863339150810029752320*s^22*p^3+6314203981279214934425600*s^22*p^2+
493810151293095056834560*s^20*p^5+145003954650682203045888*s^26*p^2+
502655698057030251446272*s^22*p^4+346921643310716550381568*s^24*p^3+
1103428329573264758407168*s^24*p^2+34100211922597322948608*s^28*p+
2111666444426483110772736*s^24*p+302725443924151964270592*s^26*p+
22278961624649544*p^17+10811192201463666688*s^14*p^11+
544409315025488300840583168*s^4+2390791585*s^16*p^16+10235024352*s^18*p^15-\
2256890937104670822236160000*s^2*p-2912824182999835982217609216*s^2*p^2+
12687876318966213971471892480*p^3+17250107967038644902403375104*p^2+
35892611874816*s^36*p^5+1615246958592*s^34*p^7+199893639293421158400*s^32+
10726563154050724864*s^18*p^10+2060698571800906961336795136*s^4*p^2+
1681337565599128317933649920*s^4*p^3-3069102747616515059991183360*s^6*p-\
2819563410366420278079651840*s^6*p^2-1310931814890860229912625152*s^2*p^4-\
2334055343605195223832330240*s^2*p^3+1561246123451621672569798656*s^4*p+
2299268673113538949341511680*s^8*p+2578501454275621352012120064*s^8*p^2-\
1630428770785931004517023744*s^6*p^3+120285763516285649260904448*s^10*p-\
1580230408552889752144576512*s^6+6679355186538447898507591680*p^4+
940107815620690828765298688*s^8+435360153489712695191273472*s^12-\
6400456373410398799921152*s^10+2678432061477280568420892672*p^5+
46641518944124249282913792*p^8+219062608339417743945277440*p^7+
850116744550633207435812864*p^6+957349101830475914533306368*s^4*p^4-\
551231106704234449260281856*s^2*p^5-180742683599800350641602560*s^2*p^6+
161578562794731111363510272*s^12*p^4-666488377401293109078982656*s^6*p^4+
215486203766583416156061696*s^10*p^2+133841444776577416656805888*s^4*p^6+
1778756112724650460307390464*s^8*p^3+851206797121792005837471744*s^8*p^4-\
205213766056674260391395328*s^6*p^5+406294077786617488438296576*s^4*p^5-\
47478206182798378274217984*s^2*p^7+455378323077321096215658496*s^14*p+
835870644551131613220569088*s^12*p+174351259296125606056034304*s^10*p^3+
749849213409797302507143168*s^12*p^2+301440082944010397867442176*s^8*p^5+
35152615420996846999502848*s^4*p^7+417491037291735407116943360*s^12*p^3+
351730577536536905559048192*s^14*p^2+317025997888045743360442368*s^16*p-\
49568910001927736496750592*s^6*p^6+86507146931885601126088704*s^10*p^4+
29521788390422219305385984*s^10*p^5+168659222418141731894591488*s^14*p^3+
224934479231687652669128704*s^16*p^2+137748795266698046802493440*s^18*p-\
10179074787313792521904128*s^2*p^8+1314615059410616868743168*s^4*p^9-\
1561229946628769314578432*s^6*p^8+56125053514409979210366976*s^14*p^4+
90115256714801047078961152*s^18*p^2+7328937880932321166426112*s^10*p^6+
46226129410260920560517120*s^20*p+98802232829610188490407936*s^16*p^3+
46126452803306574661419008*s^12*p^5+17681098645960828047425536*s^8*p^7+
3054067628371089639917568*s^8*p^8+30047144406735432245018624*s^16*p^4+
28216040869219866012549120*s^20*p^2+10055533510679081363406848*s^12*p^6-\
9673067081800719224209408*s^6*p^7+82165263304638262898032640*s^8*p^6+
7496904859016900899631104*s^4*p^8-1804327863490455130302464*s^2*p^9+
36259394008461873194991616*s^18*p^3+13721046860453772520456192*s^14*p^5+
1360668720286709474099200*s^10*p^7-212622115862983830120448*s^6*p^9+
191116826915578369022464*s^4*p^10-266771892955787980207104*s^2*p^10-\
33083221729135568624128*s^2*p^11+276003932022540152573788160*s^14+
208523295107384391175700480*s^16+97687565565626303462244352*s^18+
34957618984015564926091264*s^20+8306863505003472096946176*p^9+
159114177432764617526784*p^11+1248154411605287320401408*p^10+
17264504117011982400448*p^12+9063293713910712805359616*s^22+
1839922129989469361405952*s^24+217675091877888*s^30*p^8+
11171024726275726327676928*s^22*p+125605900653330122272*p^14+
1596122631603722990976*p^13+8387202107698027488*p^15+472576382530416609*p^16+
2053133935158861957632*s^12*p^10+3457212782593908586496*s^14*p^9-\
24847871773143818110976*s^6*p^10-2521755439836408445952*s^6*p^11+
6701375194821035120590848*s^16*p^5+229232158444876328226816*s^12*p^8+
2340272521784893919616*s^4*p^12+23147554534045538804736*s^4*p^11-\
3451159578540784804096*s^2*p^12+19775003577920074381312*p^9*s^10+
2016864960846190615789568*s^18*p^5+40328170714754456182784*s^14*p^8+
147623667415196043034624*s^16*p^7+1132343768581386475814912*s^16*p^6+
4572640058896681400832*p^11*s^8+10532318644718235276541952*s^20*p^3+
190377040489478358294528*s^10*p^8+304406069761004797657088*s^18*p^6+
2684374524228247792582656*s^20*p^4+427926262536939914364928*p^9*s^8+
24376277306654943332352*p^9*s^12+1709248398844007793098752*s^12*p^7+
10027439808940473511182336*s^18*p^4+48924276624544434730496*p^10*s^8+
2543595445474640122085376*s^14*p^6+363614344908983528783872*s^14*p^7+
1434188889467268035584*p^10*s^10-302957686877602224512*s^2*p^13+
197345735319742039680*s^4*p^13-223254325307259664640*s^6*p^12-\
22333748324515928896*s^2*p^14+13828827077497834016*s^4*p^14-\
17159805122213006976*s^6*p^13-1376119577971670304*s^2*p^15+351353169627403776*
s^14*p^12+270565786927103232*s^12*p^13+14975641554655545164800*s^16*p^8+
348732044486747047488*s^8*p^12+56255964349149262336*s^10*p^11+
6070793721848758272*s^26*p^7+2300982557582336*s^22*p^11+197579880923264*s^18*p
^13+898945138915712*s^20*p^12+442621600164*p^18*s^8+5035083311923712*s^24*p^10
+5043719600944971776*s^34*p+42045828605252160*s^8*p^15-35247014250501504*s^10*
p^14-890112072*s^14*p^17+495588923616*s^16*p^15+4252695832*p^19*s^8-\
112804126920*s^14*p^16+2119275353792*s^18*p^14+2400613729792*s^32*p^8+
1713309031936*s^28*p^10+967527874048*s^26*p^11+199875817740288*s^28*p^9+
132510286236672*s^26*p^10+352202675182501888*s^34*p^3+1810592659823919104*s^34
*p^2-569734380519424*s^40-52845437144*s^2*p^20+5824064810950066176*s^34+
868096195307164*p^18-20406499944*p^18*s^10+7597978617558848*s^12*p^14+
5929327189205760*s^14*p^13+406214672285166080*s^18*p^11+116890786582545472*s^
16*p^12+63436458656*s^20*p^14+4688304632*p^17*s^12+6978076718057540864*s^12*p^
12-5207425199232*s^14*p^15+7858491415144448*s^26*p^9+48694256000928*s^16*p^14+
135978852002244139008*s^12*p^11-99384398123880*p^18*s^2+75735955281408*s^24*p^
11+5684633073768824832*s^28*p^6+72963965717790982144*s^28*p^5+
642612669773240991744*s^28*p^4+14928575433991666794496*s^28*p^2-\
1129575115751776512*s^6*p^14+799683188017526144*s^4*p^15+13147724664*p^21+
429981696*s^48-247934422614016*s^40*p+101801189720064*s^34*p^6+
132888974296645632*s^32*p^5+231395053258407936*s^30*p^6+270675200553295872*s^
26*p^8+299383288099438592*s^28*p^7+10165267765768192*s^28*p^8+9361648787980288
*s^30*p^7+143176516617088*s^12*p^15+1531740882012*s^12*p^16-8268046925824*s^42
*p-195881365929984*s^38*p^3-36366897250304*s^40*p^2+28441931910360*s^8*p^17-\
63859288561400*s^10*p^16-100518066760664*p^17*s^6+42462172258916*p^18*s^4+
101198432532166656*s^22*p^10+196144840589170688*s^24*p^9+43104962149303296*s^
20*p^11+2208926525440*s^30*p^9-753189480*p^21*s^2+2732463047802880*s^34*p^5+
636694897000448*s^36*p^4+6713348448444416*s^32*p^6+(-4674587655667712*s^38-\
1162480768253952*s^38*p+5385715673403288943995125760*p-3822059520*s^46-\
9383061749760*s^42-28501199948171067392*s^16*p^9-1580079897743820800*s^16*p^10
-73209042704691200*s^16*p^11-78224818176*s^44+54251395179216896*s^32*p^4+
374317415899664068792811520*s^2-28051241824970495492096*s^26-\
227947453021308321792*s^30-2878038602534484967424*s^28-\
170716933825852350660608*s^22*p^3-600978156292627067043840*s^22*p^2-\
30359232672145716543488*s^20*p^5-8683727934182048923648*s^26*p^2-\
31728205372033922760704*s^22*p^4-21059549469625787875328*s^24*p^3-\
85519824336012646023168*s^24*p^2-2066577309190278086656*s^28*p-\
200783487976550873169920*s^24*p-23796122684688483483648*s^26*p+
3162962778007504*p^17-184064674183569408*s^14*p^11+696510567495687641137938432
*s^4+755243254821509519829368832*s^2*p+716786333315636689120002048*s^2*p^2+
4309757512212625800768258048*p^3+6040149089472534276966187008*p^2+
1461407580160*s^36*p^5-14519835581547020288*s^32-208749273131919360*s^18*p^10+
1624414997382652345545916416*s^4*p^2+1085729256656403410476597248*s^4*p^3-\
148920798740095828148355072*s^6*p-140534455915519573805236224*s^6*p^2+
174527405510902614301999104*s^2*p^4+424079405684560128736493568*s^2*p^3+
1540781080488079886543486976*s^4*p+843093739126774840962318336*s^8*p+
785349627302556450767241216*s^8*p^2-84265738752214613447671808*s^6*p^3+
361451485485205775896805376*s^10*p-75442307179676826212499456*s^6+
2195997284538000479187763200*p^4+427477999999909039608692736*s^8+
50723786417693165458817024*s^12+195223606570498665980362752*s^10+
850223076924569666301591552*p^5+13089205963077135828664320*p^8+
64268022459220177182916608*p^7+259828851826096703828361216*p^6+
516210779771061997195886592*s^4*p^4+52669773488932238881456128*s^2*p^5+
11917149671901070270365696*s^2*p^6+14639689814366575205548032*s^12*p^4-\
35990489392845387657510912*s^6*p^4+314090744829038811289223168*s^10*p^2+
52452781879036136151449600*s^4*p^6+459329693418489900933578752*s^8*p^3+
189115553367946754674655232*s^8*p^4-11635365141416613900189696*s^6*p^5+
185675241641112505074712576*s^4*p^5+2009524758876348869050368*s^2*p^7-\
18954272335012897832828928*s^14*p+93627708261402781330440192*s^12*p+
170245788647597976043126784*s^10*p^3+79371861387374767521136640*s^12*p^2+
58234581277619176368242688*s^8*p^5+11924386608815065088589824*s^4*p^7+
41157325380746896843210752*s^12*p^3-9068992464514490776420352*s^14*p^2-\
34758979789910364953509888*s^16*p-2954032005604238877917184*s^6*p^6+
64505420560354464476168192*s^10*p^4+18140877962702351254945792*s^10*p^5-\
2180457923662993357275136*s^14*p^3-20976940869427726518321152*s^16*p^2-\
17960073445048250303250432*s^18*p+238096201487766674702336*s^2*p^8+
340776604442555036073984*s^4*p^9-100697221132788524711936*s^6*p^8-\
166209438582548211433472*s^14*p^4-10285365564531207320895488*s^18*p^2+
3922970759482757153816576*s^10*p^6-5701696624867123228835840*s^20*p-\
7733682005835266152988672*s^16*p^3+3790932757355804502786048*s^12*p^5+
2634611928729447394902016*s^8*p^7+401673745323865311166464*s^8*p^8-\
1947622156448160353091584*s^16*p^4-3018605073549359035973632*s^20*p^2+
739049937708665476612096*s^12*p^6-603241982675612612100096*s^6*p^7+
13906377237194526850023424*s^8*p^6+2217150613256022732685312*s^4*p^8+
14793206050996821344256*s^2*p^9-3574405352451521686536192*s^18*p^3+
58005587438297731301376*s^14*p^5+666541883093494463266816*s^10*p^7-\
13890844518537123233792*s^6*p^9+43578381758490020007936*s^4*p^10-\
1045893691422228699136*s^2*p^10-445236141348259680256*s^2*p^11-\
16698828843861740086099968*s^14-26541309374959249044537344*s^16-\
14380427810262902472966144*s^18-4898549679943869137944576*s^20+
2221216482137318348046336*p^9+38087861463719681609728*p^11+
316590270574961737205760*p^10+3876994332558244193792*p^12-\
1172879287992181535539200*s^22-208498297323904309395456*s^24+4586725179392*s^
30*p^8-1251991189469741059145728*s^22*p+24276682736882174592*p^14+
333913829580333004288*p^13+1482617100381619200*p^15+75458105000865072*p^16+
75054279369452380160*s^12*p^10+19974896285443227648*s^14*p^9-\
1594647599835413540864*s^6*p^10-152904587955832975360*s^6*p^11-\
355220540468896845791232*s^16*p^5+12738316285952171687936*s^12*p^8+
414178687105790198272*s^4*p^12+4650715898235495641088*s^4*p^11-\
71712745721524473344*s^2*p^12+9744954706731852578816*p^9*s^10-\
141199014122326239215616*s^18*p^5+392770016478833541120*s^14*p^8-\
5124264844588459032576*s^16*p^7-48624127749291733221376*s^16*p^6+
409366138417134116864*p^11*s^8-959933960903937719533568*s^20*p^3+
90101122128684790087680*s^10*p^8-17425605239203922509824*s^18*p^6-\
203833345975626419142656*s^20*p^4+49683993768803925016576*p^9*s^8+
1127820490523366752256*p^9*s^12+110455765183616868352000*s^12*p^7-\
840592880512524030312448*s^18*p^4+5001994483062664099840*p^10*s^8+
22220800061972996554752*s^14*p^6+3855651200747330666496*s^14*p^7+
842946126697364510720*p^10*s^10-7925193078583240704*s^2*p^13+
30683099823621390848*s^4*p^13-12250584110419065344*s^6*p^12-665690751663453568
*s^2*p^14+1878415399799627776*s^4*p^14-817327804071571456*s^6*p^13-\
43867827834866944*s^2*p^15-16624401390466048*s^14*p^12+346590441231360*s^12*p^
13-425339502311269416960*s^16*p^8+27076252766223629312*s^8*p^12+
57926620658539028480*s^10*p^11+66271457275478016*s^26*p^7+23043161149440*s^22*
p^11-1670425876480*s^18*p^13+2736495057408*s^20*p^12+6352902320*p^18*s^8+
73337608079360*s^24*p^10-241975948245729280*s^34*p+1880942453500160*s^8*p^15+
3841489212761344*s^10*p^14-12674500864*s^16*p^15+24961296*p^19*s^8-4720922928*
s^14*p^16-14004581248*s^18*p^14+3546413629440*s^28*p^9+2072486062080*s^26*p^10
+16292181632352256*s^34*p^3+26981916280881152*s^34*p^2-153165593837568*s^40-\
1146046128*s^2*p^20-935892379631616000*s^34+107339231463152*p^18-57218544*p^18
*s^10-115721405934592*s^12*p^14-873365694156800*s^14*p^13-5710228251611136*s^
18*p^11-2758800797614592*s^16*p^12-1014757424*p^17*s^12+102201673378661376*s^
12*p^12-548020332288*s^14*p^15+157454150189056*s^26*p^9-1440291737472*s^16*p^
14+3557566029712711680*s^12*p^11-2947627427760*p^18*s^2+905807265792*s^24*p^11
+98251916928745472*s^28*p^6+523373338882998272*s^28*p^5-3936867992528748544*s^
28*p^4-601990177532898443264*s^28*p^2-45039439700384768*s^6*p^14+
94014730313005312*s^4*p^15+852507504*p^21-18884844322816*s^40*p+3070909579264*
s^34*p^6+5162513900634112*s^32*p^5+7184542353195008*s^30*p^6+4796700072837120*
s^26*p^8+7005999974383616*s^28*p^7+246609012277248*s^28*p^8+284199949107200*s^
30*p^7-5393378712832*s^12*p^15-114602736560*s^12*p^16-1355613732864*s^42*p+
3789070270464*s^38*p^3+1025166016512*s^40*p^2+683556345136*s^8*p^17+
849872417552*s^10*p^16-1965581302848*p^17*s^6+2857349392224*p^18*s^4+
2296116092259084701977804800+633717396017152*s^22*p^10+2260352133840896*s^24*p
^9-14521619107840*s^20*p^11-11892960*p^21*s^2+135176812756992*s^34*p^5+
49074638553088*s^36*p^4+240457169338368*s^32*p^6+1431302126310697984*s^8*p^13-\
5557517212812574720*s^32*p-156432648975679488*s^32*p^2+3117155283461403648*s^
10*p^12+3784741155441904*s^4*p^16-2020285022469376*s^6*p^15+59389260102668544*
s^8*p^14+128050327169318912*s^10*p^13-8739292162437120*s^20*p^10-\
2284743790820432*s^2*p^16-3274489330433732902912*s^24*p^4-\
325927491150474117120*s^24*p^5+4485631377408*s^32*p^7+293036228608*s^38*p^4-\
27230994432*s^42*p^2+126165712896*s^40*p^3-3822059520*s^44*p+
247274327022501888*s^32*p^3-84810889725852254208*s^28*p^3+1026908448*p^17*s^10
-69321444672*s^2*p^19+2876220950032*p^19+58583749008*p^20-93454967889632*p^17*
s^2-72034316620176*p^16*s^6+119596805109040*p^17*s^4-28627907076096*s^14*p^14-\
114794259580416*s^18*p^12-78141087400448*s^16*p^13+1176348692316160*s^36*p^2-\
13537177144131584*s^36*p-2308541018177536*s^22*p^9-622041087028559872*s^22*p^8
-19628257173719023616*s^22*p^7-346901245873463361536*s^22*p^6-\
4015218712565634826240*s^22*p^5-62821160935489536*s^36-2900880*p^20*s^6+
2255682714599424*s^34*p^4+534946128068608*s^36*p^3+7896528*p^22-60759963860992
*s^38*p^2+2677104*p^21*s^4-58320*p^22*s^2+34992*p^23-19347519610703839232*s^24
*p^6+23520044653920256*s^24*p^8-445831249806426112*s^24*p^7-482954048*s^6*p^19
-38540101984*s^6*p^18+275415633408*s^22*p^12+48531345760*s^4*p^19+
77358787555584*p^15*s^10+522265776*s^4*p^20+91170429146759168*s^30*p^5+
518049455382462464*s^30*p^4-540670744430903296*s^30*p^3-24640753902205009920*s
^30*p^2-128668453189497913344*s^30*p+43516836703632*s^8*p^16-\
510388622385946624*s^14*p^10+37238950400*s^20*p^13-459347704585453568*s^20*p^9
-246924721072557195264*s^20*p^7-13157409785545539584*s^20*p^8-\
3237058960172353191936*s^20*p^6-109690425196974669824*s^18*p^8-\
1600591162693063606272*s^18*p^7-5579634787324444672*s^18*p^9+80808521888956416
*s^26*p^6-11865483425799471104*s^26*p^5-203996708180328972288*s^26*p^4-\
1750846882759143587840*s^26*p^3)*T+(672277662269440*s^38+150014194089984*s^38*
p+973872184885823346573312000*p+396191858688*s^42+623826413244825600*s^16*p^9-\
23538244579127296*s^16*p^10-2932530349912064*s^16*p^11+13504610304*s^44+
2155320920244224*s^32*p^4+193456095126182211354624000*s^2+
4231131616513907228672*s^26+51767177200676110336*s^30+514836412585385918464*s^
28+16737612759673522356224*s^22*p^3+65707918645473667186688*s^22*p^2+
2280010543247014232064*s^20*p^5+1141120604979509329920*s^26*p^2+
2749195195921060593664*s^22*p^4+2193303662580060913664*s^24*p^3+
9786900977449860857856*s^24*p^2+357045303240355217408*s^28*p+
25164217029929098805248*s^24*p+3337080734576296329216*s^26*p+184534335906720*p
^17+9847781005287424*s^14*p^11+176893583924947701281587200*s^4+
406156888120737095693107200*s^2*p+405654423287768760157470720*s^2*p^2+
721226629944605377293189120*p^3+1051773728511071820762316800*p^2+
4278126062156644352*s^32-6091015404969984*s^18*p^10+
357670505570752268360220672*s^4*p^2+221780637254581307441152000*s^4*p^3+
53876111412067042534096896*s^6*p+51140164313776110667038720*s^6*p^2+
114947245517765244066201600*s^2*p^4+256322922965517981554049024*s^2*p^3+
364745900338013792045629440*s^4*p+51833585176167404965724160*s^8*p+
44316326037596396203278336*s^8*p^2+30807089235999798756114432*s^6*p^3+
57066864884078985273671680*s^10*p+27122902322012214484008960*s^6+
352386498772419607799267328*p^4+28739347376170721684226048*s^8+
19322535380498616524210176*s^12+33770731521023488984875008*s^10+
130494650882084186540212224*p^5+1725329304589087812427776*p^8+
8943805168840882793152512*p^7+38034922540886461931913216*p^6+
97526524214328446023368704*s^4*p^4+38898764760063680295469056*s^2*p^5+
10310483547697881028886528*s^2*p^6+2917334782370183147159552*s^12*p^4+
13191851898213355782930432*s^6*p^4+45543499719291157119762432*s^10*p^2+
8383200657896402241585152*s^4*p^6+23844235310745730894790656*s^8*p^3+
9038150463663895189913600*s^8*p^4+4262475813052946813288448*s^6*p^5+
32330073069142965557919744*s^4*p^5+2192882966611392620855296*s^2*p^7+
14193751935126079184830464*s^14*p+29370569483112815955804160*s^12*p+
22781579786901059358687232*s^10*p^3+20990627306898778774044672*s^12*p^2+
2560156443784173939851264*s^8*p^5+1741168337785565889888256*s^4*p^7+
9363831810842279253377024*s^12*p^3+8908686779862341084250112*s^14*p^2+
6670116231047375419867136*s^16*p+1076845398746016011911168*s^6*p^6+
7991744749442820250533888*s^10*p^4+2083876118782709372813312*s^10*p^5+
3435751214296975498280960*s^14*p^3+3794333797076450412593152*s^16*p^2+
2501396791493640985772032*s^18*p+380288875812621900890112*s^2*p^8+
40841319566872204312576*s^4*p^9+35627441194802321915904*s^6*p^8+
909234525351300963500032*s^14*p^4+1309954359148789471641600*s^18*p^2+
417634424837301305212928*s^10*p^6+705403501475434994860032*s^20*p+
1305351187104379204272128*s^16*p^3+672504153722327890132992*s^12*p^5+
97122429679325745971200*s^8*p^7+13452994165312746758144*s^8*p^8+
301868505121343476858880*s^16*p^4+338667740392383492128768*s^20*p^2+
118471867912691994984448*s^12*p^6+217512626474651385266176*s^6*p^7+
560992425267705412714496*s^8*p^6+294201441367098327490560*s^4*p^8+
54341903644890553040896*s^2*p^9+410575906506195052003328*s^18*p^3+
174460554461204181942272*s^14*p^5+65599735036421139267584*s^10*p^7+
4771791039276047237120*s^6*p^9+4683752517417085829120*s^4*p^10+
6439239777669073641472*s^2*p^10+634574777701825597440*s^2*p^11+
10483565479978594709012480*s^14+5367619079192731069710336*s^16+
2168243241512303463497728*s^18+661543255104077906837504*s^20+
276147874990561000505344*p^9+4147366356167687540736*p^11+
36941172676574257623040*p^10+391301148361204741120*p^12+
154712737954783471599616*s^22+28494226556269902168064*s^24+
151000455382306973024256*s^22*p+2050822447385801472*p^14+30985339703151259648*
p^13+112631832321451264*p^15+5075272884381424*p^16+9526731375732293632*s^12*p^
10+12772651340335480832*s^14*p^9+524613953307836407808*s^6*p^10+
47335442224427249664*s^6*p^11+49220589321956105388032*s^16*p^5+
1742329218838824738816*s^12*p^8+34859332349968215040*s^4*p^12+
444540715632586813440*s^4*p^11+52000059116665094144*s^2*p^12+
806879813119604375552*p^9*s^10+12287951777210657931264*s^18*p^5+
217420297911281713152*s^14*p^8+472859945568969228288*s^16*p^7+
5746583310856901885952*s^16*p^6+9766991673781493760*p^11*s^8+
96351378434559844548608*s^20*p^3+8160638343287592796160*s^10*p^8+
1233459904275124977664*s^18*p^6+17956883869043400376320*s^20*p^4+
1500619687344582606848*p^9*s^8+146346270524104966144*p^9*s^12+
16231936709860232200192*s^12*p^7+85355206943511198826496*s^18*p^4+
135004859877044662272*p^10*s^8+24964565398663609319424*s^14*p^6+
2692018988922986496000*s^14*p^7+63252693596884320256*p^10*s^10+
3531630747190947840*s^2*p^13+2246354421994680320*s^4*p^13+3490596890293960704*
s^6*p^12+197462942038519296*s^2*p^14+117804013014210048*s^4*p^14+
208529621842907136*s^6*p^13+8991064023429376*s^2*p^15-158824214298624*s^14*p^
12+428793079877632*s^12*p^13+25409960996858781696*s^16*p^8+563812268260476928*
s^8*p^12+3897326340374667264*s^10*p^11+1511998600577024*s^26*p^7-435059396608*
s^22*p^11-97334534144*s^18*p^13-236260082688*s^20*p^12+27329296*p^18*s^8-\
620304789504*s^24*p^10+116942339496214528*s^34*p+23384837558016*s^8*p^15+
173016613177856*s^10*p^14+1222782468751360*s^34*p^3+17828331024023552*s^34*p^2
+26008141955072*s^40+29159136*s^2*p^20+287390309931810816*s^34+5281964962576*p
^18+6587646220800*s^12*p^14-16530982178816*s^14*p^13-354178332389376*s^18*p^11
-128642118925312*s^16*p^12+17105034498512896*s^12*p^12-4662661376*s^14*p^15-\
669597515776*s^26*p^9-28076896000*s^16*p^14+471205402267607040*s^12*p^11+
200650400704*p^18*s^2+2497224038809600*s^28*p^6+89735957878669312*s^28*p^5+
1624190559099813888*s^28*p^4+105216117140770258944*s^28*p^2+9945675870549504*s
^6*p^14+4950689589692672*s^4*p^15+17410464*p^21+4256138526720*s^40*p+
44764880699392*s^32*p^5+39014534873088*s^30*p^6-11211994382336*s^26*p^8+
15248594108416*s^28*p^7-502405554176*s^28*p^8-175550693376*s^30*p^7+
45157516032*s^12*p^15-41672208*s^12*p^16+27009220608*s^42*p+95840894976*s^38*p
^3+143266938880*s^40*p^2+4953838112*s^8*p^17+31114799456*s^10*p^16+
205451173824*p^17*s^6+71131744864*p^18*s^4-27471200755712*s^22*p^10-\
26803120029696*s^24*p^9-18913761513472*s^20*p^11+132192*p^21*s^2+156777840640*
s^34*p^5+113607704576*s^36*p^4+86823600128*s^32*p^6+25620769997459456*s^8*p^13
+2150852596919697408*s^32*p+430503908511580160*s^32*p^2+185735396541693952*s^
10*p^12+162828491265808*s^4*p^16+370097231756544*s^6*p^15+897003622206464*s^8*
p^14+6669388183203840*s^10*p^13-539448322392064*s^20*p^10+327952931448160*s^2*
p^16+310326587639022485504*s^24*p^4+28400477047329128448*s^24*p^5+
42983582195515392*s^32*p^3+17028802136193892352*s^28*p^3+136695392*p^17*s^10+
3046598848*s^2*p^19+114614328256*p^19+1772535312*p^20+
430382448074270089543680000+9350074836960*p^17*s^2+10362037859136*p^16*s^6+
4039800058944*p^17*s^4-449582198272*s^14*p^14-9175583571968*s^18*p^12-\
2905090932736*s^16*p^13+506536151482368*s^36*p^2+4831839537594368*s^36*p-\
375361108869120*s^22*p^9+18398270062166016*s^22*p^8+960162647633887232*s^22*p^
7+21757499433725329408*s^22*p^6+301096942529953136640*s^22*p^5+
15489584482746368*s^36+33781124694016*s^34*p^4+18956061507584*s^36*p^3+81648*p
^22+9084206055424*s^38*p^2+1631686620612526080*s^24*p^6+362341172600832*s^24*p
^8+51397747379601408*s^24*p^7+15312960*s^6*p^19+2573089728*s^6*p^18+792611648*
s^4*p^19+3021759980288*p^15*s^10+4203792*s^4*p^20+2754409499983872*s^30*p^5+
72929376890519552*s^30*p^4+1003295679130370048*s^30*p^3+7666348801363279872*s^
30*p^2+30972978318750515200*s^30*p+428701146640*s^8*p^16+503488077405339648*s^
14*p^10-1640559160819712*s^20*p^9+11059148926805147648*s^20*p^7+
327285463965081600*s^20*p^8+197271062655685754880*s^20*p^6+3265854362374324224
*s^18*p^8+83308385024153288704*s^18*p^7+15597627679260672*s^18*p^9+
81238907039907840*s^26*p^6+1912158048580796416*s^26*p^5+26084707379414302720*s
^26*p^4+220270972045847691264*s^26*p^3)*T^2+(-38296101060608*s^38-\
6712698339328*s^38*p+110116421907252550041600000*p-23970447360*s^42-\
1280473794674688*s^16*p^9+527170092015616*s^16*p^10+25146739326976*s^16*p^11-\
90647824957440*s^32*p^4+36851936749152908083200000*s^2-429729016197490409472*s
^26-4698479563821285376*s^30-49914102419520749568*s^28-1413607775430145736704*
s^22*p^3-5978999203755898961920*s^22*p^2-168549517473084342272*s^20*p^5-\
97194023904549535744*s^26*p^2-216717776220810379264*s^22*p^4-\
180300801473463189504*s^24*p^3-871889429568736460800*s^24*p^2-\
31411971781015109632*s^28*p-2429993948533573550080*s^24*p-\
310968955061514797056*s^26*p+5573265753664*p^17+1092893875830784*s^14*p^11+
26585026406723852697600000*s^4+75539305303805893017600000*s^2*p+
73534373537894604472320000*s^2*p^2+74703074914932589854720000*p^3+
113958604635299374694400000*p^2-359056219593244672*s^32-187041014751232*s^18*p
^10+48353442318170065207296000*s^4*p^2+28237692220739067733606400*s^4*p^3+
19980638042104925257728000*s^6*p+17974870077495859268812800*s^6*p^2+
19677730110436296661401600*s^2*p^4+45201452667038565138432000*s^2*p^3+
52107884636125805936640000*s^4*p+2351769611138435960012800*s^8*p+
2175894462484031618416640*s^8*p^2+10138108175605726718197760*s^6*p^3+
786773981150567110541312*s^10*p+10474855747436292341760000*s^6+
34800019379234697314304000*p^4+1156558325829600804864000*s^8-\
2824824888145683152896*s^12+332268430166781979525120*s^10+
12250732460851647975260160*p^5+136139243305207719198720*p^8+
750896977976792733450240*p^7+3383104768285130183540736*p^6+
11635341471902604627804160*s^4*p^4+6448930833653718116728832*s^2*p^5+
1650918970015154071797760*s^2*p^6+80989731543233048084480*s^12*p^4+
4019098414137144980275200*s^6*p^4+744105912367367617249280*s^10*p^2+
863355901747216265379840*s^4*p^6+1231356123016545592934400*s^8*p^3+
481247020920560418816000*s^8*p^4+1189746253475576152064000*s^6*p^5+
3594412646726538871439360*s^4*p^5+338061218194741307637760*s^2*p^7-\
510433565588307490897920*s^14*p+274156513169097694904320*s^12*p+
402016107695371756503040*s^10*p^3+362267155469573417861120*s^12*p^2+
138670737360794938245120*s^8*p^5+165004416069119956746240*s^4*p^7+
219421347589190519357440*s^12*p^3-214790978371905409515520*s^14*p^2-\
504058129124078229913600*s^16*p+272649827244634030080000*s^6*p^6+
143183933983617565327360*s^10*p^4+36227179921012226523136*s^10*p^5-\
43344601722440321597440*s^14*p^3-251022280578570953687040*s^16*p^2-\
230880997068977702174720*s^18*p+56238817770633315614720*s^2*p^8+
3201392401418388439040*s^4*p^9+7208560258621183098880*s^6*p^8-\
1513371965936128491520*s^14*p^4-110955973517622210723840*s^18*p^2+
6806098772003533225984*s^10*p^6-68744193085577495576576*s^20*p-\
74252092822721386250240*s^16*p^3+20354174171043565928448*s^12*p^5+
5326248008695334830080*s^8*p^7+738997718758841712640*s^8*p^8-\
14437622391818834411520*s^16*p^4-30608457274247312572416*s^20*p^2+
3683175064862482366464*s^12*p^6+49474893303263230689280*s^6*p^7+
30647842454911345623040*s^8*p^6+25464619921649017159680*s^4*p^8+
7675674352532403978240*s^2*p^9-31837930672503883038720*s^18*p^3+
1495700588168857255936*s^14*p^5+976771969718542925824*s^10*p^7+
849838392803070115840*s^6*p^9+329229392480636985344*s^4*p^10+
864194051532658204672*s^2*p^10+80405786344965226496*s^2*p^11-\
503175848606865167482880*s^14-456521167425123437772800*s^16-\
217255419619381199503360*s^18-69408957561731666673664*s^20+
20377398309007101460480*p^9+262775317833454452736*p^11+2534549421457749417984*
p^10+22709478891852425216*p^12-16349746825440255803392*s^22-\
2976287915393316552704*s^24-14817341403870953209856*s^22*p+96708648140655104*p
^14+1630938014280972288*p^13+4684686435705856*p^15+182419301208384*p^16+
222751835975106560*s^12*p^10+564983811116498944*s^14*p^9+81275397238020349952*
s^6*p^10+6291310768909910016*s^6*p^11-1923329499796374290432*s^16*p^5+
50092019799820599296*s^12*p^8+1898033888652943360*s^4*p^12+
27696085795214213120*s^4*p^11+6171492367121950720*s^2*p^12+9626396178682085376
*p^9*s^10-806325391996719464448*s^18*p^5+7600811433583968256*s^14*p^8-\
10714758241819295744*s^16*p^7-176383362762230071296*s^16*p^6+
534742458503462912*p^11*s^8-8080722757676882198528*s^20*p^3+
109153599077282086912*s^10*p^8-76554972209789140992*s^18*p^6-\
1404301891640926142464*s^20*p^4+82496841606158090240*p^9*s^8+
3843951073915437056*p^9*s^12+494695467041428602880*s^12*p^7-\
6064675951951735685120*s^18*p^4+7419189057538899968*p^10*s^8+
449205234270814208000*s^14*p^6+71748351712134430720*s^14*p^7+
676043818016030720*p^10*s^10+388649093949108224*s^2*p^13+105034667823509504*s^
4*p^13+391268285754302464*s^6*p^12+19885389239545344*s^2*p^14+4624986869961216
*s^4*p^14+19285520307122176*s^6*p^13+813940685097984*s^2*p^15+26667865464832*s
^14*p^12+6600884670464*s^12*p^13-369716276263059456*s^16*p^8+30505018963128320
*s^8*p^12+37935165673537536*s^10*p^11-124673748369408*s^26*p^7-\
7760706833219584*s^34*p+1030834938880*s^8*p^15+1462584977920*s^10*p^14-\
53160861237248*s^34*p^3-984914172313600*s^34*p^2-914177916928*s^40+589248*s^2*
p^20-22145053388439552*s^34+128701218432*p^18+90938910208*s^12*p^14+
390241013760*s^14*p^13-2458261176320*s^18*p^11+522328401920*s^16*p^12+
302447356207104*s^12*p^12+9624547118383104*s^12*p^11+10688712832*p^18*s^2-\
139715886841856*s^28*p^6-5159169937113088*s^28*p^5-103120405048328192*s^28*p^4
-8340940101412454400*s^28*p^2+736762608322048*s^6*p^14+158343523692544*s^4*p^
15+108864*p^21-71911342080*s^40*p-1370812317696*s^32*p^5-1598787551232*s^30*p^
6-1256821489664*s^26*p^8-1572998217728*s^28*p^7+608225280*s^12*p^15+102573632*
s^8*p^17+186302144*s^10*p^16+5348607744*p^17*s^6+838634368*p^18*s^4-\
363413299200*s^22*p^10-784091447296*s^24*p^9-112271540224*s^20*p^11+
1347433009487872*s^8*p^13-158457782373187584*s^32*p-27244487853998080*s^32*p^2
+1689338220605440*s^10*p^12+4064202919040*s^4*p^16+21047667341312*s^6*p^15+
44453983616512*s^8*p^14+58192065105920*s^10*p^13-15262057373696*s^20*p^10+
26027994315200*s^2*p^16-23662707020551684096*s^24*p^4-2042380117334818816*s^24
*p^5-2268269973078016*s^32*p^3-1209161478414794752*s^28*p^3+115145472*s^2*p^19
+2112575616*p^19+21971520*p^20+50675308574051598336000000+626695472896*p^17*s^
2+423341781888*p^16*s^6+73597912448*p^17*s^4+2609570304*s^14*p^14-14869518336*
s^18*p^12+4307216384*s^16*p^13-23760411295744*s^36*p^2-283543448059904*s^36*p-\
44225720942592*s^22*p^9-2410822443204608*s^22*p^8-77149966411759616*s^22*p^7-\
1601201861754486784*s^22*p^6-22498390940410970112*s^22*p^5-1078087131332608*s^
36-1013598126080*s^34*p^4-627220414464*s^36*p^3-275718864896*s^38*p^2-\
115872120759517184*s^24*p^6-86213737906176*s^24*p^8-4166295142268928*s^24*p^7+
31937920*s^6*p^18+4523136*s^4*p^19+23783865344*p^15*s^10-124868201807872*s^30*
p^5-3889601127120896*s^30*p^4-62457793449295872*s^30*p^3-548766343457931264*s^
30*p^2-2512532312680300544*s^30*p+14979905088*s^8*p^16+29768104061779968*s^14*
p^10-944967160758272*s^20*p^9-848242973312811008*s^20*p^7-34872647538049024*s^
20*p^8-14248581554850103296*s^20*p^6-252734442482040832*s^18*p^8-\
5217252582307921920*s^18*p^7-8475676631171072*s^18*p^9-5306822182961152*s^26*p
^6-126655871891537920*s^26*p^5-1855846324652474368*s^26*p^4-\
17118084667157774336*s^26*p^3)*T^3+(1044725628928*s^38+89279954944*s^38*p+
8466811219663257600000000*p+1924894159929344*s^16*p^9+37611033624576*s^16*p^10
+397211959296*s^16*p^11+988379873280*s^32*p^4+4218779124331315200000000*s^2+
25602057357248954368*s^26+231428518330761216*s^30+2713151939087958016*s^28+
75059484083649249280*s^22*p^3+357770469655588110336*s^22*p^2+
8239789184658702336*s^20*p^5+4498760265352871936*s^26*p^2+9999528357783404544*
s^22*p^4+8226054638990786560*s^24*p^3+45708659327567396864*s^24*p^2+
1496205090023800832*s^28*p+143467527272516288512*s^24*p+16486250800905977856*s
^26*p+90816384384*p^17-4589365100544*s^14*p^11+2836379100876963840000000*s^4+
8295697151209635840000000*s^2*p+7730269007335391232000000*s^2*p^2+
5198458227382812672000000*p^3+8346814522883112960000000*p^2+15696887120134144*
s^32+4132729815040*s^18*p^10+4605592951976558592000000*s^4*p^2+
2531583736269294796800000*s^4*p^3+2774036258897657856000000*s^6*p+
2301581241372219801600000*s^6*p^2+1880816660256174899200000*s^2*p^4+
4537425050226786304000000*s^2*p^3+5258694805027160064000000*s^4*p+
836117935287277977600000*s^8*p+654914495678345379840000*s^8*p^2+
1195075156606776770560000*s^6*p^3+130641961433822134272000*s^10*p+
1575883300291608576000000*s^6+2294007375564546048000000*p^4+
505345016805163008000000*s^8+98153612869762023424000*s^12+
103357808427285872640000*s^10+762445073858925035520000*p^5+
6954364088632185733120*p^8+41164142040394275225600*p^7+
198038054538569711616000*p^6+978637962737867816960000*s^4*p^4+
584974658145394491392000*s^2*p^5+141572465882485188198400*s^2*p^6+
1839020101075919175680*s^12*p^4+434828197006369619968000*s^6*p^4+
78892566181275972403200*s^10*p^2+63113758503757941309440*s^4*p^6+
322083196076436750336000*s^8*p^3+111184703433166710374400*s^8*p^4+
117618394179711412469760*s^6*p^5+282513934875524884070400*s^4*p^5+
27282796888930170961920*s^2*p^7+109842641585636775034880*s^14*p+
105048303299187231948800*s^12*p+30892293554305016791040*s^10*p^3+
48966058833364427735040*s^12*p^2+28528546644375335075840*s^8*p^5+
11155865952873857679360*s^4*p^7+12671749854081570570240*s^12*p^3+
54811001827936981483520*s^14*p^2+60209619774136396021760*s^16*p+
24484373188738081095680*s^6*p^6+8975217378169853050880*s^10*p^4+
2073394320877084999680*s^10*p^5+16230382925586859294720*s^14*p^3+
29022678352095766118400*s^16*p^2+21044367861693619896320*s^18*p+
4248640258864086712320*s^2*p^8+181159426259338526720*s^4*p^9+
521108141452824084480*s^6*p^8+3154024350114581053440*s^14*p^4+
9426709154000954982400*s^18*p^2+390654838634559569920*s^10*p^6+
5240339656430374092800*s^20*p+8342547827224278466560*s^16*p^3+
96054715167670272000*s^12*p^5+865885630917994086400*s^8*p^7+
105295671196759736320*s^8*p^8+1588398766621327360000*s^16*p^4+
2134349930575570141184*s^20*p^2-16875825557894856704*s^12*p^6+
4005291984317946265600*s^6*p^7+5620167259130911784960*s^8*p^6+
1581535377228675317760*s^4*p^8+539363189402267811840*s^2*p^9+
2502216111114934026240*s^18*p^3+418739230359411490816*s^14*p^5+
59844570501851643904*s^10*p^7+54213984168345600000*s^6*p^9+
16805704325623906304*s^4*p^10+56050742956119982080*s^2*p^10+
4768250159457173504*s^2*p^11+99240222851446131916800*s^14+
56451136475371898142720*s^16+21117607839670342778880*s^18+
5731117813529302794240*s^20+964339925312057507840*p^9+10441522865661378560*p^
11+110359683831492935680*p^10+815332405219526656*p^12+1190253253676740116480*s
^22+194954344279431970816*s^24+983790353557672165376*s^22*p+2722590436126720*p
^14+52258832939331584*p^13+113520634112000*p^15+3699500476000*p^16-\
1108124550692864*s^12*p^10+80562236162048*s^14*p^9+4508712966541279232*s^6*p^
10+297952478297718784*s^6*p^11+210290002488430952448*s^16*p^5-\
479752409637519360*s^12*p^8+75698633029124096*s^4*p^12+1259552314669006848*s^4
*p^11+330699571129442304*s^2*p^12+706702892985221120*p^9*s^10+
52487096781872562176*s^18*p^5+75159305746513920*s^14*p^8+1318535041236074496*s
^16*p^7+19756618957005520896*s^16*p^6+45215839000526848*p^11*s^8+
509379363514494222336*s^20*p^3+7337628271203188736*s^10*p^8+
4425067910607142912*s^18*p^6+78786598178977218560*s^20*p^4+
10127441176969871360*p^9*s^8-31039229415653376*p^9*s^12-4331056692958593024*s^
12*p^7+436620064048147333120*s^18*p^4+767005087142313984*p^10*s^8+
38082607012802199552*s^14*p^6+2272698230032564224*s^14*p^7+52397219731800064*p
^10*s^10+18535484231372800*s^2*p^13+3598588844421120*s^4*p^13+
15449560641265664*s^6*p^12+827381469566976*s^2*p^14+132338278397952*s^4*p^14+
615214651297792*s^6*p^13+28743591464960*s^2*p^15-78043144192*s^14*p^12+
37037346816*s^12*p^13+61465545913909248*s^16*p^8+2032253118271488*s^8*p^12+
2917540143562752*s^10*p^11+1068646793216*s^26*p^7+225546659168256*s^34*p+
22015567872*s^8*p^15+54627391488*s^10*p^14+579828973568*s^34*p^3+
20042162896896*s^34*p^2+22319988736*s^40+828350050336768*s^34+1579868736*p^18+
468408320*s^12*p^14-415371264*s^14*p^13+27247443968*s^18*p^11+1619519488*s^16*
p^12+903746306048*s^12*p^12-9450459103232*s^12*p^11+160184192*p^18*s^2+
1314419900416*s^28*p^6+92884782022656*s^28*p^5+2680236380520448*s^28*p^4+
339538769055055872*s^28*p^2+18163696521216*s^6*p^14+3632790958080*s^4*p^15+
29053568*p^17*s^6+4849216*p^18*s^4+67272762298368*s^8*p^13+5744319520571392*s^
32*p+775330839134208*s^32*p^2+117715332964352*s^10*p^12+70098686528*s^4*p^16+
374559252480*s^6*p^15+1545780150272*s^8*p^14+3244845166592*s^10*p^13+
122981384192*s^20*p^10+749431286400*s^2*p^16+913471109058265088*s^24*p^4+
63992003677913088*s^24*p^5+45669041569792*s^32*p^3+40533291006164992*s^28*p^3+
881280*s^2*p^19+17366400*p^19+90720*p^20+13802801024*p^17*s^2+4815463040*p^16*
s^6+848509056*p^17*s^4+4080698475835392000000000+255563137024*s^36*p^2+
5935468642304*s^36*p+341852815360*s^22*p^9+37961730293760*s^22*p^8+
1829129005563904*s^22*p^7+50368580164780032*s^22*p^6+875968065048674304*s^22*p
^5+33411913744384*s^36+2756340432764928*s^24*p^6+688133128192*s^24*p^8+
66575482224640*s^24*p^7+423514112*p^15*s^10+1286276644864*s^30*p^5+
74930781683712*s^30*p^4+1711785757376512*s^30*p^3+19215400382234624*s^30*p^2+
106185254217187328*s^30*p+146340448*s^8*p^16-109389165887488*s^14*p^10+
15704153260032*s^20*p^9+28355871800033280*s^20*p^7+877382867255296*s^20*p^8+
589024356577312768*s^20*p^6+10501279526879232*s^18*p^8+260876357375885312*s^18
*p^7+273654539091968*s^18*p^9+89174988816384*s^26*p^6+3122921208807424*s^26*p^
5+59676270079770624*s^26*p^4+673574686323376128*s^26*p^3)*T^4+(-10653532160*s^
38+228362203791360000000000+450067215974400000000000*p-60166369443840*s^16*p^9
-876528304128*s^16*p^10-5213650944*s^16*p^11+315230928076800000000000*s^2-\
928815775962103808*s^26-6443510928506880*s^30-86439153717215232*s^28-\
2500113991930478592*s^22*p^3-13545818299840856064*s^22*p^2-252591978974281728*
s^20*p^5-121112288601047040*s^26*p^2-285937207458398208*s^22*p^4-\
225916411308933120*s^24*p^3-1468772147571720192*s^24*p^2-40318944757678080*s^
28*p-5262036684186320896*s^24*p-521727626516103168*s^26*p+759850752*p^17+
110959460352*s^14*p^11+216821440217088000000000*s^4+590539584503808000000000*s
^2*p+522624892531507200000000*s^2*p^2+247179630949171200000000*p^3+
420281392545792000000000*p^2-382027828297728*s^32-36707532800*s^18*p^10+
319490735816048640000000*s^4*p^2+166284807445413888000000*s^4*p^3+
197782124646891520000000*s^6*p+154811945439461376000000*s^6*p^2+
113458055198441472000000*s^2*p^4+290333596947578880000000*s^2*p^3+
383679097267814400000000*s^4*p+81296716465176576000000*s^8*p+
61639926607773696000000*s^8*p^2+75231328246431744000000*s^6*p^3+
11585166097829068800000*s^10*p+118154731592089600000000*s^6+
102646915936911360000000*p^4+49519080384757760000000*s^8-\
11455542985123430400000*s^12+4464265810830950400000*s^10+
31979562858754867200000*p^5+233254927689940992000*p^8+1495947235250667520000*p
^7+7751584054838886400000*p^6+60591561531162624000000*s^4*p^4+
33121533200223436800000*s^2*p^5+7485862018508718080000*s^2*p^6-\
171724964683485020160*s^12*p^4+25409295229786521600000*s^6*p^4+
10918276892133949440000*s^10*p^2+3418077184610402304000*s^4*p^6+
28670613098279731200000*s^8*p^3+9158447611257815040000*s^8*p^4+
6326033878578364416000*s^6*p^5+16405491137300398080000*s^4*p^5+
1339362951331971072000*s^2*p^7-10058444437865889792000*s^14*p-\
11900925233269309440000*s^12*p+5680125228733169664000*s^10*p^3-\
5355993407145639936000*s^12*p^2+2129979492631157145600*s^8*p^5+
559817051488675430400*s^4*p^7-1318354376456562278400*s^12*p^3-\
4850311394898424627200*s^14*p^2-4252063457653397913600*s^16*p+
1201201108327674675200*s^6*p^6+1908549750633214771200*s^10*p^4+
447543702218870882304*s^10*p^5-1389419482720543703040*s^14*p^3-\
1930740619541773025280*s^16*p^2-1216078818926321991680*s^18*p+
192317895539805388800*s^2*p^8+7615766367664865280*s^4*p^9+20631060253617684480
*s^6*p^8-261863496667354890240*s^14*p^4-504148175618215772160*s^18*p^2+
76402908922614644736*s^10*p^6-256808124650612588544*s^20*p-\
520023422196661616640*s^16*p^3-3366803231817596928*s^12*p^5+
50042946479818014720*s^8*p^7+5195601103466004480*s^8*p^8-92140463884861440000*
s^16*p^4-95275600119651631104*s^20*p^2+3075221101813432320*s^12*p^6+
177492085855417794560*s^6*p^7+372830961044708392960*s^8*p^6+
72976308149759508480*s^4*p^8+22328136699610398720*s^2*p^9-\
122744392820132413440*s^18*p^3-33909343929224921088*s^14*p^5+
9713176456332312576*s^10*p^7+1893241333429043200*s^6*p^9+636343067973255168*s^
4*p^10+2101055387457650688*s^2*p^10+159865441630617600*s^2*p^11-\
9406742764600688640000*s^14-4214060442659586048000*s^16-1309324082236148940800
*s^18-305362703281486299136*s^20+29644927179364761600*p^9+262536480495304704*p
^11+3083677904556097536*p^10+18218986100465664*p^12-55506752156737732608*s^22-\
8018341497193627648*s^24-41608143873779957760*s^22*p+45606702987264*p^14+
1021556141137920*p^13+1584209502208*p^15+41287787776*p^16+250979538173952*s^12
*p^10-130025521152000*s^14*p^9+136746156410011648*s^6*p^10+7694776414568448*s^
6*p^11-11249496357819383808*s^16*p^5+71631973777932288*s^12*p^8+
2215174248701952*s^4*p^12+42334074257473536*s^4*p^11+9762877498220544*s^2*p^12
+66543746472738816*p^9*s^10-2082070811841134592*s^18*p^5-7148773331435520*s^14
*p^8-57433027195699200*s^16*p^7-962482711508287488*s^16*p^6+1198207884656640*p
^11*s^8-20452492218665533440*s^20*p^3+928178553901547520*s^10*p^8-\
153050728179957760*s^18*p^6-2797443473184129024*s^20*p^4+417422609552506880*p^
9*s^8+5183559441580032*p^9*s^12+641898909486022656*s^12*p^7-\
19415348339948912640*s^18*p^4+25749901204979712*p^10*s^8-3047633497752600576*s
^14*p^6-186085584238804992*s^14*p^7+3530703511683072*p^10*s^10+472049422958592
*s^2*p^13+89265568849920*s^4*p^13+330800022773760*s^6*p^12+17673973536768*s^2*
p^14+2675542855680*s^4*p^14+10507001659392*s^6*p^13+494444466176*s^2*p^15+
1571168256*s^14*p^12+1225383936*s^12*p^13-2325709432553472*s^16*p^8+
40727863222272*s^8*p^12+134643722158080*s^10*p^11-3214078377984*s^34*p+
93122560*s^8*p^15+401381376*s^10*p^14-143923347456*s^34*p^2-17657701072896*s^
34+8808192*p^18+146782347264*s^12*p^12+7899332542464*s^12*p^11+702720*p^18*s^2
-552043806720*s^28*p^5-30864303980544*s^28*p^4-7453182611423232*s^28*p^2+
232622346240*s^6*p^14+56211664896*s^4*p^15+955066048512*s^8*p^13-\
105318017138688*s^32*p-9548995756032*s^32*p^2+3492527480832*s^10*p^12+
739176192*s^4*p^16+3208687616*s^6*p^15+13822408704*s^8*p^14+55202414592*s^10*p
^13+9733050624*s^2*p^16-20667101683384320*s^24*p^4-1123652638605312*s^24*p^5-\
284222816256*s^32*p^3-682005859663872*s^28*p^3+48384*p^19+120304128*p^17*s^2+
20781824*p^16*s^6+4581120*p^17*s^4-53267660800*s^36*p-258223374336*s^22*p^8-\
23577624576000*s^22*p^7-930183052787712*s^22*p^6-20734943705432064*s^22*p^5-\
588595068928*s^36-33590810771456*s^24*p^6-425534160896*s^24*p^7-443642019840*s
^30*p^4-19853469548544*s^30*p^3-328703812829184*s^30*p^2-2389643567824896*s^30
*p+1328877404160*s^14*p^10-117693743104*s^20*p^9-568657456398336*s^20*p^7-\
12369303699456*s^20*p^8-15039751852654592*s^20*p^6-243217831821312*s^18*p^8-\
7599048094646272*s^18*p^7-4514468593664*s^18*p^9-545544208384*s^26*p^6-\
36683366006784*s^26*p^5-1016311830282240*s^26*p^4-14863095155392512*s^26*p^3)*
T^5+(16243620249600000000000*p+926821384192*s^16*p^9+8216051712*s^16*p^10+
15867106099200000000000*s^2+20389233432723456*s^26+110011023884288*s^30+
1692365492322304*s^28+44760518195412992*s^22*p^3+287125686034890752*s^22*p^2+
3880411029569536*s^20*p^5+1802239983222784*s^26*p^2+4156399168782336*s^22*p^4+
3261045976072192*s^24*p^3+26221812408909824*s^24*p^2+637444013686784*s^28*p+
111655250510741504*s^24*p+9617820795011072*s^26*p+2801152*p^17+2232745984*s^14
*p^11+12836939857920000000000*s^4+27997460561920000000000*s^2*p+
23261932093440000000000*s^2*p^2+7856967024640000000000*p^3+
14260039188480000000000*p^2+5310441848832*s^32+16687960489984000000000*s^4*p^2
+8124006458982400000000*s^4*p^3+10613882355712000000000*s^6*p+
7636967214284800000000*s^6*p^2+4398672583065600000000*s^2*p^4+
12086769778688000000000*s^2*p^3+21361385799680000000000*s^4*p+
5118921067724800000000*s^8*p+3272587233198080000000*s^8*p^2+
3414276834590720000000*s^6*p^3+2890409929867264000000*s^10*p+
6908708126720000000000*s^6+3044638334976000000000*p^4+3729363173376000000000*s
^8+1322507947737088000000*s^12+2341417433169920000000*s^10+
881159730626560000000*p^5+4976856234803200000*p^8+34992470940057600000*p^7+
197385951035392000000*p^6+2758296465899520000000*s^4*p^4+
1189811779272704000000*s^2*p^5+247697761560166400000*s^2*p^6+
50546689844969472000*s^12*p^4+1060734477795328000000*s^6*p^4+
1644052458713907200000*s^10*p^2+133000085792358400000*s^4*p^6+
1292663874912256000000*s^8*p^3+352738636529664000000*s^8*p^4+
242576842398105600000*s^6*p^5+692536863254118400000*s^4*p^5+
40536971834163200000*s^2*p^7+598248507886796800000*s^14*p+
1497288477035724800000*s^12*p+570800656246374400000*s^10*p^3+
773653382719078400000*s^12*p^2+70401758236508160000*s^8*p^5+
19928263962787840000*s^4*p^7+241222389082357760000*s^12*p^3+
281293372134522880000*s^14*p^2+179561814231613440000*s^16*p+
42182468188241920000*s^6*p^6+135056866326609920000*s^10*p^4+
23018317139882803200*s^10*p^5+78941203640352768000*s^14*p^3+
76138672319102976000*s^16*p^2+41089737431187456000*s^18*p+5279666958663680000*
s^2*p^8+219998533661491200*s^4*p^9+596769281487667200*s^6*p^8+
14686685789316710400*s^14*p^4+15501897030539673600*s^18*p^2+
2910703804628336640*s^10*p^6+7294804515293757440*s^20*p+19025654888949350400*s
^16*p^3+7499448474434273280*s^12*p^5+1226358453750988800*s^8*p^7+
109404724046069760*s^8*p^8+3101223483510620160*s^16*p^4+2407297346753789952*s^
20*p^2+807975848308113408*s^12*p^6+5679160827445248000*s^6*p^7+
10606903914528768000*s^8*p^6+2354261712912384000*s^4*p^8+550366496587776000*s^
2*p^9+3391854305261649920*s^18*p^3+1901312892393750528*s^14*p^5+
276897669926879232*s^10*p^7+48935366064865280*s^6*p^9+16206408261435392*s^4*p^
10+45917378784133120*s^2*p^10+3048572035203072*s^2*p^11+575485638397132800000*
s^14+189581215085363200000*s^16+48147996994437120000*s^18+9616968553542451200*
s^20+572123555266560000*p^9+4011153898536960*p^11+53285097893068800*p^10+
242237712252928*p^12+1533237639858094080*s^22+196830148257906688*s^24+
1016547472706633728*s^22*p+428210114560*p^14+11576870043648*p^13+11828457472*p
^15+229777152*p^16+4078871379968*s^12*p^10+15485745758208*s^14*p^9+
3105156470800384*s^6*p^10+149698635563008*s^6*p^11+344378274685648896*s^16*p^5
+3652463596142592*s^12*p^8+40906217046016*s^4*p^12+931175503691776*s^4*p^11+
159092075921408*s^2*p^12+1061536401981440*p^9*s^10+43871900568387584*s^18*p^5+
516222864064512*s^14*p^8+1373753016582144*s^16*p^7+26368660604977152*s^16*p^6+
14768173285376*p^11*s^8+451181570972188672*s^20*p^3+19851888997957632*s^10*p^8
+2685966844166144*s^18*p^6+52497330040995840*s^20*p^4+7497258219601920*p^9*s^8
+148591152726016*p^9*s^12+63715735756603392*s^12*p^7+474090611083837440*s^18*p
^4+388561066786816*p^10*s^8+174706510742421504*s^14*p^6+11390386956140544*s^14
*p^7+41243534295040*p^10*s^10+6388728987648*s^2*p^13+1328077406208*s^4*p^13+
5306310066176*s^6*p^12+190647885824*s^2*p^14+30050271232*s^4*p^14+130524577792
*s^6*p^13+3983667200*s^2*p^15+46569476456448*s^16*p^8+389016764416*s^8*p^12+
1105089069056*s^10*p^11+16005464064*s^34*p+169550544896*s^34+16128*p^18+
522174464*s^12*p^12+67992092672*s^12*p^11+126865113088*s^28*p^4+89382530842624
*s^28*p^2+1991712768*s^6*p^14+423350272*s^4*p^15+6354173952*s^8*p^13+
1000022736896*s^32*p+46741323776*s^32*p^2+18341822464*s^10*p^12+2797312*s^4*p^
16+14209024*s^6*p^15+48525312*s^8*p^14+142671872*s^10*p^13+52040192*s^2*p^16+
226320227237888*s^24*p^4+8302104674304*s^24*p^5+5524787560448*s^28*p^3+320000*
p^17*s^2+90168098816*s^22*p^7+6988312346624*s^22*p^6+229704363671552*s^22*p^5+
2667577344*s^36+8739975168000000000000+125595287552*s^24*p^6+89506447360*s^30*
p^3+2899673350144*s^30*p^2+31050466066432*s^30*p+276738998272*s^14*p^10+
4611392929792*s^20*p^7+51776192512*s^20*p^8+177787025489920*s^20*p^6+
2363578646528*s^18*p^8+104819189612544*s^18*p^7+23434887168*s^18*p^9+
140928614400*s^26*p^5+7721831104512*s^26*p^4+167560481865728*s^26*p^3)*T^6+
21576454288970929920*s^8*p^13+168384981313671659520*s^32*p+
61502302122939908096*s^32*p^2-41869092*p^18*s^12+6207670703637817548886573056-\
1460319164082098688*s^10*p^12+37743935639882716*s^4*p^16-62380576297788032*s^6
*p^15+1071773780071730752*s^8*p^14-420633437791432448*s^10*p^13+
1390452555207982592*s^20*p^10+(4096000000000000000*p+8192000000000000000*s^2+
1174405120000*s^26+1342177280*s^30+50331648000*s^28+2290089984000*s^22*p^3+
22900899840000*s^22*p^2+125954949120*s^20*p^5+35232153600*s^26*p^2+
114504499200*s^22*p^4+76336332800*s^24*p^3+1145044992000*s^24*p^2+10066329600*
s^28*p+7633633280000*s^24*p+352321536000*s^26*p+12288000000000000000*s^4+
12288000000000000000*s^2*p+8601600000000000000*s^2*p^2+1433600000000000000*p^3
+3072000000000000000*p^2+16777216*s^32+11182080000000000000*s^4*p^2+
4472832000000000000*s^4*p^3+14909440000000000000*s^6*p+8945664000000000000*s^6
*p^2+1118208000000000000*s^2*p^4+3727360000000000000*s^2*p^3+
17203200000000000000*s^4*p+8945664000000000000*s^8*p+4920115200000000000*s^8*p
^2+3280076800000000000*s^6*p^3+3936092160000000000*s^10*p+11468800000000000000
*s^6+465920000000000000*p^4+7454720000000000000*s^8+1312030720000000000*s^12+
3578265600000000000*s^10+111820800000000000*p^5+329472000000000*p^8+
2928640000000000*p^7+20500480000000000*p^6+1230028800000000000*s^4*p^4+
246005760000000000*s^2*p^5+41000960000000000*s^2*p^6+27552645120000000*s^12*p^
4+820019200000000000*s^6*p^4+1968046080000000000*s^10*p^2+36900864000000000*s^
4*p^6+1640038400000000000*s^8*p^3+369008640000000000*s^8*p^4+
147603456000000000*s^6*p^5+246005760000000000*s^4*p^5+5271552000000000*s^2*p^7
+337379328000000000*s^14*p+1312030720000000000*s^12*p+590413824000000000*s^10*
p^3+590413824000000000*s^12*p^2+59041382400000000*s^8*p^5+4217241600000000*s^4
*p^7+157443686400000000*s^12*p^3+134951731200000000*s^14*p^2+67475865600000000
*s^16*p+19680460800000000*s^6*p^6+118082764800000000*s^10*p^4+
16531587072000000*s^10*p^5+31488737280000000*s^14*p^3+23616552960000000*s^16*p
^2+10496245760000000*s^18*p+527155200000000*s^2*p^8+24600576000000*s^4*p^9+
147603456000000*s^6*p^8+4723310592000000*s^14*p^4+3148873728000000*s^18*p^2+
1653158707200000*s^10*p^6+1259549491200000*s^20*p+4723310592000000*s^16*p^3+
3306317414400000*s^12*p^5+590413824000000*s^8*p^7+36900864000000*s^8*p^8+
590413824000000*s^16*p^4+314887372800000*s^20*p^2+275526451200000*s^12*p^6+
1968046080000000*s^6*p^7+6888161280000000*s^8*p^6+369008640000000*s^4*p^8+
41000960000000*s^2*p^9+524812288000000*s^18*p^3+472331059200000*s^14*p^5+
118082764800000*s^10*p^7+8200192000000*s^6*p^9+1230028800000*s^4*p^10+
2460057600000*s^2*p^10+111820800000*s^2*p^11+374865920000000000*s^14+
84344832000000000*s^16+14994636800000000*s^18+2099249152000000*s^20+
29286400000000*p^9+111820800000*p^11+2050048000000*p^10+4659200000*p^12+
229008998400000*s^22+19084083200000*s^24+114504499200000*s^22*p+3072000*p^14+
143360000*p^13+40960*p^15+256*p^16+131203072*s^12*p^10+374865920*s^14*p^9+
328007680000*s^6*p^10+8945664000*s^6*p^11+47233105920000*s^16*p^5+590413824000
*s^12*p^8+1118208000*s^4*p^12+44728320000*s^4*p^11+3727360000*s^2*p^12+
196804608000*p^9*s^10+3148873728000*s^18*p^5+33737932800*s^14*p^8+67475865600*
s^16*p^7+2361655296000*s^16*p^6+894566400*p^11*s^8+41984983040000*s^20*p^3+
5904138240000*s^10*p^8+104962457600*s^18*p^6+3148873728000*s^20*p^4+
1640038400000*p^9*s^8+13120307200*p^9*s^12+15744368640000*s^12*p^7+
52481228800000*s^18*p^4+49201152000*p^10*s^8+31488737280000*s^14*p^6+
1349517312000*s^14*p^7+3936092160*p^10*s^10+86016000*s^2*p^13+17203200*s^4*p^
13+149094400*s^6*p^12+1228800*s^2*p^14+122880*s^4*p^14+1146880*s^6*p^13+8192*s
^2*p^15+843448320*s^16*p^8+7454720*s^8*p^12+35782656*s^10*p^11+503316480*s^28*
p^2+1908408320*s^24*p^4+2560000000000000000+2290089984*s^22*p^5+134217728*s^30
*p+2099249152*s^20*p^6+1499463680*s^18*p^7+1174405120*s^26*p^3)*T^8+(
365445120000000000000*p-2099249152*s^16*p^9+495370240000000000000*s^2-\
269652810792960*s^26-820875624448*s^30-17673253552128*s^28-488100618829824*s^
22*p^3-3823488435486720*s^22*p^2-31774235164672*s^20*p^5-15141605212160*s^26*p
^2-34893337722880*s^22*p^4-27664287006720*s^24*p^3-288096373440512*s^24*p^2-\
5147249868800*s^28*p-1494726465290240*s^24*p-104499507101696*s^26*p+3072*p^17+
500826112000000000000*s^4+817037312000000000000*s^2*p+631575347200000000000*s^
2*p^2+152974131200000000000*p^3+299081728000000000000*p^2-24092082176*s^32+
574511185920000000000*s^4*p^2+259960995840000000000*s^4*p^3+
395572674560000000000*s^6*p+277345402880000000000*s^6*p^2+
101704744960000000000*s^2*p^4+303725936640000000000*s^2*p^3+
785475174400000000000*s^4*p+79198945280000000000*s^8*p+59106983936000000000*s^
8*p^2+119299375104000000000*s^6*p^3-30410486579200000000*s^10*p+
261069209600000000000*s^6+54767534080000000000*p^4+46627553280000000000*s^8-\
31049803366400000000*s^12-32490651648000000000*s^10+14565031936000000000*p^5+
61213261824000000*p^8+478844354560000000*p^7+2979427942400000000*p^6+
81384669184000000000*s^4*p^4+25145068748800000000*s^2*p^5+4748075171840000000*
s^2*p^6-630089632972800000*s^12*p^4+35182103756800000000*s^6*p^4-\
11800404295680000000*s^10*p^2+3243700748288000000*s^4*p^6+26083170713600000000
*s^8*p^3+7664227450880000000*s^8*p^4+7526595428352000000*s^6*p^5+
18672821207040000000*s^4*p^5+698497040384000000*s^2*p^7-13415401652224000000*s
^14*p-31089879941120000000*s^12*p-2222055227392000000*s^10*p^3-\
13938489556992000000*s^12*p^2+1592779053465600000*s^8*p^5+434420868710400000*s
^4*p^7-3677254739558400000*s^12*p^3-5627172303667200000*s^14*p^2-\
3845404596633600000*s^16*p+1204818129715200000*s^6*p^6-99110800588800000*s^10*
p^4+50822821969920000*s^10*p^5-1385864311603200000*s^14*p^3-\
1455724324454400000*s^16*p^2-808630773350400000*s^18*p+80906374348800000*s^2*p
^8+3659909693440000*s^4*p^9+13634623242240000*s^6*p^8-221491778027520000*s^14*
p^4-269942448455680000*s^18*p^2+14007764779008000*s^10*p^6-129347335749632000*
s^20*p-319421750968320000*s^16*p^3-72827151581184000*s^12*p^5+
27222013378560000*s^8*p^7+2277422923776000*s^8*p^8-44723453558784000*s^16*p^4-\
37182740679884800*s^20*p^2-5680253317939200*s^12*p^6+146625055948800000*s^6*p^
7+241794141388800000*s^8*p^6+45225698918400000*s^4*p^8+7403133337600000*s^2*p^
9-51230076305408000*s^18*p^3-23938997629747200*s^14*p^5+1918923649843200*s^10*
p^7+964211376128000*s^6*p^9+228355666739200*s^4*p^10+533356888064000*s^2*p^10+
29936366387200*s^2*p^11-14280892088320000000*s^14-4489694150656000000*s^16-\
1054962666700800000*s^18-192075299553280000*s^20+6259792281600000*p^9+
33319616512000*p^11+512078561280000*p^10+1703328972800*p^12-27487186714624000*
s^22-3091926823731200*s^24-15910323827507200*s^22*p+1956241408*p^14+
66976645120*p^13+39993344*p^15+510976*p^16+3280076800*s^12*p^10-48432676864*s^
14*p^9+51051771330560*s^6*p^10+1962654826496*s^6*p^11-4137997943439360*s^16*p^
5-8149285208064*s^12*p^8+373553037312*s^4*p^12+10788112957440*s^4*p^11+
1283300229120*s^2*p^12+9537938522112*p^9*s^10-452816439083008*s^18*p^5-\
2735021752320*s^14*p^8-9779502120960*s^16*p^7-252545970733056*s^16*p^6+
183684300800*p^11*s^8-5911821491896320*s^20*p^3+166449465262080*s^10*p^8-\
21044972748800*s^18*p^6-561137695326208*s^20*p^4+140046159052800*p^9*s^8-\
57729351680*p^9*s^12-286673464197120*s^12*p^7-6041009284710400*s^18*p^4+
6159853027328*p^10*s^8-1765195634442240*s^14*p^6-87182417068032*s^14*p^7+
352542654464*p^10*s^10+40616525824*s^2*p^13+8950251520*s^4*p^13+51795394560*s^
6*p^12+895098880*s^2*p^14+132685824*s^4*p^14+839974912*s^6*p^13+12271616*s^2*p
^15-217272287232*s^16*p^8+3330768896*s^8*p^12+7657488384*s^10*p^11-335544320*s
^34+71565312*s^12*p^11-498383978496*s^28*p^2+6316032*s^6*p^14+917504*s^4*p^15+
210124800000000000000+27754496*s^8*p^13-2348810240*s^32*p+74547200*s^10*p^12+
78848*s^2*p^16-1322908647424*s^24*p^4-25190989824*s^24*p^5-16039018496*s^28*p^
3-20801650688*s^22*p^6-1323672010752*s^22*p^5-7751073792*s^30*p^2-159719096320
*s^30*p-356122624*s^14*p^10-13195280384*s^20*p^7-992944848896*s^20*p^6-\
6297747456*s^18*p^8-553601990656*s^18*p^7-23311941632*s^26*p^4-971937677312*s^
26*p^3)*T^7-70318680566840392*s^2*p^16+73036920387729016717312*s^24*p^4+
10836155757649868750848*s^24*p^5+192498072199168*s^32*p^7-6267650375680*s^38*p
^4-1084241477632*s^42*p^2-2085544656896*s^40*p^3+167915814912*s^44*p+
12725381680031465472*s^32*p^3+788582391808*s^36*p^6-41602613248*s^38*p^5+
3840956019828155482112*s^28*p^3-1472717968104*p^17*s^10-2635165407768*s^2*p^19
+27472298483256*p^19+688436439046*p^20+725436*p^22*s^4+18859590*p^20*s^8-\
2945125756726008*p^17*s^2-2815413649751160*p^16*s^6+1430285793328104*p^17*s^4-\
49251973235968*s^14*p^14+10957792596054784*s^18*p^12+2905125261564800*s^16*p^
13+18388365509525504*s^36*p^2-3142723755311104*s^36*p+2953678830070859776*s^22
*p^9+60797865318249046016*s^22*p^8+911851557702278250496*s^22*p^7+
10119375417520523313152*s^22*p^6+83273278820768130203648*s^22*p^5-\
116865249174093824*s^36-630862680*p^20*s^6+40335383609278464*s^34*p^4+
5319581243801600*s^36*p^3+179817084*p^22+180394455936*s^22*p^13-\
2517706917543936*s^38*p^2-129156408*p^19*s^10+151893864*p^21*s^4-29160*p^23*s^
2-3614328*p^21*s^6-6795576*p^22*s^2+1568808*p^23+6561*p^24+
1160205853327525511168*s^24*p^6+5033381194665297920*s^24*p^8+
90157100879681257472*s^24*p^7+496563560896*s^24*p^12-52142770224*s^6*p^19-\
2718200905136*s^6*p^18+30811128824576*s^22*p^12+951194577968*s^4*p^19-\
1828997893769152*p^15*s^10+15116673508*s^4*p^20+3630539306429972480*s^30*p^5+
37554379754154754048*s^30*p^4+256387108981059878912*s^30*p^3+
1114895463455647596544*s^30*p^2+2803791306662791348224*s^30*p+1270452295965382
*s^8*p^16+225537793419555868672*s^14*p^10+11244916823168*s^20*p^13-37275697152
*s^42*p^3+116785152*s^44*p^2+32030223587922376704*s^20*p^9+
6972899674571243061248*s^20*p^7+544955727825780281344*s^20*p^8+
67552066717295190425600*s^20*p^6+3097541060299871232000*s^18*p^8+
35049540718724996251648*s^18*p^7+209552852494283622400*s^18*p^9+
93609080702200512512*s^26*p^6+1016252133161248882688*s^26*p^5+
7786799749142048669696*s^26*p^4+41339623055559814807552*s^26*p^3:


## poly(ha*IA+hb*IB+hc*IC)

hamIAT:=46656*p-142720*s^2*p-26080*s^2*p^2-291744*s^2+70896*s^4+576*p^3+7776
*p^2-104128*s^6+16*p^4-41472*T^2+17136*s^8+3168*s^4*p^2+128*s^4*p^3-41984*s^6*
p-5664*s^6*p^2-64*s^2*p^4-2112*s^2*p^3+25984*s^4*p+4096*T^4+16*s^12-928*s^10+
4672*s^8*p+320*s^8*p^2-256*s^6*p^3-128*s^10*p+5760*s^4*T^2*p+2048*T^4*p+T^4*p^
4+32*T^4*p^3+384*T^4*p^2-3464*T^2*p^2-19584*T^2*p-8*T^2*p^4-272*T^2*p^3-58880*
s^2*T^2-512*s^6*T^2+14848*s^4*T^2+32*s^4*T^2*p^3+744*s^4*T^2*p^2-496*s^2*T^2*p
^3-30080*s^2*T^2*p-16*s^2*T^2*p^4-5784*s^2*T^2*p^2-128*s^6*T^2*p-8*s^6*T^2*p^2
+104976-262144*s^2*T-2048*T*p^3*s^2-64*T*p^4*s^2-131072*T*p*s^2-24576*T*p^2*s^
2:

## poly(ha*ma+hb*mb+hc*mc)
hammaT := 9540608*T^4*s^8*p^3+84934656*s^4*T^6*p+5034541056*s^4*T^4*p+151072*s
^6*T^2*p^7-576*T^4*s^10*p^5-225456*s^2*T^4*p^7+6100376576*s^6*T^2*p^3-1760048*
s^4*T^2*p^7-64*s^2*T^2*p^10+2116448256*s^4*T^4*p^2+430080*T^2*s^16*p+156991488
*T^2*s^12*p+96402615118848*p-15360*s^6*T^6*p^4-8977664*s^2*T^2*p^7-68087808*s^
6*T^4*p^3-220160*T^2*s^14*p^3+1190155742208*s^2*p+1068936175872*s^2*p^2-6384*s
^2*T^4*p^8-983040*s^6*T^6*p^2+8064*T^2*s^12*p^5-908328960*s^6*T^4*p-12*s^2*T^6
*p^8+898464*T^4*s^8*p^4+396718580736*s^2-9542741663232*s^4+21819521940480*p^3+
58912709239296*p^2+4630640*s^6*T^2*p^6-1816601472*s^2*T^2*p^5+222*s^4*T^4*p^8-\
3145728*s^6*T^6*p+48*s^4*T^6*p^7+2148*s^6*T^2*p^8-331968*s^2*T^2*p^8-18310144*
T^2*s^10*p^3-100481536*T^2*s^10*p^2+76093344*s^4*T^4*p^4-163840*s^6*T^6*p^3-\
3940722304*s^4*T^2*p^4-2266166784*T^2*s^8*p^2-432*s^6*T^4*p^7-11484979200*s^2*
T^4*p^2-118640*T^2*s^8*p^6+14880*s^4*T^4*p^7-16*s^6*T^6*p^6+3072*T^4*s^12*p^3-\
531340608*s^2*T^4*p^4-109117440*s^2*T^6*p^2+435888*s^4*T^4*p^6-6607331328*T^2*
s^8*p-24816*s^6*T^4*p^6-2605056*T^2*s^14*p^2+2672*s^4*T^6*p^6+96*T^4*s^12*p^4-\
800*s^2*T^6*p^7-3085273088*s^2*T^4*p^3-23280*s^2*T^6*p^6+146872341504*s^6+
5454880485120*p^4+969756530688*p^5+831409920*p^8+11972302848*p^7+125709179904*
p^6+6347497291776*T^2+458779832064*s^8-5461491453696*s^4*p^2-1641238640640*s^4
*p^3+75934319616*s^6*p-307556352*s^6*p^2+143123438592*s^2*p^4+497530812672*s^2
*p^3-10764370050048*s^4*p-323496553248*s^4*p^4+27512110080*s^2*p^5+3660443136*
s^2*p^6+208971104256*T^4+3057647616*T^6-9122227200*s^12+16777216*T^8-\
23543986176*s^10+998393856*s^14+38162176*s^16-12086272*s^18+811520*s^20+
41057280*p^9+27648*p^11+1368576*p^10+256*p^12+72301961339136+1130496*T^2*s^16-\
16384*T^2*s^18+247595008*T^2*s^12-27000832*T^2*s^14-8206516224*T^2*s^8-\
346193920*T^2*s^10+423952496640*s^8*p+171201678336*s^8*p^2-9586750464*s^6*p^3-\
29136096*s^12*p^4-3298979904*s^6*p^4-4757607936*s^10*p^2-4096731872*s^4*p^6+
39457689600*s^8*p^3+5676445472*s^8*p^4-16456992768*s^10*p-568960832*s^6*p^5-\
43698343104*s^4*p^5+340028928*s^2*p^7+567838720*s^14*p-6637025280*s^12*p-\
724249088*s^10*p^3-2007023104*s^12*p^2+521929600*s^8*p^5-263195264*s^4*p^7-\
322856960*s^12*p^3+128055296*s^14*p^2+22993920*s^16*p-58161648*s^6*p^6-\
60419968*s^10*p^4-2502528*s^10*p^5+14289920*s^14*p^3+5040640*s^16*p^2-4711424*
s^18*p+21731328*s^2*p^8-276672*s^4*p^9-123536*s^6*p^8+787392*s^14*p^4-611072*s
^18*p^2-28688*s^10*p^6+209920*s^20*p+480256*s^16*p^3-1398464*s^12*p^5+980640*s
^8*p^7+14025*s^8*p^8+16864*s^16*p^4+13568*s^20*p^2-27888*s^12*p^6-3582544*s^6*
p^7+29950672*s^8*p^6-11089120*s^4*p^8+913408*s^2*p^9-26368*s^18*p^3+17088*s^14
*p^5+688*s^10*p^7-1840*s^6*p^9-3104*s^4*p^10+22784*s^2*p^10+256*s^2*p^11+
318848*T^2*s^12*p^4-6976*T^2*s^14*p^4-386304*s^2*T^6*p^5-3998720*s^2*T^6*p^4-\
26443776*s^2*T^6*p^3-179238666240*s^4*T^2*p-23887872000*s^2*T^4+240779264*s^8*
T^4+9699072*T^6*p^5+80698368*T^6*p^4+1594294272*T^6*p^2+447447040*T^6*p^3+
3312451584*T^6*p+16*T^6*p^9+28672*T^8*p^5+1792*T^8*p^6+64*T^8*p^7+T^8*p^8+
16777216*T^8*p+7340032*T^8*p^2+1835008*T^8*p^3+286720*T^8*p^4+1200*T^6*p^8+
39984*T^6*p^7+776848*T^6*p^6+110037408*T^4*p^6+319392*T^4*p^8+7319424*T^4*p^7+
1133932608*T^4*p^5+243799621632*T^4*p+8111682144*T^4*p^4+39775546368*T^4*p^3+
127946428416*T^4*p^2+55447483392*T^2*p^5+4507163875584*T^2*p^2+7934371614720*T
^2*p+348829369344*T^2*p^4+1535855986944*T^2*p^3+96*T^4*p^10+8256*T^4*p^9+256*T
^2*p^11+1094656*T^2*p^9+24832*T^2*p^10+6294081024*T^2*p^6+28947456*T^2*p^8+
510230016*T^2*p^7-531134889984*s^2*T^2+70067552256*s^6*T^2-1058537472*s^6*T^4+
96468992*s^4*T^6-171228266496*s^4*T^2+5234098176*s^4*T^4-264241152*s^2*T^6-\
4194304*s^6*T^6-18087936*T^4*s^10+393216*T^4*s^12-768*s^6*T^6*p^5-35409296*s^4
*T^2*p^6-50992*s^4*T^2*p^8-656*s^4*T^2*p^9-22610877440*s^4*T^2*p^3-80*s^2*T^4*
p^9-457638272*s^4*T^2*p^5-83366240256*s^4*T^2*p^2+507884544*s^4*T^4*p^3+
7288704*s^4*T^4*p^5+32047104*s^4*T^6*p^2+6717440*s^4*T^6*p^3+63744*s^4*T^6*p^5
+844800*s^4*T^6*p^4-155608768*s^2*T^2*p^6-7040*s^2*T^2*p^9-78685903872*s^2*T^2
*p^3-573944942592*s^2*T^2*p-14520824640*s^2*T^2*p^4-277171911936*s^2*T^2*p^2-\
60823104*s^2*T^4*p^5-24875237376*s^2*T^4*p-4626704*s^2*T^4*p^6-256901120*s^2*T
^6*p+65086193664*s^6*T^2*p+878997312*s^6*T^2*p^4-333791232*s^6*T^4*p^2+
80826880*s^6*T^2*p^5+26391656448*s^6*T^2*p^2-8325504*s^6*T^4*p^4-610176*s^6*T^
4*p^5-2875392*T^4*s^10*p^2+56979456*T^4*s^8*p^2+181469184*T^4*s^8*p+36864*T^4*
s^12*p^2-362496*T^4*s^10*p^3+196608*T^4*s^12*p-11403264*T^4*s^10*p-22848*T^4*s
^10*p^4+45120*T^4*s^8*p^5+944*T^4*s^8*p^6-13697024*T^2*s^14*p-290889728*T^2*s^
10*p-48282368*T^2*s^8*p^4-428792320*T^2*s^8*p^3-256*T^2*s^18*p^2-4096*T^2*s^18
*p+54528*T^2*s^16*p^2-99968*T^2*s^10*p^5-1859776*T^2*s^10*p^4+5039104*T^2*s^12
*p^3-3230208*T^2*s^8*p^5+39790592*T^2*s^12*p^2-1840*T^2*s^8*p^7+2304*T^2*s^16*
p^3-2224*T^2*s^10*p^6-23552*s^22+256*s^24-3072*s^22*p:

## poly(HA*ma+HB*mb+HC*mc)
HAmmaT := 10158317568*p+14041589760*s^2*p+6448076928*s^2*p^2+13598171136*s^2+
5273330688*s^4+1657314432*p^3+5331101184*p^2-45895680*s^6+337986756*p^4-\
13953024*s^8+9216*s^12+36864*s^10+1939303296*s^4*p^2+446527872*s^4*p^3+
31629312*s^6*p+33677568*s^6*p^2+298020072*s^2*p^4+1728367488*s^2*p^3+
4827285504*s^4*p-11108352*s^8*p-3317504*s^8*p^2+10691840*s^6*p^3-67584*s^10*p+
64443708*s^4*p^4+34281992*s^2*p^5+2630936*s^2*p^6+4*s^12*p^4+1707184*s^6*p^4-\
45440*s^10*p^2+346448*s^4*p^6+47247192*p^5+13308*p^8+304976*p^7+4584892*p^6+64
*T^8+344*p^9+4*p^10-483968*s^8*p^3-35972*s^8*p^4+150416*s^6*p^5+5968880*s^4*p^
5+129896*s^2*p^7+6144*s^12*p-9344*s^10*p^3+1408*s^12*p^2-1224*s^8*p^5+11520*s^
4*p^7+128*s^12*p^3+7016*s^6*p^6-792*s^10*p^4-24*s^10*p^5+3744*s^2*p^8+136*s^6*
p^7-12*s^8*p^6+168*s^4*p^8+48*s^2*p^9+8707129344+(15349824+64*s^8-64000*s^2*p^
3+1344*s^4*p^3+40292*p^4+3031488*p^2-1280*s^6*p+465472*p^3-4711680*s^2+255360*
s^4+36*s^4*p^4+10554624*p+112384*s^4*p-64*s^6*p^2+18624*s^4*p^2+36*p^6-586304*
s^2*p^2-3432*s^2*p^4-2645760*s^2*p+1864*p^5-72*s^2*p^5-5376*s^6)*T^4+(
1128577536*p+563461632*s^2*p+215382624*s^2*p^2+646534656*s^2-62078976*s^4+
138082720*p^3+516045600*p^2+840704*s^6+23829320*p^4+88064*s^8-2560*s^10-\
4794816*s^4*p^2-4160*s^4*p^3-232448*s^6*p-220224*s^6*p^2+6510320*s^2*p^4+
47234176*s^2*p^3-30409728*s^4*p+39424*s^8*p+6304*s^8*p^2-48000*s^6*p^3-512*s^
10*p+87248*s^4*p^4+578432*s^2*p^5+32404*s^2*p^6-4752*s^6*p^4-32*s^10*p^2+588*s
^4*p^6+2750496*p^5+308*p^8+10572*p^7+212340*p^6+4*p^9+416*s^8*p^3+8*s^8*p^4-\
224*s^6*p^5+11072*s^4*p^5+1048*s^2*p^7+12*s^4*p^7-4*s^6*p^6+15*s^2*p^8+
1100335104)*T^2+(65664+22272*p-96*s^2*p^2+2528*p^2-1792*s^2*p+128*s^4-6912*s^2
+96*p^3)*T^6:
## poly(HA*IA+HB*IB+HC*IC)
HAmIAT := 50054823936*p-60121153536*s^2*p-32766427136*s^2*p^2-49627004928*s^2+
15820914688*s^4+7867072512*p^3+25798115328*p^2-973078528*s^6+1571872768*p^4+
16777216*s^8+11224481792*s^4*p^2+3771203584*s^4*p^3-1107296256*s^6*p-560463872
*s^6*p^2-2237521920*s^2*p^4-10575282176*s^2*p^3+19839057920*s^4*p+16777216*s^8
*p+7340032*s^8*p^2-165543936*s^6*p^3+832786432*s^4*p^4-324175872*s^2*p^5-\
32560512*s^2*p^6-31432704*s^6*p^4+13291264*s^4*p^6+215009280*p^5+56289*p^8+
1323616*p^7+20389632*p^6+256*T^8+1416*p^9+16*p^10+1835008*s^8*p^3+286720*s^8*p
^4-3977216*s^6*p^5+126226432*s^4*p^5-2238112*s^2*p^7+28672*s^8*p^5+959456*s^4*
p^7-335232*s^6*p^6-100732*s^2*p^8+1272*s^4*p^9-572*s^6*p^8+64*s^8*p^7+s^8*p^8-\
18144*s^6*p^7+1792*s^8*p^6+45414*s^4*p^8-2680*s^2*p^9-8*s^6*p^9+16*s^4*p^10-32
*s^2*p^10+43637538816+(-272896*s^2*p^3+27947008*p^2+157679616+96*s^4*p^4-16192
*s^2*p^4+102924288*p+4041216*p^3-384*s^2*p^5+3072*s^4*p^3-16384000*s^2+14208*p
^5+196608*s^4*p-2299904*s^2*p^2+256*p^6+36864*s^4*p^2+393216*s^4-9699328*s^2*p
+328288*p^4)*T^4+(-4808245248*p-2409103360*s^2*p-1083310080*s^2*p^2-2294284288
*s^2+205520896*s^4-421969920*p^3-1886191616*p^2-4194304*s^6-58882048*p^4+
69140480*s^4*p^2+14401536*s^4*p^3-3145728*s^6*p-983040*s^6*p^2-42487808*s^2*p^
4-273457152*s^2*p^3+182976512*s^4*p-163840*s^6*p^3+1788928*s^4*p^4-4168192*s^2
*p^5-252464*s^2*p^6-15360*s^6*p^4+5456*s^4*p^6-5247872*p^5-128*p^8-9248*p^7-\
291728*p^6-768*s^6*p^5+132736*s^4*p^5-8640*s^2*p^7+96*s^4*p^7-16*s^6*p^6-128*s
^2*p^8-5351931904)*T^2+(393216+129024*p-4096*s^2*p-16384*s^2+14080*p^2+512*p^3
-256*s^2*p^2)*T^6:


## poly(wb*wc/rb/rc+wc*wa/rc/ra+wa*wb/ra/rb)

wbmwcdrbdrcT := 9467330560*p-463290368*s^2*p-133800960*s^2*p^2-666435584*s^2+
11927552*s^4+832442368*p^3+3716251648*p^2-65536*s^6+116375552*p^4+10396672*p^5
+256*p^8+18432*p^7+579584*p^6+1005568*s^4*p^2+78848*s^4*p^3-16384*s^6*p-1024*s
^6*p^2-1768448*s^2*p^4-20544512*s^2*p^3+5668864*s^4*p+2304*s^4*p^4-80896*s^2*p
^5-1536*s^2*p^6+10538188800+(-939648*s^2*p^2-128*s^2*p^5-104512*s^2*p^3-\
13295360*p-41728*p^4-5792*s^2*p^4-7505920*s^2+384*s^6*p^2-128*s^4*p^4-277760*s
^4*p-550912*s^4-51712*s^4*p^2+6400*s^6*p-20428800-4224*s^4*p^3-32*p^6-3595008*
p^2+26624*s^6-4207872*s^2*p-1792*p^5-517056*p^3)*T^2+(-18432*p^3-458752*s^2*p-\
247808*p^2-53248*s^2*p^2-32768*s^4*p-3276800-2048*s^4*p^2-1474560*p-131072*s^4
-1310720*s^2-512*p^4-2048*s^2*p^3)*T+(10000+8000*s^2+2400*s^4+320*s^6+16*s^8+p
^4+2400*s^2*p+4000*p+600*p^2+40*p^3+240*s^2*p^2+480*s^4*p+8*s^2*p^3+24*s^4*p^2
+32*s^6*p)*T^4:


## poly(HA/ma+HB/mb+HC/mc)
HAdmaT:=742425852125380608*p+13545807896264048640*s^2*p+10009324235575001088
*s^2*p^2+285659136*T^6*s^18*p-77027328*T^6*s^14*p^3-1372121856*T^6*s^16*p^2-\
38115681408*T^6*s^10*p^4-8979351552*T^6*s^10*p^5-2067296256*T^6*s^16*p-\
389348425728*T^6*s^14+143257683456*T^6*s^12*p^3-26595039744*T^6*s^14*p^2+
8547045218501787648*s^2+41803752162579185664*s^4+322835349200044032*p^3+
620799654141886464*p^2+835616798208*T^6*s^12*p^2-423205378560*T^6*s^8*p^5+
1835108130816*T^6*s^12*p+586227041280*T^6*s^10*p^3-200640208896*T^6*s^14*p-\
4956899535360*T^6*s^8*p^4+49311859580928*T^6*s^10*p+9112806996480*T^6*s^10*p^2
-38182257031680*T^6*s^8*p^3-187287056782848*T^6*s^8*p^2+11963759616*T^6*s^12*p
^4+98601467609088*T^6*s^10-491469078528*T^6*s^12-532194741116928*T^6*s^8*p-\
668578377867264*T^6*s^8-332234895360*T^2*s^14*p^4+4072669184*T^2*s^20-35651584
*T^2*s^22+2396176515072*T^2*s^16-173264601088*T^2*s^18-3193988123197440*T^2*s^
12+61375481118720*T^2*s^14-524201156507860992*T^2*s^8+58620049014915072*T^2*s^
10-13140*s^12*p^10+231120*T^6*s^14*p^6-400896*T^8*s^20-80064*T^6*s^18*p^4+
26352*T^6*s^12*p^7+9216*T^8*s^22-120312*T^6*p^9*s^8+256*T^8*s^24-239220*T^6*s^
10*p^8+25344*T^6*s^20*p^3+6912*T^6*s^16*p^5+12830976*T^6*s^14*p^5-19589760*T^6
*s^10*p^7-23600734560*T^6*s^8*p^6-1051136*T^6*s^18*p^3-135168*T^6*s^22*p+
777984*T^6*s^20*p^2+8420016*T^6*s^12*p^6-15701400*T^6*s^8*p^8-5061888*T^6*s^16
*p^4-819209952*T^6*s^8*p^7-153504000*T^6*s^16*p^3+492583680*T^6*s^12*p^5-\
245760*T^6*s^22+798720*T^6*s^20*p-619291296*T^6*s^10*p^6+8192*T^6*s^24+
201182976*T^6*s^14*p^4+9561120768*T^6*s^16+22019328*T^6*s^18*p^2-16515072*T^6*
s^20+529514496*T^6*s^18+11536722432*T^8*s^10*p^3-19580963328*T^8*s^12*p^2-\
78565718016*T^8*s^12*p+7860602880*T^8*s^14+1088391168*T^8*s^14*p+258100992*T^8
*s^16+103975998624*T^8*s^8*p^4-653155633152*T^8*s^10*p+782553249792*T^8*s^8*p^
3-14183424*T^8*s^18-62402400*T^8*s^12*p^4-53603265024*T^8*s^10*p^2+
9875698661376*T^8*s^8*p+3675799305216*T^8*s^8*p^2+11654356578048*T^8*s^8-\
1725825595392*T^8*s^10-2304*T^6*s^22*p^2-84551869440*T^8*s^12-42048*T^8*s^14*p
^5+213264*T^8*s^10*p^7+465003504*T^8*s^8*p^6+5888*T^8*s^18*p^3+100464*T^8*s^12
*p^6-3072*T^8*s^22*p+9984*T^8*s^20*p^2+182529*T^8*s^8*p^8-52128*T^8*s^16*p^4+
1539648*T^8*s^12*p^5+13956192*T^8*s^8*p^7-857088*T^8*s^16*p^3-175104*T^8*s^20*
p+946944*T^8*s^18*p^2+12133584*T^8*s^10*p^6-4269888*T^8*s^14*p^4+1244160*T^8*s
^18*p-87505920*T^8*s^14*p^3+20777472*T^8*s^16*p^2+2952111744*T^8*s^10*p^4+
274306176*T^8*s^10*p^5+202300416*T^8*s^16*p-452376576*T^8*s^14*p^2-1934917632*
T^8*s^12*p^3+8813784960*T^8*s^8*p^5+37083803455034228736*s^4*p^2+
14627680484135141376*s^4*p^3-26253780951012212736*s^6*p-14822230589662298112*s
^6*p^2+1445930349594624000*s^2*p^4+4730886273487601664*s^8*p+
4574342406296567808*s^2*p^3+57807757682084413440*s^4*p-21385025199752085504*s^
6+116861703486345216*p^4+4449491207998930944*s^8-507836424662286336*s^10+
35112859239186432*s^12+2284195534759526400*s^8*p^2-5093949175640358912*s^6*p^3
+139443864248320*s^12*p^4+3963617487769522176*s^4*p^4-1188525935900786688*s^6*
p^4-179794430980521984*s^10*p^2+115178083673333760*s^4*p^6+661365589428928512*
s^8*p^3+127680002503778304*s^8*p^4-452791416989417472*s^10*p-\
198727159082287104*s^6*p^5+780486415429238784*s^4*p^5+334856339532896256*s^2*p
^5+58692406144828032*s^2*p^6+7928336737833984*s^2*p^7-806155966218240*s^14*p+
25078240037044224*s^12*p-41786918782894080*s^10*p^3+7722429538369536*s^12*p^2+
17276500797419520*s^8*p^5+12940658831922432*s^4*p^7+1332196253368320*s^12*p^3-\
173830060376064*s^14*p^2+13852678815744*s^16*p-24485922308696064*s^6*p^6-\
6277192923611136*s^10*p^4-634037365968896*s^10*p^5-19008280592384*s^14*p^3+
1654175825920*s^16*p^2-93440704512*s^18*p+31223051130820608*p^5+
126544385492001*p^8+1011932165702592*p^7-1514658066333696*s^14+39971985555456*
s^16-591900180480*s^18+3774873600*s^20+6369303193617024*p^6-1800*s^14*p^9+
72301961339136*T^8+489112751315091456*T^2+155615243605180416*T^4+
12497115582408*p^9+832172765689944*s^2*p^8+72805721259048*s^4*p^9-\
154007436970776*s^6*p^8-1037618085888*s^14*p^4-1161297920*s^18*p^2-\
43283975962368*s^10*p^6-125829120*s^20*p+64326598656*s^16*p^3+8870914179072*s^
12*p^5+116782846273152*s^8*p^7+5774955686598*s^8*p^8-1495609344*s^16*p^4-\
6815744*s^20*p^2+313617024000*s^12*p^6-2249669063570432*s^6*p^7+
1675118825023744*s^8*p^6+1112383391756572*s^4*p^8+67868856094216*s^2*p^9+
264241152*s^18*p^3-17717772288*s^14*p^5-1943090316288*s^10*p^7+58808834168*p^
11+971419267036*p^10+2718228294*p^12-278495806992*s^6*p^10-6753117072*s^6*p^11
-135825408*s^16*p^5-7751565298584*s^6*p^9-93461604*s^12*p^8+3120582852*s^4*p^
12+3571656304500*s^4*p^10+127357882992*s^4*p^11+7070378728*s^2*p^12+
4265672261736*s^2*p^10+202903042328*s^2*p^11-685836648*p^9*s^10-133120*s^18*p^
5+154584*s^14*p^8+31680*s^16*p^7-855936*s^16*p^6+51246360*p^11*s^8+131072*s^20
*p^3-52919799192*s^10*p^8-1920*s^18*p^6+4096*s^20*p^4+195685378008*p^9*s^8-\
3007944*p^9*s^12+3887179008*s^12*p^7+3850240*s^18*p^4+4243829124*p^10*s^8+
719072256*s^14*p^6+30409728*s^14*p^7+831528*p^10*s^10+2202076*p^14+92732792*p^
13+32520*p^15+170388728*s^2*p^13+47033064*s^4*p^13-98859096*s^6*p^12+2539224*s
^2*p^14+211252644241920*s^4*T^8+415989582513831936-18433132135317504*s^2*T^4+
24791306302586880*s^8*T^4+329004*s^4*p^14-658008*s^6*p^13+17640*s^2*p^15+225*p
^16+141786486091008*T^6*p^5+718225930540800*T^6*p^4+6513424838168832*T^6*p^2+
2619433608954624*T^6*p^3+9897335152201728*T^6*p+499758336*T^6*p^10+14946048*T^
6*p^11+11393395200*T^6*p^9+1368576*T^8*p^10+256*T^8*p^12+969756530688*T^8*p^5+
125709179904*T^8*p^6+11972302848*T^8*p^7+831409920*T^8*p^8+273152*T^6*p^12+
2304*T^6*p^13+96402615118848*T^8*p+58912709239296*T^8*p^2+21819521940480*T^8*p
^3+5454880485120*T^8*p^4+187011804672*T^6*p^8+2273739849216*T^6*p^7+
20733035457024*T^6*p^6+27648*T^8*p^11+41057280*T^8*p^9+751695060574944*T^4*p^6
+8803434186432*T^4*p^8+92971550981376*T^4*p^7+4630312853350848*T^4*p^5+
235860304367812608*T^4*p+21390227591006304*T^4*p^4+71860766197515264*T^4*p^3+
165964044502259712*T^4*p^2+23444910602373888*T^2*p^5+619878248300445696*T^2*p^
2+806182936033886208*T^2*p+97123621208578560*T^2*p^4+294947693859225600*T^2*p^
3+4704*T^4*p^14+36569312*T^4*p^12+608704*T^4*p^13+34360287936*T^4*p^10+
635087716992*T^4*p^9+1351944448*T^4*p^11+18456125664*T^2*p^11+5643285500224*T^
2*p^9+370852413920*T^2*p^10+4285890894893328*T^2*p^6+66222050209344*T^2*p^8+
604188450661392*T^2*p^7+225*s^16*p^8+265616*T^2*p^14+1936*T^2*p^15+17000256*T^
2*p^13+673326912*T^2*p^12+124391410297344*s^2*T^6*p^5+739200894947136*s^2*T^6*
p^4+203516631917568*s^2*T^8-3519210480715431936*s^2*T^2+8875487267870976*s^2*T
^6*p^2+3119567173056000*s^2*T^6*p^3+87536*s^6*T^8*p^9-15284274744816*s^6*T^4*p
^6-429660288*s^6*T^6*p^7-51378959664*s^6*T^6*p^6+32536365576192*s^6*T^8*p^2+
1114816146624*s^6*T^8*p^4+79312716*s^6*T^6*p^8+7504477258752*s^6*T^8*p^3+
1343751349747580928*s^4*T^2*p+84590850903860736*s^4*T^2*p^4+7341916464*s^6*T^8
*p^6+314006544*s^6*T^8*p^7+3895192*s^6*T^6*p^9+110659400640*s^6*T^8*p^5-\
100474830673920*s^6*T^6*p^3-1193688659939328*s^6*T^6*p+60156*s^6*T^6*p^10-\
1130727009024*s^6*T^6*p^5+1848385597524148224*s^6*T^2-36533930557833216*s^6*T^
4-13578662396160*s^6*T^6*p^4+92846841172992*s^6*T^8+19122840*s^4*T^2*p^12-\
458949477199104*s^6*T^6*p^2+225149097556800*s^4*T^2*p^7+149400*s^4*T^2*p^13+
2182151783014272*s^4*T^2*p^6+17370533992920*s^4*T^2*p^8+989880442840*s^4*T^2*p
^9+40505006864*s^4*T^2*p^10-1107328460*s^4*T^4*p^10-19310792*s^4*T^4*p^11+
1127176784*s^4*T^2*p^11-38258781480*s^4*T^4*p^9+324691605801418752*s^4*T^2*p^3
-153306*s^4*T^4*p^12-985994320*s^2*T^4*p^10-23048398416*s^2*T^4*p^9+
15812159208376320*s^4*T^2*p^5+846612585248882688*s^4*T^2*p^2-43366297105492992
*s^4*T^4*p^3-131333744925775872*s^4*T^4*p^2-1518824672865792*s^4*T^4*p^5-\
240431756244516864*s^4*T^4*p-9638715430605600*s^4*T^4*p^4-173934775896624*s^4*
T^4*p^6-887713452378*s^4*T^4*p^8-14581155023712*s^4*T^4*p^7+192894399216*s^4*T
^6*p^7+2612363533488*s^4*T^6*p^6+2442816*s^4*T^8*p^9+99389024434944*s^4*T^8*p^
2+27022575919104*s^4*T^8*p^3+4812508616544*s^4*T^8*p^4+9990332640*s^4*T^6*p^8+
108794016*s^4*T^8*p^8+216211626501120*s^4*T^8*p+49577715360*s^4*T^8*p^6+
2868690816*s^4*T^8*p^7+345780960*s^4*T^6*p^9+24672*s^4*T^8*p^10+586646618688*s
^4*T^8*p^5+7201392*s^4*T^6*p^10+68400*s^4*T^6*p^11+2760048305904384*s^4*T^6*p^
2+851880365971200*s^4*T^6*p^3+5368395834519552*s^4*T^6*p+4747927974248448*s^4*
T^6+980278434758393856*s^4*T^2-201252338578096128*s^4*T^4+25312577345280*s^4*T
^6*p^5-380971148*s^2*T^2*p^12+175422353495040*s^4*T^6*p^4-42372*s^2*T^2*p^14-\
5900216*s^2*T^2*p^13-120900703470516*s^2*T^2*p^8-1364119956275904*s^2*T^2*p^7-\
411973572076*s^2*T^2*p^10-11770051979963088*s^2*T^2*p^6-28815536*s^2*T^4*p^11-\
15118743760*s^2*T^2*p^11-8154239407160*s^2*T^2*p^9+12053897357082624*s^2*T^6-\
388567625904*s^2*T^4*p^8-4859224153488*s^2*T^4*p^7-1358572954252935168*s^2*T^2
*p^3-515792*s^2*T^4*p^12-4272*s^2*T^4*p^13-77285788102533888*s^2*T^2*p^5-\
5029753092523425792*s^2*T^2*p-380177171736127488*s^2*T^2*p^4-\
3334074777339199488*s^2*T^2*p^2-6323893352515584*s^2*T^4*p^3-16231520331601920
*s^2*T^4*p^2-321610410622656*s^2*T^4*p^5-25461927469744128*s^2*T^4*p-\
1680320788288704*s^2*T^4*p^4+15241320993024*s^2*T^6*p^6+3840*s^2*T^8*p^11+
19187712*s^2*T^8*p^9-45627176401776*s^2*T^4*p^6+546435072*s^2*T^8*p^8+21312*s^
2*T^6*p^12+40806914012928*s^2*T^8*p^3+8683728933888*s^2*T^8*p^4+89629441920*s^
2*T^6*p^8+1369898168832*s^2*T^6*p^7+239221304183808*s^2*T^8*p+127644203351808*
s^2*T^8*p^2+15286360352919552*s^2*T^6*p+130225152*s^2*T^6*p^10+1291376120832*s
^2*T^8*p^5+136925655552*s^2*T^8*p^6+10349793792*s^2*T^8*p^7+2463744*s^2*T^6*p^
11+4162512384*s^2*T^6*p^9+403200*s^2*T^8*p^10+7855056*s^6*T^8*p^8+
82404816307200*s^6*T^8*p+932820*s^6*T^2*p^12+5819623350516*s^6*T^2*p^8+
98773136208576*s^6*T^2*p^7+6900279768*s^6*T^2*p^10+1222122726792960*s^6*T^2*p^
6-1358129327947776*s^6*T^6+118434000*s^6*T^2*p^11+243854887248*s^6*T^2*p^9-\
1853885992*s^6*T^4*p^9-348696*s^6*T^4*p^11+345726149257986048*s^6*T^2*p^3-\
37642152*s^6*T^4*p^10+2104145146270973952*s^6*T^2*p+73509926508638208*s^6*T^2*
p^4-19061034473170944*s^6*T^4*p^2+11104003129798656*s^6*T^2*p^5+
1096292328258502656*s^6*T^2*p^2-39054851539107840*s^6*T^4*p-1105803162005760*s
^6*T^4*p^4-5608588527820800*s^6*T^4*p^3-55011495576*s^6*T^4*p^8-1093271447664*
s^6*T^4*p^7-153419077085184*s^6*T^4*p^5+241254*s^8*p^12+84600*s^10*p^11+
248043170227392*T^4*s^8*p^4+1754946656667648*T^4*s^8*p^3-469433851342848*T^4*s
^10*p^2-510010761024*T^4*s^12*p^4+7974976264335360*T^4*s^8*p^2+
21109864938799104*T^4*s^8*p-10697236918272*T^4*s^12*p^2-55415197937664*T^4*s^
10*p^3+15076734861312*T^4*s^12*p+4716309970944*T^4*s^14*p-1906094668972032*T^4
*s^10*p+235338929280*T^4*s^10*p^5-2121648971904*T^4*s^10*p^4-158766759936*T^4*
s^16*p+1314964647936*T^4*s^14*p^2-3715515463680*T^4*s^12*p^3+23375869709184*T^
4*s^8*p^5-1801420800*T^4*s^18*p-10618324992*T^4*s^16*p^2+151230652416*T^4*s^14
*p^3+6724495104*T^4*s^14*p^4-1282276368*T^4*s^12*p^6+14403584*T^4*s^20*p^2+
240300768*T^4*s^16*p^4+1459219812*T^4*s^8*p^8+60025667520*T^4*s^8*p^7-\
35931042816*T^4*s^12*p^5+1603630080*T^4*s^16*p^3+135823360*T^4*s^20*p+
35489306160*T^4*s^10*p^6-850425856*T^4*s^18*p^2+1472021856144*T^4*s^8*p^6-\
1343488*T^4*s^22*p-3117709561430016*T^4*s^10+10792128*T^4*s^16*p^5+1998553488*
T^4*s^10*p^7-55113216*T^4*s^14*p^5-85477376*T^4*s^18*p^3+24102*T^4*s^12*p^8-\
47040*T^4*s^18*p^5+573912*T^4*p^9*s^10+168912*T^4*s^16*p^6+54054744*T^4*s^10*p
^8+533504*T^4*s^20*p^3+4704*T^4*s^20*p^4+17196360*T^4*p^9*s^8+6940988288557056
*T^6-3408064*T^4*s^18*p^4-17899872*T^4*s^12*p^7-12877008*T^4*s^14*p^6+42084*T^
4*p^10*s^8-34816*T^4*s^22*p^2-265104*T^4*s^14*p^7-6776624775168*T^2*s^14*p+
43184737320173568*T^2*s^10*p-8381998012419072*T^2*s^8*p^4-51972594392530944*T^
2*s^8*p^3+13563065025626112*T^2*s^10*p^2+5058736831488*T^2*s^12*p^4-\
209207337489727488*T^2*s^8*p^2-495151916472336384*T^2*s^8*p-10621452288*T^2*s^
18*p^2-76989071360*T^2*s^18*p+654610956288*T^2*s^16*p^2-2888650063872*T^2*s^14
*p^3+10155954614784*T^2*s^10*p^5+224847734317056*T^2*s^10*p^4+2441083355136*T^
2*s^16*p-11743611125760*T^2*s^14*p^2+318707761152*T^2*s^12*p^3-912102830590464
*T^2*s^8*p^5-244712217968640*T^2*s^12*p^2+2323252978384896*T^2*s^10*p^3-\
1548825155076096*T^2*s^12*p+112849556078592*T^4*s^12+151496448*T^2*s^16*p^5-\
48455566656*T^2*s^10*p^7-20807067648*T^2*s^14*p^5-619511808*T^2*s^18*p^3-\
67097016409056*T^2*s^8*p^6-524288*T^2*s^22*p+51035362560*T^2*s^12*p^6+39878656
*T^2*s^20*p^2+4755558912*T^2*s^16*p^4-88623871728*T^2*s^8*p^8-3212835868320*T^
2*s^8*p^7+732715388928*T^2*s^12*p^5+78083899392*T^2*s^16*p^3+839385088*T^2*s^
20*p-174170735904*T^2*s^10*p^6-412575399936*T^4*s^16+4372627193856*T^4*s^14-\
32768*T^2*s^22*p^2-13048512*T^2*s^14*p^7-722806656*T^2*s^14*p^6+23587440*T^2*p
^10*s^8-16693248*T^2*s^18*p^4+1936284480*T^2*s^12*p^7+312312*T^2*p^9*s^12-\
778983312*T^2*p^9*s^8+15872*T^2*s^20*p^4-1936*T^2*s^18*p^6-2595148044*T^2*s^10
*p^8+868352*T^2*s^20*p^3+532944*T^2*p^11*s^8+2414160*T^2*s^16*p^6+17424*T^2*s^
16*p^7-94644*T^2*s^14*p^8-251648*T^2*s^18*p^5-61903512*T^2*p^9*s^10+38196312*T
^2*s^12*p^8+242614272*T^4*s^20-548172*T^2*p^10*s^10+5984354304*T^4*s^18-\
8257536*T^4*s^22+65536*T^4*s^24:


## poly(wa+wb+wc):
waT := (2*s^2+p+10)^4*T^4-8*(s^6+3*s^4+42*s^2*p+2*s^2*p^2+
211*s^2+81+p^2+18*p)*(2*s^2+p+10)^2*T^2-64*s^2*(p+8)*(2*s^2
+p+10)^3*T-374688*s^2+46656*p+7776*p^2-171520*s^2*p-29408*s
^2*p^2-160528*s^4+104976-218816*s^6+576*p^3+16*p^4-6560*s^4
*p^2-13584*s^8-256*s^4*p^3-70656*s^6*p-7456*s^6*p^2+96*s^10
-64*s^2*p^4-256*s^6*p^3-3264*s^8*p-192*s^8*p^2+16*s^12-2240
*s^2*p^3-56192*s^4*p:

## poly(1/wa+1/wb+1/wc):
dwaT := 16*s^2*(p+8)^2*T^4-8*(p+8)*(s^2*p+2*p+10*s^2+18)*T^2-
16*(p+8)*(2*s^2+p+10)*T-4*s^4-92*p+88*s^2+s^2*p^2-484-4*p^2
+20*s^2*p:

## poly(wb*wc+wc*wa+wa*wb):
wbmwcT := (2*s^2+p+10)^4*T^4-32*s^2*(p+8)*(s^2*p+2*p+10*s^2+18
)*(2*s^2+p+10)^2*T^2-512*s^4*(p+8)^2*(2*s^2+p+10)^2*T-256*s
^6*(p+8)^2*(4*s^4+92*p-88*s^2-s^2*p^2+484+4*p^2-20*s^2*p):

## poly(1/wb/wc+1/wc/wa+1/wa/wb):
dwbdwcT := 256*s^8*(p+8)^4*T^4-32*s^4*(p+8)^2*(s^6+3*s^4+42*s^2
*p+2*s^2*p^2+211*s^2+81+p^2+18*p)*T^2-32*s^4*(p+8)^2*(2*s^2
+p+10)^2*T+2916*p-23418*s^2+486*p^2-10720*s^2*p-1838*s^2*p^
2-10033*s^4+6561-13676*s^6+36*p^3+p^4-410*s^4*p^2-849*s^8-
16*s^4*p^3-4416*s^6*p-466*s^6*p^2+6*s^10-4*s^2*p^4-16*s^6*p
^3-204*s^8*p-12*s^8*p^2+s^12-140*s^2*p^3-3512*s^4*p:

## poly(a/wa+b/wb+c/wc):
adwaT := 16*s^2*(p+8)^2*T^4-8*(p+8)*(-2*p^2-3*s^2*p-36*p+s^4*p
-28*s^2-162+6*s^4)*T^2-16*s*(p+8)^2*(2*s^2+p+10)*T+s^6*p^2-4
*s^8+108*s^4*p+456*s^4+4*s^2*p^3+105*s^2*p^2+924*s^2*p+2704*
s^2-4*p^3-92*p^2-700*p-1764+20*s^6*p+80*s^6+6*s^4*p^2:

## poly(wa/a+wb/b+wc/c):
wadaT := (2*s^2+p+10)^4*(p+8)^4*s^4*T^4-8*s^2*(p+8)^2*(6561+
2916*p+2709*s^2-3*s^6*p^2-2*s^4*p^3-50*s^6*p-378*s^4*p-48*s
^4*p^2+36*p^3+486*p^2+105*s^2*p^2+922*s^2*p+p^4-966*s^4-198
*s^6-11*s^8+4*s^2*p^3+s^10-2*s^8*p)*(2*s^2+p+10)^2*T^2-64*s
^5*(p+8)^4*(2*s^2+p+10)^3*T+33768672*s^6*p^2+18883328*s^4*p
^3+106718816*s^4*p^2+150208992*s^2*p^2+446357952*s^2*p+
568759968*s^2+612220032*p+178775936*s^6+445446864*s^4+
52907904*p^3+16*s^12*p^4+7348320*p^4+33729824*s^8+120390400
*s^6*p+333623808*s^4*p+653184*p^5+16*p^8+1152*p^7+38784*s^
14-4400*s^16-352*s^18+16*s^20+267552*s^12+238085568*p^2+
28097280*s^2*p^3+19526400*s^8*p+1182656*s^10+36288*p^6+
3155040*s^2*p^4+4526048*s^8*p^2+5047424*s^6*p^3+1994064*s^4
*p^4+423808*s^6*p^4-45408*s^10*p^2+4352*s^4*p^6+524672*s^8*
p^3+30400*s^8*p^4+259200*s^10*p+18944*s^6*p^5+125504*s^4*p^
5+212672*s^2*p^5+7968*s^2*p^6+128*s^2*p^7+18176*s^14*p+
115200*s^12*p-18432*s^10*p^3+17440*s^12*p^2+704*s^8*p^5+64*
s^4*p^7+1024*s^12*p^3+2720*s^14*p^2-896*s^16*p+352*s^6*p^6-
1888*s^10*p^4-64*s^10*p^5+128*s^14*p^3-32*s^16*p^2-64*s^18*
p+688747536:

## poly(wa/ha+wb/hb+wc/hc):
wadhaT := (2*s^2+p+10)^4*T^4+2*(p+8)*(2*p^2-5*s^2*p+39*p-64*s^2
+192)*(2*s^2+p+10)^2*T^2-8*(p+8)^2*(2*s^2+p+10)^3*T-(p+8)^2*
(36*s^2*p^3-4*p^3-9*s^4*p^2-113*p^2+1110*s^2*p^2-288*s^4*p+
11456*s^2*p-1056*p+64*s^6-2112*s^4+39616*s^2-3264):

## poly(ha/wa+hb/wb+hc/wc):
hadwaT := (p+8)^4*T^4-2*(p+8)^2*(p^2+18*p+84+4*s^2)*T^2-8*(p+8)
^2*(2*s^2+p+10)*T+p^4+13200+5040*p+712*p^2-1376*s^2-272*s^2*
p-12*s^2*p^2+44*p^3+16*s^4:

## poly(ha*wa+hb*wb+hc*wc):
hamwaT:=1/256*(2*s^2+p+10)^4*(p+8)^4*T^4-1/8*(p+8)^2*(6561+2916*p+2709*s^2-3*s^6
*p^2-2*s^4*p^3-50*s^6*p-378*s^4*p-48*s^4*p^2+36*p^3+486*p^2+105*s^2*p^2+922*s^
2*p+p^4-966*s^4-198*s^6-11*s^8+4*s^2*p^3+s^10-2*s^8*p)*(2*s^2+p+10)^2*T^2-2*s^
4*(p+8)^4*(2*s^2+p+10)^3*T+35547498*s^2+38263752*p+27897372*s^2*p+27840429*s^4
+3306744*p^3+14880348*p^2+s^20+2424*s^14-22*s^18-275*s^16+2108114*s^8+73916*s^
10+459270*p^4+11173496*s^6+40824*p^5+p^8+9388062*s^2*p^2+16722*s^12+6669926*s^
4*p^2+1180208*s^4*p^3+7524400*s^6*p+2110542*s^6*p^2+197190*s^2*p^4+1756080*s^2
*p^3+20851488*s^4*p+1220400*s^8*p+282878*s^8*p^2+315464*s^6*p^3+16200*s^10*p+
124629*s^4*p^4+13292*s^2*p^5+498*s^2*p^6+s^12*p^4+26488*s^6*p^4-2838*s^10*p^2+
272*s^4*p^6+32792*s^8*p^3+1900*s^8*p^4+1184*s^6*p^5+7844*s^4*p^5+8*s^2*p^7+
1136*s^14*p+7200*s^12*p-1152*s^10*p^3+1090*s^12*p^2+44*s^8*p^5+4*s^4*p^7+64*s^
12*p^3+170*s^14*p^2-56*s^16*p+22*s^6*p^6-118*s^10*p^4-4*s^10*p^5+8*s^14*p^3-2*
s^16*p^2-4*s^18*p+72*p^7+2268*p^6+43046721:

## poly(ra*wa+rb*wb+rc*wc):
ramwaT := (2*s^2+p+10)^4*T^4-8*(6561+486*p^2+4*s^4*p^2+2916*p+
2547*s^2+58*s^4*p+103*s^2*p^2+p^4+4*s^2*p^3+211*s^4+s^6+886
*s^2*p+36*p^3)*(2*s^2+p+10)^2*T^2-64*s^4*(p+8)*(2*s^2+p+10)
^3*T+424816*s^4*p^4+20832*s^6*p^4+534747744*s^2-1152*s^10*p
^2+612220032*p+156389616*s^4+238085568*p^2+143910432*s^2*p^
2+52907904*p^3+7348320*p^4+36288*p^6+653184*p^5+16*p^8+1152
*p^7+384*s^4*p^6+6784*s^8*p^3+256*s^8*p^4-18112*s^10*p+
688747536+18779456*s^6+423683136*s^2*p+108617472*s^4*p+
31479968*s^4*p^2+347376*s^8+4872768*s^4*p^3+11398272*s^6*p+
2778464*s^6*p^2-71072*s^10+3077280*s^2*p^4+339776*s^6*p^3+
257664*s^8*p+64672*s^8*p^2+16*s^12+27164160*s^2*p^3+512*s^6
*p^5+19776*s^4*p^5+209216*s^2*p^5+7904*s^2*p^6+128*s^2*p^7:

## poly(ma+mb+mc):
maT := T^8-6*(-9+s^2-p)*T^6+9*(p^2-20*s^2+18*p-2*s^2*p+81+s^
4)*T^4-(-4*p^3-972*p-2916-12*s^4*p-1566*s^2+4*s^6-15*s^2*p^
2-18*s^4-108*p^2-306*s^2*p)*T^2+81*s^4:

## poly(1/ma+1/mb+1/mc):
dmaT := (4*s^6-12*s^4*p+36*s^4-15*s^2*p^2-360*s^2*p-2052*s^2-
4*p^3-108*p^2-2916-972*p)^4*T^8-144*(81-14*s^2+s^4+18*p-2*s
^2*p+p^2)*(4*s^6-12*s^4*p+36*s^4-15*s^2*p^2-360*s^2*p-2052*
s^2-4*p^3-108*p^2-2916-972*p)^3*T^6+96*(-p-9+7*s^2)*(7*s^6-
27*s^4*p-315*s^4+1314*s^2*p+69*s^2*p^2+6453*s^2-11907*p-
1323*p^2-35721-49*p^3)*(4*s^6-12*s^4*p+36*s^4-15*s^2*p^2-
360*s^2*p-2052*s^2-4*p^3-108*p^2-2916-972*p)^2*T^4-256*(4*s
^6-12*s^4*p+36*s^4-15*s^2*p^2-360*s^2*p-2052*s^2-4*p^3-108*
p^2-2916-972*p)*(20607*s^4*p^4+42869574*p-202144410*s^2-
23954940*s^2*p^2-726*s^10*p+196012791*s^4+11908215*p^2-
110001726*s^2*p+1764180*p^3+147015*p^4+121*p^6+6534*p^5+
64304361-20241900*s^6-2609604*s^2*p^3+79191756*s^4*p+
12014082*s^4*p^2+807111*s^8+811548*s^4*p^3-4969836*s^6*p-
388908*s^6*p^2-13914*s^10-142218*s^2*p^4-9548*s^6*p^3+
100206*s^8*p+4191*s^8*p^2+121*s^12-3102*s^2*p^5)*T^2+2304*(
32805+185652*s^2-28674*s^4+756*s^6+5*s^8+14580*p+56916*s^2*
p-4788*s^4*p-20*s^6*p+2430*p^2+5796*s^2*p^2-186*s^4*p^2+180
*p^3+196*s^2*p^3+5*p^4)^2:

## poly(a*wa+b*wb+c*wc):
amwaT:= -1/1024*(2*s^2+p+10)^4*T^4+1/128*s^2*(p+8)*(5*s^2*p+64*s^2-2*p^2-39*p-\
192)*(2*s^2+p+10)^2*T^2+1/16*s^3*(p+8)^2*(2*s^2+p+10)^3*T+1/64*s^4*(p+8)^2*(36
*s^2*p^3-4*p^3-9*s^4*p^2-113*p^2+1110*s^2*p^2-288*s^4*p+11456*s^2*p-1056*p+64*
s^6-2112*s^4+39616*s^2-3264):

## poly(a*ma+b*mb+c*mc):
ammaT := T^8-2*(s^4-6*s^2-2*s^2*p+81+p^2+18*p)*T^6+(-92*s^2*p
^2-1620*s^2+p^4+76*s^4*p+6*s^4*p^2-4*s^2*p^3+6561-20*s^6+
2916*p+342*s^4-4*s^6*p-684*s^2*p+s^8+486*p^2+36*p^3)*T^4+s^
2*(568*s^2*p^3+4*p^5+3244*p^3+8*s^8+204*s^4*p^2+180*p^4+
29268*p^2+12*s^4*p^3-4*s^6*p^2-96*s^6*p+864*s^4*p+132192*p+
8004*s^2*p^2-448*s^6-144*s^4+15*s^2*p^4+239112+115776*s^2+
49824*s^2*p)*T^2+16*s^4*(-9+s^2-p)^4:

## poly(ma/a+mb/b+mc/c):
madaT := 256*s^8*(p+8)^8*T^8-256*s^6*(p+8)^6*(-4*p^3-108*p^2+3
*s^2*p^2+56*s^2*p-12*s^4*p-972*p-2916+4*s^6-92*s^4+252*s^2)*
T^6+32*s^4*(p+8)^4*(699840*p^3-339336*s^2*p^2+638928*s^4+
4723920*p^2-1578528*s^2*p+58320*p^4+17006112*p-2916000*s^2+
111*s^4*p^4-288*s^10*p-40*s^2*p^5+2592*p^5+48*p^6+29392*s^8-
2208*s^10+48*s^12+50904*s^4*p^2+3888*s^4*p^3-46272*s^6*p-
5496*s^6*p^2-1912*s^2*p^4-216*s^6*p^3+7456*s^8*p+472*s^8*p^2
-36184*s^2*p^3+295104*s^4*p-129216*s^6+25509168)*T^4-16*s^2*
(p+8)^2*(-2857026816*p^3+619463376*s^2*p^2+668860416*s^4-
11019960576*p^2+1723286016*s^2*p-476171136*p^4-24794911296*p
+2074745664*s^2-576*s^16*p-537*s^6*p^6+556*s^10*p^4+3923876*
s^4*p^4-656476*s^6*p^4+171824*s^10*p^2+10124*s^4*p^6+421312*
s^8*p^3+22300*s^8*p^4+798208*s^10*p-29176*s^6*p^5+267532*s^4
*p^5+1221696*s^2*p^5+57904*s^2*p^6+1504*s^2*p^7+27136*s^14*p
-371456*s^12*p+16096*s^10*p^3-47456*s^12*p^2+460*s^8*p^5+164
*s^4*p^7-2016*s^12*p^3+1744*s^14*p^2-52907904*p^5-5184*p^8-
186624*p^7+105472*s^14-4416*s^16+64*s^18-3919104*p^6+
32056704*s^8+1352320*s^10-967168*s^12+181964448*s^4*p^2+
34505504*s^4*p^3-185817600*s^6*p-52361424*s^6*p^2+15649200*s
^2*p^4-7835840*s^6*p^3+17795712*s^8*p+3902400*s^8*p^2+
125574624*s^2*p^3+532935936*s^4*p-273701376*s^6+16*s^2*p^8-
64*p^9-24794911296)*T^2+(233280*p^3+22248*s^2*p^2-561168*s^4
+1574640*p^2+54432*s^2*p+19440*p^4+5668704*p+23328*s^2-99*s^
4*p^4-96*s^10*p+8*s^2*p^5+864*p^5+16*p^6+8432*s^8-736*s^10+
16*s^12-44792*s^4*p^2-3440*s^4*p^3+1984*s^6*p+24*s^6*p^2+280
*s^2*p^4-8*s^6*p^3+2144*s^8*p+136*s^8*p^2+3704*s^2*p^3-
259008*s^4*p+10176*s^6+8503056)^2:

## poly(a/ma+b/mb+c/mc):
admaT := 1/256*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+
2052*s^2+4*p^3+108*p^2+2916+972*p)^4*T^8-1/16*(5832+1944*p+
216*p^2+8*p^3-4536*s^2-960*s^2*p-51*s^2*p^2+312*s^4+24*s^4*p
-8*s^6)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^
2+4*p^3+108*p^2+2916+972*p)^3*T^6+1/8*(45349632*p-97044480*s
^2*p-20960208*s^2*p^2-179718912*s^2+74058624*s^4+12597120*p^
2+1866240*p^3+155520*p^4-9469440*s^6+4839984*s^4*p^2+336256*
s^4*p^3-2739456*s^6*p-261168*s^6*p^2-122224*s^2*p^4-8176*s^6
*p^3+93184*s^8*p+3792*s^8*p^2-2263536*s^2*p^3+30931200*s^4*p
+551808*s^8-14080*s^10+128*s^12+8751*s^4*p^4-768*s^10*p-2640
*s^2*p^5+6912*p^5+128*p^6+68024448)*(-4*s^6+12*s^4*p-36*s^4+
15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^2*T^
4+s^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+
4*p^3+108*p^2+2916+972*p)*(381299705856*p-351483162624*s^2*p
-112022735616*s^2*p^2-472442388480*s^2+164533690368*s^4+
144622495872*p^2+31336968960*p^3+4242741120*p^4-26427949056*
s^6+26340764544*s^4*p^2+3618199296*s^4*p^3-13055385600*s^6*p
-2563702272*s^6*p^2-2104615800*s^2*p^4-249965312*s^6*p^3+
848001024*s^8*p+114989952*s^8*p^2-19826919936*s^2*p^3+
102079346688*s^4*p+2304958464*s^8-113393664*s^10+2990080*s^
12+279002376*s^4*p^4-12090504*s^6*p^4-2111232*s^10*p^2+
195351*s^4*p^6+6788608*s^8*p^3+146616*s^8*p^4-27537408*s^10*
p-231848*s^6*p^5+11449920*s^4*p^5-133985064*s^2*p^5-4736744*
s^2*p^6-71736*s^2*p^7+362496*s^12*p-49920*s^10*p^3+8320*s^12
*p^2+367538688*p^5+8320*p^8+615168*p^7-32768*s^14+19894144*p
^6+439710031872)*T^2+s^4*(73903104+39377664*p+8386416*p^2+
892368*p^3+47440*p^4+1008*p^5-25629696*s^2-10526976*s^2*p-
1615248*s^2*p^2-109696*s^2*p^3-2781*s^2*p^4+3621888*s^4+
1043712*s^4*p+98448*s^4*p^2+3024*s^4*p^3-211968*s^6-32512*s^
6*p-1008*s^6*p^2+4096*s^8)^2:

## poly(ma*wa+mb*wb+mc*wc):
mamwaT := (2*s^2+p+10)^8*T^8-4*(-2916-972*p-2664*s^2-4*s^6*p-7
*s^4*p^2-772*s^2*p-2*s^2*p^3-156*s^4*p-71*s^2*p^2-108*p^2-4
*p^3-800*s^4-24*s^6+4*s^8)*(2*s^2+p+10)^6*T^6+2*(2790*s^6*p
^4+16747*s^4*p^4-216*s^10*p^2+48*s^16-96*s^14*p+17006112*p+
8*s^4*p^6+27946944*s^2+4104648*s^2*p^2-3104*s^10*p+17454528
*s^4+4723920*p^2+16757280*s^2*p+699840*p^3+58320*p^4+48*p^6
+2592*p^5+4160*s^8*p^3+99*s^8*p^4+6393408*s^6+521960*s^2*p^
3+9739488*s^4*p+2209416*s^4*p^2+1076512*s^8+260064*s^4*p^3+
3181152*s^6*p+620944*s^6*p^2-15296*s^10+35912*s^2*p^4+59392
*s^6*p^3+434912*s^8*p+64480*s^8*p^2-16448*s^12+25509168+52*
s^6*p^5+564*s^4*p^5+1240*s^2*p^5-3552*s^12*p+16*s^2*p^6-8*s
^10*p^3-576*s^14-184*s^12*p^2)*(2*s^2+p+10)^4*T^4-4*(-
185391648*s^6*p^4-173127676*s^4*p^4-32*s^4*p^9-392*s^6*p^8+
36000*s^14*p^4+5488*s^18*p^2+811*s^10*p^6-6720*s^20*p+33088
*s^16*p^3+15172*s^12*p^5-1344*s^8*p^7-395717536*s^10*p^2+
5742400*s^16+21934208*s^14*p-24794911296*p-1487588*s^4*p^6-
24794911296-13536865152*s^2-3751107408*s^2*p^2-1509779840*s
^10*p-10633275648*s^4-11019960576*p^2-11031297984*s^2*p-
2857026816*p^3-476171136*p^4-3919104*p^6-52907904*p^5-5184*
p^8-186624*p^7-3121936*s^8*p^5-75580*s^4*p^7+887872*s^12*p^
3+4901888*s^14*p^2+2508992*s^16*p-887375*s^6*p^6-3802384*s^
10*p^4+1904*s^2*p^8-64*p^9+93824*s^18-469491008*s^8*p^3-
49688748*s^8*p^4-19400515200*s^6-663634944*s^2*p^3-
10006514496*s^4*p-4226269392*s^4*p^2-11015449920*s^8-
1056437056*s^4*p^3-16728039360*s^6*p-6318283392*s^6*p^2-
2357025536*s^10-57344112*s^2*p^4-1366696192*s^6*p^3-
8260312704*s^8*p-2646954240*s^8*p^2-89492480*s^12-27392*s^
20+8*s^8*p^8+1020*s^16*p^4-400*s^20*p^2+409*s^12*p^6-192*s^
22*p-113696*s^10*p^5-28054*s^6*p^7+578816*s^14*p^3+423296*s
^16*p^2+39232*s^18*p-105929*s^8*p^6+199980*s^12*p^4-2304*s^
4*p^8+32*s^2*p^9+256*s^18*p^3+932*s^14*p^5+90*s^10*p^7+64*s
^24-16172036*s^6*p^5-1152*s^22-19382228*s^4*p^5-247968*s^2*
p^5-37499520*s^12*p+451024*s^2*p^6+44608*s^2*p^7-53573888*s
^10*p^3+41188096*s^14-2892064*s^12*p^2)*(2*s^2+p+10)^2*T^2+
(-510*s^6*p^4-5031*s^4*p^4-2248*s^10*p^2+16*s^16-32*s^14*p+
5668704*p-3125952*s^2-875880*s^2*p^2-18528*s^10*p-6070464*s
^4+1574640*p^2-2604960*s^2*p+233280*p^3+19440*p^4+16*p^6+
864*p^5-1472*s^8*p^3-31*s^8*p^4-2411328*s^6-153544*s^2*p^3-
3416928*s^4*p-772904*s^4*p^2-412576*s^8-87904*s^4*p^3-
1091552*s^6*p-188496*s^6*p^2-49472*s^10-14888*s^2*p^4-15040
*s^6*p^3-165472*s^8*p-24032*s^8*p^2-4800*s^12+8503056-4*s^6
*p^5-116*s^4*p^5-760*s^2*p^5-1440*s^12*p-16*s^2*p^6-88*s^10
*p^3-192*s^14-104*s^12*p^2)^2:

## poly(ma/wa+mb/wb+mc/wc):
madwaT := subs(q=4*p+q,(p+8)^4*(q+27)^2*T^8-1/4*(p+8)^3*(q+27)*(p*q^2+22*q^2
-4*q*p^2-5*q*p+984*q-110*p^2-900*p+10368)*T^6-1/128*(p+8)^2*
(-35432*p^4-48*p^4*q^2-2608*p^4*q-765144*p^3-38804*p^3*q+24*
p^3*q^3+260*p^3*q^2+545704*q*p^2+594*p^2*q^3-100656*p^2+
38569*p^2*q^2-3*p^2*q^4+31104000*p-4644*p*q^3+97792*p*q^2-
140*p*q^4+4423104*q*p-179159040-828*q^4-34007040*q+4*q^5-
81824*q^3-2540736*q^2)*T^4+1/1024*(p+8)*(-10701766656-
2650669056*q+2786918400*p+652990464*p^2+173924352*q*p+
37350528*q*p^2+70688960*p^3+22142400*p^4-226566144*q^2-80720
*p*q^4-1026624*p*q^3+4306176*p*q^2+9807*p^3*q^3-853116*p^3*q
^2-14488112*p^3*q+12392*p^4*q+4954*p^2*q^4+453432*p^2*q^3+
7349856*p^2*q^2-9683456*q^3-156544*q^4+2592*q^5+88*q^6-81658
*p^4*q^2+106424*p^5*q-90*p^2*q^5+638*p^3*q^4+12*p^4*q^4-1594
*p^4*q^3+45824*p^6+1895232*p^5-48*p^5*q^3+48*p^5*q^2+64*p^6*
q^2+3424*p^6*q-1388*p*q^5+4*p*q^6-p^3*q^5)*T^2+1/65536*(
1327104+202752*q+3904*q^2+32*q^3+4*q^4-230400*p+33472*q*p+
256*p*q^2-52*p*q^3-112688*p^2+2872*q*p^2+249*p^2*q^2-p^2*q^3
-13672*p^3-316*p^3*q+8*p^3*q^2-416*p^4-16*p^4*q)^2):

## poly(wa/ma+wb/mb+wc/mc):
wadmaT := (4*s^6-12*s^4*p+36*s^4-360*s^2*p-2052*s^2-15*s^2
*p^2-972*p-108*p^2-4*p^3-2916)^4*(2*s^2+p+10)^8*T^8-64*
(6561+65205*s^2-54630*s^4+2458*s^6+21*s^8+s^10+2916*p+
27450*s^2*p-17978*s^4*p+366*s^6*p-2*p*s^8+486*p^2+4333*
s^2*p^2-1952*s^4*p^2+9*s^6*p^2+36*p^3+304*s^2*p^3-70*s^
4*p^3+p^4+8*s^2*p^4)*(4*s^6-12*s^4*p+36*s^4-360*s^2*p-
2052*s^2-15*s^2*p^2-972*p-108*p^2-4*p^3-2916)^3*(2*s^2+
p+10)^6*T^6+512*(-17834429232*s^6*p-23639124888*s^6+
114791256*p-252110*s^6*p^6-5754919230*s^6*p^2-7082232*s
^6*p^5-1029710752*s^6*p^3-110343720*s^6*p^4-3840*s^6*p^
7+6552864*s^12*p+129140163-305746*s^10*p^4+7032528135*s
^4+2267027082*s^4*p^2+5668868*s^4*p^5+487731120*s^4*p^3
+65681975*s^4*p^4+9460*s^4*p^7+6031306656*s^4*p+128*s^4
*p^8+306176*s^4*p^6-6522*s^14*p^2+16*s^2*p^8+40430*s^2*
p^6+328506354*s^2*p^2+768020*s^2*p^5+69234264*s^2*p^3+
9116370*s^2*p^4+1216*s^2*p^7-61936*s^14*p+890327700*s^2
*p+1055205630*s^2+6129477072*p*s^8+48800*s^12*p^3+
860046*s^12*p^2+13848*p^6*s^8+24*s^16*p+232986696*p^3*s
^8+4807*s^16-127640*s^14+126*s^18-773961036*s^10+
18183670*s^12-12*s^18*p+1035*s^12*p^4+3*s^20-5188*s^10*
p^5+786860*p^5*s^8+18569988*p^4*s^8-144*s^14*p^3+
1638986962*p^2*s^8+9520884342*s^8-73093946*s^10*p^2-
380514152*s^10*p-6816936*s^10*p^3+2*s^16*p^2+216*p^7+
1377810*p^4+9920232*p^3+122472*p^5+44641044*p^2+6804*p^
6+3*p^8)*(4*s^6-12*s^4*p+36*s^4-360*s^2*p-2052*s^2-15*s
^2*p^2-972*p-108*p^2-4*p^3-2916)^2*(2*s^2+p+10)^4*T^4-
16384*(4*s^6-12*s^4*p+36*s^4-360*s^2*p-2052*s^2-15*s^2*
p^2-972*p-108*p^2-4*p^3-2916)*(368215*s^6*p^10+3584*s^6
*p^11+193936266777204*s^6*p+163690176574503*s^6+
376572715308*p-162669526*s^16*p^5+17185510*s^6*p^9+
480974522*s^6*p^8+117001014991*s^6*p^6+104378268004650*
s^6*p^2+1089573831522*s^6*p^5+33686002513980*s^6*p^3+
7243275144591*s^6*p^4+8968822728*s^6*p^7+166334910874*s
^14*p^4+13304817894*s^14*p^5-177728147370810*s^12*p-
1074*s^26*p-25711929*s^12*p^8+20898995702080*s^10*p^4+
41699212486425*s^4-230188*s^22*p+33276556994652*s^4*p^2
+530163707652*s^4*p^5+12194167464702*s^4*p^3+
3015588888774*s^4*p^4+6394497820*s^4*p^7+128*s^4*p^12+
703648*s^4*p^10+14022*s^4*p^11+55025845778970*s^4*p+
37096*s^24*p+21389186*s^4*p^9+438660233*s^4*p^8+
67941413788*s^4*p^6+6477647287740*s^14*p^2-29693476826*
p^7*s^8-1205338*s^2*p^9-23795613*s^2*p^8-3392137602*s^2
*p^6-1357047879525*s^2*p^2-25293521052*s^2*p^5-
526037307912*s^2*p^3-137049067962*s^2*p^4-333187992*s^2
*p^7+18045660755832*s^14*p-8*s^2*p^12-41113*s^2*p^10-
848*s^2*p^11+13424940*p^9*s^10-2111441665050*s^2*p-
1497380189985*s^2+140754*s^18*p^5+242953352*s^18*p^3-
538614876042576*p*s^8-18644673739940*s^12*p^3+
2426914925*s^18*p^2+186*s^24*p^3-75455441227512*s^12*p^
2-311500509034*s^12*p^5+6178*s^24*p^2+221568*s^14*p^8-
50562*s^16*p^7-378404216286*p^6*s^8-6*s^28*p-
775823089412*s^16*p+236338219521*s^10*p^6+282429536481-
4532514*s^16*p^6-1626953727*p^8*s^8-12800*p^11*s^8-
2155876*s^20*p^2+534886*s^20*p^3-100226943023670*p^3*s^
8+71111*s^24-1146429987581*s^16+21839156216163*s^14+
22465189693*s^18+767823259611051*s^10-185631860209059*s
^12+1213621*s^22+570233411*s^10*p^8-25*s^26*p^2+
11770686090*s^18*p-3098043729*s^16*p^4-2954923613736*s^
12*p^4-96062453*s^20+2668390083074*s^10*p^5-3399*s^18*p
^6-3435268457706*p^5*s^8+65850*s^20*p^4-59289038*p^9*s^
8-34227129600*s^16*p^3-298432*p^9*s^12-225*s^22*p^4-
22212257118774*p^4*s^8-982312936*s^12*p^7+11298098*s^18
*p^4+1318523851656*s^14*p^3-300496812189282*p^2*s^8-
437102422038891*s^8-36603034*s^20*p+1614*s^20*p^5+
14338078968*s^10*p^7+394258333087089*s^10*p^2+
820659867004674*s^10*p+112114637552608*s^10*p^3-1293480
*p^10*s^8+658210457*s^14*p^6+s^30-2567*s^26+63*s^28+
18385800*s^14*p^7-15908*s^22*p^3-152902*s^22*p^2+142080
*p^10*s^10-220985501986*s^16*p^2-21841962456*s^12*p^6+
108*p^11+5346*p^10+p^12+46766808*p^7+21308126895*p^4+
85232507580*p^3+3788111448*p^5+230127770466*p^2+
491051484*p^6+3247695*p^8+160380*p^9)*(2*s^2+p+10)^2*T^
2+65536*(-7185308688*s^6*p-9455036040*s^6+38263752*p-
104562*s^6*p^6-2334250602*s^6*p^2-2922824*s^6*p^5-
420269408*s^6*p^3-45296280*s^6*p^4-1600*s^6*p^7+3917664
*s^12*p-131238*s^10*p^4-37146195*s^4-2986578*s^4*p^2+
10620*s^4*p^5+99600*s^4*p^3+84957*s^4*p^4+12*s^4*p^7-
19183392*s^4*p+576*s^4*p^6+3458*s^14*p^2-16*s^2*p^8-
36230*s^2*p^6-232144218*s^2*p^2-650020*s^2*p^5-52036344
*s^2*p^3-7276410*s^2*p^4-1152*s^2*p^7-1104*s^14*p-
590621220*s^2*p-656034390*s^2+1835383536*p*s^8+24672*s^
12*p^3+506458*s^12*p^2+3760*p^6*s^8-1272*s^16*p+
66998296*p^3*s^8-5907*s^16-115592*s^14+42*s^18-
242342340*s^10+10428242*s^12-4*s^18*p+43046721+281*s^12
*p^4+s^20-2604*s^10*p^5+217652*p^5*s^8+5236044*p^4*s^8+
208*s^14*p^3+480865222*p^2*s^8+2910363858*s^8-25761726*
s^10*p^2-125571960*s^10*p-2614776*s^10*p^3-42*s^16*p^2+
72*p^7+459270*p^4+3306744*p^3+40824*p^5+14880348*p^2+
2268*p^6+p^8)^2:

## poly(1/ma/wa+1/mb/wb+1/mc/wc):
dmadwaT := s^4*(p+8)^4*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^
2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^4*T^8+4*s^2*(p+8)^3*(
5832+1944*p+216*p^2+8*p^3+3240*s^2+768*s^2*p+54*s^2*p^2+s^2*
p^3+600*s^4+108*s^4*p+4*s^4*p^2-8*s^6+4*s^6*p)*(-4*s^6+12*s^
4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+
972*p)^3*T^6+2*(p+8)^2*(45349632*p+33125760*s^2*p+7604928*s^
2*p^2+58366656*s^2+21710592*s^4+12597120*p^2+1866240*p^3+
155520*p^4+2077344*s^4*p^2+206704*s^4*p^3+2337408*s^6*p+
424992*s^6*p^2+55472*s^2*p^4+37216*s^6*p^3+374272*s^8*p+
54416*s^8*p^2+893520*s^2*p^3+10604736*s^4*p+4968000*s^6+
931968*s^8+20288*s^10+10872*s^4*p^4+1556*s^6*p^4+2560*s^10*p
^2+3*s^4*p^6+3360*s^8*p^3+72*s^8*p^4+16896*s^10*p+24*s^6*p^5
+284*s^4*p^5+1648*s^2*p^5+16*s^2*p^6+64*s^12*p+96*s^10*p^3+
48*s^12*p^2+6912*p^5-64*s^14+128*p^6+68024448)*(-4*s^6+12*s^
4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+
972*p)^2*T^4+4*(p+8)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*
s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*(16235168256*p+
57043118592*s^2*p+22238022528*s^2*p^2+63479407104*s^2+
48186316800*s^4+10269172224*p^2+3352980096*p^3+658098432*p^4
+10391597568*s^4*p^2+1751291136*s^4*p^3+6278508288*s^6*p+
1655963136*s^6*p^2+671572224*s^2*p^4+234722624*s^6*p^3+
604700928*s^8*p+179329920*s^8*p^2+4911883200*s^2*p^3+
34183980288*s^4*p+9937852416*s^6+765379584*s^8+176237568*s^
10+14317568*s^12+11360*s^12*p^4+175933152*s^4*p^4+19153056*s
^6*p^4+27390336*s^10*p^2+327672*s^4*p^6+26865280*s^8*p^3+
2259968*s^8*p^4+110211840*s^10*p+901824*s^6*p^5+10425792*s^4
*p^5+58017216*s^2*p^5+3066232*s^2*p^6+88040*s^2*p^7+111872*s
^14*p+8697600*s^12*p+3472512*s^10*p^3+2025216*s^12*p^2+
112832*s^8*p^5+3704*s^4*p^7+220864*s^12*p^3+56576*s^14*p^2-
7936*s^16*p+25024*s^6*p^6+240608*s^10*p^4+9072*s^10*p^5+6016
*s^14*p^3+384*s^16*p^2-256*s^18*p+82505088*p^5+9984*p^8+
341376*p^7-370688*s^14-29184*s^16+512*s^18+6692864*p^6+128*p
^9+872*s^2*p^8+s^4*p^9+12*s^6*p^8+192*s^14*p^4+160*s^10*p^6+
64*s^16*p^3+240*s^12*p^5+60*s^8*p^7+560*s^6*p^7+3496*s^8*p^6
-6*s^4*p^8-8*s^2*p^9+8435031552)*T^2+(-9984384*p-6533568*s^2
*p-1253664*s^2*p^2-13281408*s^2-2621376*s^4-2426112*p^2-
316944*p^3-23536*p^4-112416*s^4*p^2-4000*s^4*p^3+87808*s^6*p
+10928*s^6*p^2-4944*s^2*p^4+800*s^6*p^3+10752*s^8*p+960*s^8*
p^2-115760*s^2*p^3-936576*s^4*p+315648*s^6+39488*s^8-128*s^
10-64*s^12+132*s^4*p^4+24*s^6*p^4+16*s^10*p^2+32*s^8*p^3+192
*s^10*p+8*s^4*p^5-60*s^2*p^5+s^2*p^6-944*p^5-16*p^6-17216064
)^2:

## poly(1/ra/wa+1/rb/wb+1/rc/wc):
dradwaT:=s^6*(p+8)^2*T^4+1/2*s^2*(p+8)*(2*p^2+36*p-5*s^2*p-38*s^2+162)*T^2-s^2*(
p+8)*(2*s^2+p+10)*T-1975/4*p+37/4*s^2*p+9/16*s^2*p^2+75/2*s^2-1/4*s^4-231/4*p^
2-9/4*p^3-5625/4:

## poly(mb*mc+mc*ma+ma*mb):
mbmmcT := 256*T^4-288*(81-14*s^2+s^4+18*p-2*s^2*p+p^2)*T^2-32*
(4*s^6-12*s^4*p+36*s^4-15*s^2*p^2-360*s^2*p-2052*s^2-4*p^3-
108*p^2-2916-972*p)*T-540*p^3-15*p^4-556956*s^2-2268*s^6-
588*s^2*p^3-43740*p-7290*p^2-17388*s^2*p^2+60*s^6*p+86022*s
^4+14364*s^4*p+558*s^4*p^2-170748*s^2*p-98415-15*s^8:

## poly(1/(mb*mc)+1/(mc*ma)+1/(ma*mb)):
dmbdmcT := (4*s^6-12*s^4*p+36*s^4-15*s^2*p^2-360*s^2*p-2052*s^2
-4*p^3-108*p^2-2916-972*p)^2*T^4-192*(-9+s^2-p)*(4*s^6-12*s
^4*p+36*s^4-15*s^2*p^2-360*s^2*p-2052*s^2-4*p^3-108*p^2-
2916-972*p)*T^2-512*(4*s^6-12*s^4*p+36*s^4-15*s^2*p^2-360*s
^2*p-2052*s^2-4*p^3-108*p^2-2916-972*p)*T-36864*s^2:

## poly(ra*ma*wa+rb*mb*wb+rc*mc*wc):
rammamwaT := (2*s^2+p+10)^8*T^8-4*(-236196-131220*p-81000*s^2-
3936*s^4-3240*p^3-1764*s^4*p-4*p^5+108*s^6*p-12*s^4*p^3-
37764*s^2*p-6607*s^2*p^2-180*p^4-514*s^2*p^3+4*s^6*p^2+4*s^
8+616*s^6-29160*p^2-15*s^2*p^4-255*s^4*p^2)*(2*s^2+p+10)^6*
T^6+2*(185961834720*p+114791256000*s^2+5356925280*p^4+
53267394312*s^2*p^2+25428966336*s^4+92980917360*p^2+
27549901440*p^3+117291154464*s^2*p+48*s^12*p^4+348171091*s^
4*p^4+15475526*s^6*p^4-2014936*s^10*p^2+1940282*s^4*p^6-
3609008*s^8*p^3-197493*s^8*p^4-8267808*s^10*p+1225468*s^6*p
^5+32887180*s^4*p^5+272908440*s^2*p^5+20658456*s^2*p^6+
1005288*s^2*p^7-96*s^14*p+348256*s^12*p-237320*s^10*p^3+
46280*s^12*p^2-3088*s^8*p^5+65372*s^4*p^7+2560*s^12*p^3-32*
s^14*p^2+53294*s^6*p^6-13424*s^10*p^4-288*s^10*p^5+
714256704*p^5+174960*p^8+4199040*p^7+1472*s^14+48*s^16+
66134880*p^6+24081331104*s^4*p+1192117824*s^6-217151712*s^8
-13147072*s^10+938432*s^12+9970797384*s^4*p^2+2357550288*s^
4*p^3+1210543200*s^6*p+508211312*s^6*p^2+2403513000*s^2*p^4
+115570352*s^6*p^3-130411744*s^8*p-31016960*s^8*p^2+
14112081144*s^2*p^3+4320*p^9+28536*s^2*p^8+984*s^6*p^7+72*s
^8*p^6+963*s^4*p^8+360*s^2*p^9+48*p^10+167365651248)*(2*s^2
+p+10)^4*T^4-4*(-21961720756762560*p-13556617751088000*s^2-
2741449367442240*p^4-15659901890321616*s^2*p^2-
5347468929385728*s^4-17081338366370880*p^2-8224348102326720
*p^3-21383305066049472*s^2*p+18039631500*s^12*p^4-
669318986250396*s^4*p^4-93740813981856*s^6*p^4+
3634590940512*s^10*p^2-21239072929872*s^4*p^6-
17901423823744*s^8*p^3-4784674287628*s^8*p^4+7940676203136*
s^10*p-17870557626900*s^6*p^5-138540809858220*s^4*p^5-
492757537155840*s^2*p^5-83278683875376*s^2*p^6-
10723442007168*s^2*p^7-30352164224*s^14*p+701758472832*s^12
*p+942844644800*s^10*p^3+350557101024*s^12*p^2-882984199392
*s^8*p^5-2441743241328*s^4*p^7+100158695040*s^12*p^3-
9180616320*s^14*p^2-2093319872*s^16*p-2481734122871*s^6*p^6
+149482264784*s^10*p^4+14223511840*s^10*p^5-1354565440*s^14
*p^3-766826176*s^16*p^2+99390784*s^18*p-670132067596992*p^5
-1969817952960*p^8-17728361576640*p^7-40435913984*s^14-
2383269056*s^16+160476800*s^18-2356992*s^20-124098531036480
*p^6-7997524253790912*s^4*p-929716592326272*s^6-
39870722975040*s^8+7570177443072*s^10+611354631168*s^12-
5519835576492624*s^4*p^2-2327930040514752*s^4*p^3-
1335103063637184*s^6*p-877708690824384*s^6*p^2-
2186725214472480*s^2*p^4-349315553557440*s^6*p^3-
63043318106496*s^8*p-43875491529600*s^8*p^2-
7057549166559552*s^2*p^3-170231181120*p^9-1057179283776*s^2
*p^8+41856*s^22+64*s^24-13441496104*s^4*p^9-18786401585*s^6
*p^8-78809312*s^14*p^4+24874992*s^18*p^2+661705983*s^10*p^6
-1206208*s^20*p-151717568*s^16*p^3+2121813836*s^12*p^5-
10621839840*s^8*p^7-680849778*s^8*p^8-17455716*s^16*p^4-
211728*s^20*p^2+162575217*s^12*p^6+10816*s^22*p-
252975240598*s^6*p^7-115112000789*s^8*p^6-210508430472*s^4*
p^8-79407345600*s^2*p^9+3169920*s^18*p^3+3883092*s^14*p^5-
8792598*s^10*p^7-573168960*p^11-11348745408*p^10-21228480*p
^12-35274633*s^6*p^10-760190*s^6*p^11-1160928*s^16*p^5-
991238584*s^6*p^9+210196*s^12*p^8-370748*s^4*p^12-617873152
*s^4*p^10-19362416*s^4*p^11-5162016*s^2*p^12-4473318960*s^2
*p^10-183269952*s^2*p^11-147380*p^9*s^10+6592*s^18*p^5+1008
*s^14*p^8-576*s^16*p^7-40880*s^16*p^6-8388*p^11*s^8-14784*s
^20*p^3-2919813*s^10*p^8+64*s^18*p^6-320*s^20*p^4-28905156*
p^9*s^8+2400*p^9*s^12+7790052*s^12*p^7+211152*s^18*p^4-
732149*p^10*s^8+875844*s^14*p^6+49984*s^14*p^7+704*s^22*p^2
-2628*p^10*s^10-89472*s^2*p^13-3276*s^4*p^13-7503*s^6*p^12-
720*s^2*p^14-8640*p^14-544320*p^13-13177032454057536-64*p^
15)*(2*s^2+p+10)^2*T^2+(61987278240*p+55788550416+
38263752000*s^2+1785641760*p^4+17755798104*s^2*p^2+
8588296512*s^4+30993639120*p^2+9183300480*p^3+39097051488*s
^2*p+16*s^12*p^4+116626289*s^4*p^4+5370530*s^6*p^4-455880*s
^10*p^2+648126*s^4*p^6-820432*s^8*p^3-44615*s^8*p^4-1616736
*s^10*p+417668*s^6*p^5+10999812*s^4*p^5+90969480*s^2*p^5+
6886152*s^2*p^6+335096*s^2*p^7-1824*s^14*p+110368*s^12*p-
61144*s^10*p^3+17176*s^12*p^2-560*s^8*p^5+21812*s^4*p^7+
1024*s^12*p^3-96*s^14*p^2+17930*s^6*p^6-3920*s^10*p^4-96*s^
10*p^5+238085568*p^5+58320*p^8+1399680*p^7-8384*s^14+16*s^
16+22044960*p^6+8113268448*s^4*p+498840768*s^6-44772768*s^8
-2152768*s^10+242496*s^12+3351986712*s^4*p^2+791041968*s^4*
p^3+469813536*s^6*p+187424336*s^6*p^2+801171000*s^2*p^4+
41131664*s^6*p^3-28042144*s^8*p-6898816*s^8*p^2+4704027048*
s^2*p^3+1440*p^9+9512*s^2*p^8+328*s^6*p^7+24*s^8*p^6+321*s^
4*p^8+120*s^2*p^9+16*p^10)^2:

## poly(cos(A/2)+cos(B/2)+cos(C/2)):
cosAd2T := (p+8)^4*T^8-8*(p+9)*(p+8)^3*T^6-8*(p+8)^2*(-2*p^2-36*
p+s^2-162)*T^4-32*(p+8)*(p+7)*s^2*T^2+16*s^4:
#cosAd2T :=subs(q=4*p+q,(p+8)^4*T^8-8*(p+9)*(p+8)^3*T^6-8*(p+8)^2*(-2*p^2-36*
#p+q-135)*T^4-32*(p+8)*(p+7)*(q+27)*T^2+16*(q+27)^2):

## poly(cos(A/2)^3+cos(B/2)^3+cos(C/2)^3):
cosAd2p3T := (p+8)^6*T^4+2*(p+8)^3*(-2*p^3-54*p^2-486*p+3*s^2*p-
1458+30*s^2)*T^2-8*s^3*(p+8)^3*T-s^2*(26244+972*p^2+8748*p-
888*s^2+36*p^3-180*s^2*p-9*s^2*p^2+4*s^4):

## poly(cos(A/2)^5+cos(B/2)^5+cos(C/2)^5):
cosAd2p5T := (p+8)^10*T^4-2*(p+8)^5*(2*p^5+90*p^4+1620*p^3-5*s^2*p
^3+14580*p^2-150*s^2*p^2+65610*p-1485*s^2*p+5*s^4*p+118098-
4860*s^2+50*s^4)*T^2-8*s^5*(p+8)^5*T-s^2*(22963500*p^3-
17423100*s^2*p-571500*s^2*p^3+197140*s^4*p+29850*s^4*p^2-
4343625*s^2*p^2+478296900+372008700*p-28868400*s^2+2551500*p
^4+2000*s^4*p^3-500*s^6*p-25*s^6*p^2+170100*p^5+6300*p^6+100
*p^7+124002900*p^2+4*s^8-41750*s^2*p^4+486360*s^4-2480*s^6-
1600*s^2*p^5+50*s^4*p^4-25*s^2*p^6):

## poly(cos(B/2)*cos(C/2)+cos(C/2)*cos(A/2)+cos(A/2)*cos(B/2)):
cosBd2mcosCd2T :=subs(q=4*p+q, (p+8)^4*T^4-2*(p+8)^2*(p^2+18*p+q+108)*T^2-8*(p+8)^2*
(q+27)*T-3888+216*p+324*p^2+36*p^3+p^4-360*q-100*q*p-6*q*p^2+q^2):

## poly(sin(A/2)+sin(B/2)+sin(C/2)):
sinAd2T :=subs(q=4*p+q, (p+8)^2*T^4-2*(p+8)*(p+6)*T^2-8*(p+8)*T-4*q-12+p^2+20*p):

## poly(sin(A/2)^3+sin(B/2)^3+sin(C/2)^3):
sinAd2p3T := (p+8)^6*T^4-2*(p+8)^3*(p^3+24*p^2-3*s^2*p+192*p+510-18*s^2)*T^2-8*(p+8)
^3*T+197376*p-180*s^2*p^3-10524*s^2*p-2052*s^2*p^2-20484*s^2+504*s^4+61536*p^2
+10244*p^3+960*p^4-6*s^2*p^4+264192-4*s^6+9*s^4*p^2+p^6+132*s^4*p+48*p^5:

## poly(sin(A/2)^5+sin(B/2)^5+sin(C/2)^5):
sinAd2p5T := (p+8)^10*T^4-2*(p+8)^5*(p^5+40*p^4+640*p^3-5*s^2*p^3+5120*p^2-110*s^2*p
^2+20480*p-815*s^2*p+5*s^4*p+32766-2020*s^2+30*s^4)*T^2-8*(p+8)^5*T+1342259200
*p+6136880*s^4-136338140*s^2*p-61312260*s^2*p^2-132746820*s^2-129240*s^6+
754995200*p^2+251660800*p^3+55050400*p^4-14890*s^6*p^2-2536100*s^2*p^4-1400*s^
6*p^3+340*s^8*p+25*s^8*p^2-15767580*s^2*p^3+4884380*s^4*p+1200*s^8-4*s^10+
29050*s^4*p^4+1625225*s^4*p^2+289300*s^4*p^3-71220*s^6*p-261240*s^2*p^5-16830*
s^2*p^6-620*s^2*p^7+8257540*p^5+2880*p^8+61440*p^7+860160*p^6+80*p^9-10*s^2*p^
8+p^10-50*s^6*p^4+35*s^4*p^6+1560*s^4*p^5+1073872896:

## poly(sin(A/2)^7+sin(B/2)^7+sin(C/2)^7):
sinAd2p7T := (p+8)^14*T^4-2*(p+8)^7*(p^7+56*p^6-7*s^2*p^5+1344*p^5+17920*p^4-266*s^2
*p^4+143360*p^3+14*s^4*p^3-4053*s^2*p^3+688128*p^2+294*s^4*p^2-30940*s^2*p^2-\
118307*s^2*p+1835008*p-7*s^6*p+2086*s^4*p+2097150-181230*s^2+4970*s^4-42*s^6)*
T^2-8*(p+8)^7*T-1161367410812*s^2*p+7696588734464*p+6253475135488*p^2-\
813390333028*s^2*p^2-760179385252*s^2+53712056328*s^4+40943485905*s^4*p^2+
3126736764928*p^3+1074815637504*p^4-1981671804*s^6-98988067108*s^2*p^4-\
265719552*s^6*p^3+33355560*s^8*p+11548166*s^8*p^2-345334681020*s^2*p^3+
69885046420*s^4*p+40294128*s^8-435036*s^10+2184*s^12+3244947090*s^4*p^4+
14223932100*s^4*p^3-2117689560*s^6*p-991591636*s^6*p^2+2140180*s^8*p^3+223930*
s^8*p^4-249452*s^10*p-4792592*s^6*p^5+507961832*s^4*p^5-20181945084*s^2*p^5-\
3001047140*s^2*p^6-327940396*s^2*p^7+644*s^12*p-5292*s^10*p^3+49*s^12*p^2+
12544*s^8*p^5+4124960*s^4*p^7-322616*s^6*p^6-196*s^10*p^4+268703896832*p^5+
787218432*p^8+7197425668*p^7-4*s^14+50381979872*p^6+65601536*p^9-26136838*s^2*
p^8+5880*s^4*p^9-210*s^6*p^8-12432*s^6*p^7+294*s^8*p^6+202230*s^4*p^8-1481704*
s^2*p^9+186368*p^11+4100096*p^10+5824*p^12+77*s^4*p^10-14*s^2*p^12-56714*s^2*p
^10-1316*s^2*p^11+112*p^13+p^14-44571968*s^6*p^4-54208*s^10*p^2+55258035*s^4*p
^6+4398054899712:

## poly(sin(B/2)*sin(C/2)+sin(C/2)*sin(A/2)+sin(A/2)*sin(B/2)):
sinBd2msinCd2T :=subs(q=4*p+q, (p+8)^4*T^4-2*(p+8)^2*(-2*p+12+q)*T^2-8*(p+8)^2*T-48
-4*q*p+24*q-104*p+q^2):

## poly(sec(B/2)*sec(C/2)+sec(C/2)*sec(A/2)+sec(A/2)*sec(B/2)):
secBd2msecCd2T :=subs(q=4*p+q, (q+27)*T^4-4*(p+9)*(p+8)*T^2-8*(p+8)^2*T-4*(p+8)^2):

## poly(cos((B-C)/2)+cos((C-A)/2)+cos((A-B)/2))
cosBsCd2T:=(p+8)^4*T^4-2*(p+8)^2*(p^2+18*p+84+4*s^2)*T^2-8*(p+8)^2*(2*s^2+p+10)*T+p
^4+13200+5040*p+712*p^2-1376*s^2-272*s^2*p-12*s^2*p^2+44*p^3+16*s^4:

## poly(NA+NB+NC):
NAT :=subs(q=4*p+q, T^8+8*(3*p-q-6)*T^6+16*(q^2+30-6*q*p+10*q+9*p^2-30*p)*
T^4+64*(2*q^2+63*p^2-24*q*p-28-14*q-q*p^2+42*p+4*p^3)*T^2+
256*(3*p-q-3)^2):

## poly(1/NA+1/NB+1/NC):
dNAT := (p+8)^4*(-4*p^2-40*p-100+4*s^2+s^2*p)^4*T^8-4*(p+8)^3*(-3*p-23+s^2)*(-3
*p-15+s^2)*(-4*p^2-40*p-100+4*s^2+s^2*p)^3*T^6+2*(p+8)^2*(147*p^4+3756*p^3-268*
s^2*p^3+35442*p^2-5124*s^2*p^2+154*s^4*p^2+146220*p-32268*s^2*p+1956*s^4*p-36*s
^6*p+222675-66884*s^2+6146*s^4-228*s^6+3*s^8)*(-4*p^2-40*p-100+4*s^2+s^2*p)^2*T
^4-4*(p+8)*(-4*p^2-40*p-100+4*s^2+s^2*p)*(5169750*p-5218130*s^2-4167546*s^2*p-
1322284*s^2*p^2+1197791*s^4+2237175*p^2+511540*p^3+65127*p^4+178882*s^4*p^2+
18668*s^4*p^3-53076*s^6*p-8348*s^6*p^2-16290*s^2*p^4-436*s^6*p^3+1614*s^8*p+127
*s^8*p^2-208300*s^2*p^3+757884*s^4*p-112028*s^6+5111*s^8-114*s^10+s^12+4374*p^5
+121*p^6+727*s^4*p^4-18*s^10*p-506*s^2*p^5+4935625)*T^2+(-15375-14444*s^2+1878*
s^4-76*s^6+s^8-11100*p-6660*s^2*p+588*s^4*p-12*s^6*p-2970*p^2-1020*s^2*p^2+46*s
^4*p^2-348*p^3-52*s^2*p^3-15*p^4)^2:

## poly(JA+JB+JC):
JAT := subs(q=4*p+q,(p+9)^8*T^8+(p+9)^6*(4*p^3+27*p^2-3*q*p^2-56*q*p-540*p
-3888-252*q)*T^6+1/8*(p+9)^4*(48*p^6+1512*p^5-40*p^5*q-1102*
p^4*q+17631*p^4+15*p^4*q^2-5944*p^3*q+131112*p^3+560*p^3*q^2
+1224720*p^2+80136*q*p^2+7768*p^2*q^2+982368*q*p+8957952*p+
47424*p*q^2+25194240+2892672*q+107568*q^2)*T^4+1/16*(p+9)^2*
(-2358180864*p-3769058304*q+3436494336*p^2+1708216128*p^3-
2243966976*q*p-489094848*q*p^2+367742592*p^4-191289600*q^2-
2683008*p*q^3-118304064*p*q^2-110528*p^3*q^3-2893472*p^3*q^2
-40097376*p^3*q+1012716*p^4*q-750096*p^2*q^3-27964656*p^2*q^
2-3948480*q^3-58376*p^4*q^2+377568*p^5*q+3468879*p^6+
45370044*p^5+4752*p^8+166428*p^7+64*p^9-9060*p^4*q^3-392*p^5
*q^3+13740*p^5*q^2+1149*p^6*q^2+19451*p^6*q-7*p^6*q^3-16*p^8
*q+28*p^7*q^2+8*p^7*q-15237476352)*T^2+1/256*(-19440*q^2-
9024*p*q^2-1528*p^2*q^2-112*p^3*q^2-3*p^4*q^2-1026432*q-
432864*q*p-60264*q*p^2-2344*p^3*q+118*p^4*q+8*p^5*q-5038848+
559872*p+1061424*p^2+251640*p^3+24813*p^4+1080*p^5+16*p^6)^2):

## poly(IA+IB+IC):
IAT :=subs(q=4*p+q, T^4+2*(2*p-12-q)*T^2-8*(p+8)*T-4*q*p-104*p+q^2-48+24*q):

## poly(1/IA+1/IB+1/IC):
dIAT :=subs(q=4*p+q, (p+8)^2*T^4-2*(p+8)*(p+6)*T^2-8*(p+8)*T-4*q-12+p^2+20*p):

## poly(KA+KB+KC):
KAT :=subs(q=4*p+q, (-q-18+p)^8*T^8+(4*p^3-3*q*p^2+12*p*q^2+592*q*p+8208*p
-4*q^3-232*q^2-4032*q-15552+27*p^2)*(-q-18+p)^6*T^6+1/8*(-
891316224*p+328458240*q+175333248*p^2-1694304*p^3-265089024*
q*p+27551232*q*p^2+87615*p^4+66769920*q^2-31424*p*q^4-
1340544*p*q^3-27527424*p*q^2-216*p^3*q^3-13608*p^3*q^2-
298624*p^3*q+4082*p^4*q+472*p^2*q^4+45480*p^2*q^3+1670256*p^
2*q^2+5844480*q^3+256192*q^4+5568*q^5+48*q^6+111*p^4*q^2-288
*p*q^5-40*p^5*q+48*p^6+1512*p^5+403107840)*(-q-18+p)^4*T^4+1
/16*(5073354031104*p-1460217839616*q-3504538939392*p^2+
454722066432*p^3+3443723403264*q*p-1303725404160*q*p^2-
9714572352*p^4-653452738560*q^2+6669892608*p*q^4+96769253376
*p*q^3+812179685376*p*q^2+638612864*p^3*q^3+11659979008*p^3*
q^2+112771381248*p^3*q-2024955072*p^4*q-709617600*p^2*q^4-
15379324416*p^2*q^3-194043313152*p^2*q^2-128481804288*q^3-
13729370112*q^4-877355008*q^5-34643456*q^6-157727000*p^4*q^2
+278847488*p*q^5+11922768*p^5*q+5545071*p^6+154699632*p^5-
831232*q^7-11136*q^8+4752*p^8+26460*p^7+64*p^9-64*q^9-282160
*p^2*q^6-19182848*p^2*q^5+97280*p*q^7+7000064*p*q^6+310496*p
^3*q^5+19450688*p^3*q^4-97360*p^4*q^4-5805164*p^4*q^3-20504*
p^5*q^3+83684*p^5*q^2+33373*p^6*q^2+569819*p^6*q+537*p^6*q^3
+576*p*q^8-16*p^8*q-164*p^7*q^2-1744*p^2*q^7+2016*p^3*q^6-
556*p^4*q^5-460*p^5*q^4-10360*p^7*q-975198486528)*(-q-18+p)^
2*T^2+1/256*(-380712960*p+77635584*q+42270336*p^2-2331936*p^
3-95883264*q*p+8363520*q*p^2-45171*p^4+19823616*q^2-10816*p*
q^4-466304*p*q^3-9616128*p*q^2-8*p^3*q^3-4088*p^3*q^2-199552
*p^3*q-5066*p^4*q+136*p^2*q^4+14712*p^2*q^3+552016*p^2*q^2+
1853952*q^3+84032*q^4+1856*q^5+16*q^6-99*p^4*q^2-96*p*q^5+8*
p^5*q+16*p^6+1080*p^5-80621568)^2):

## poly(ga+gb+gc):
gaT :=subs(q=4*p+q, (p+8)^4*T^8+4*(p+8)^3*(2*p^2+3*p-q*p-216-12*q)*T^6+2*(
p+8)^2*(8*p^4-12*p^3*q-68*p^3-4113*p^2-186*q*p^2+3*p^2*q^2+
72*p*q^2-19440*p+600*q*p+77760+432*q^2+13248*q)*T^4-4*(p+8)*
(248*p^5+8*p^5*q+76*p^4*q-6*p^4*q^2+7834*p^4-3753*p^3*q+
72217*p^3-177*p^3*q^2+p^3*q^3+36*p^2*q^3-63900*q*p^2+77544*p
^2-1200*p^2*q^2-855360*p+432*p*q^3-215424*q*p+6192*p*q^2+
2612736+546048*q+65664*q^2+1728*q^3)*T^2+(-144*q^2-24*p*q^2-
p^2*q^2-2880*q+120*q*p+78*q*p^2+4*p^3*q+15552+16848*p+2403*p
^2+92*p^3)^2):

## poly(1/ga+1/gb+1/gc):
dgaT :=subs(q=4*p+q, 1/256*(9*q*p+108*q+5832+1215*p+108*p^2+4*p^3)^4*T^8-1/
64*(1944+243*p+18*p^2+p^3+72*q+6*q*p)*(9*q*p+108*q+5832+1215
*p+108*p^2+4*p^3)^3*T^6+1/128*(10368*q^2+1728*p*q^2+72*p^2*q
^2+466560*q+86832*q*p+7452*q*p^2+528*p^3*q+20*p^4*q+6298560+
1854576*p+355023*p^2+45468*p^3+3342*p^4+140*p^5+3*p^6)*(9*q*
p+108*q+5832+1215*p+108*p^2+4*p^3)^2*T^4-1/64*(9*q*p+108*q+
5832+1215*p+108*p^2+4*p^3)*(p^9+86*p^8+3445*p^7+2*p^7*q+
85532*p^6+216*p^6*q+8388*p^5*q-24*p^5*q^2+1463859*p^5+
17648118*p^4+150912*p^4*q-1440*p^4*q^2+144271287*p^3-33912*p
^3*q^2+1249290*p^3*q+2583576*q*p^2+734254632*p^2-393984*p^2*
q^2+1984046400*p-23514624*q*p-2270592*p*q^2-5225472*q^2+
1904684544-110854656*q)*T^2+1/256*(p+9)^2*(p^5+59*p^4-4*p^3*
q+1191*p^3-156*q*p^2+9477*p^2-2160*q*p+11664*p-10368*q-
139968)^2):

## poly(kb*kc+kc*ka+ka*kb):
kbmkcT:= 1/64*(2*p^3-5*s^2*p^2+54*p^2+6*s^4*p-84*s^2*p+486*p-2*s^6+46*s^4-350*s^2
+1458)^4*T^4+1/16*s^2*(p+8)^2*(81-14*s^2+s^4+18*p-2*s^2*p+p^2)*(4*p^3-3*s^2*p^
2+108*p^2+12*s^4*p-24*s^2*p+972*p+60*s^4-4*s^6+36*s^2+2916)*(2*p^3-5*s^2*p^2+
54*p^2+6*s^4*p-84*s^2*p+486*p-2*s^6+46*s^4-350*s^2+1458)^2*T^2+1/8*s^4*(p+8)^4
*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*
p)*(2*p^3-5*s^2*p^2+54*p^2+6*s^4*p-84*s^2*p+486*p-2*s^6+46*s^4-350*s^2+1458)^2
*T-1/4*s^6*(p+8)^4*(p+9-s^2)*(3*p^2+64*p+336-16*s^2)*(1417176*p-184788*s^2*p^2
-802872*s^2*p-1393848*s^2+174204*s^4+393660*p^2+58320*p^3+4860*p^4+16996*s^4*p
^2+1432*s^4*p^3-16304*s^6*p-2124*s^6*p^2-1220*s^2*p^4-92*s^6*p^3+1016*s^8*p+64
*s^8*p^2-21244*s^2*p^3+89136*s^4*p-41616*s^6+4028*s^8-184*s^10+4*s^12+45*s^4*p
^4-24*s^10*p-28*s^2*p^5+216*p^5+4*p^6+2125764):

##poly(KB*KB+KC*KA+KA*KB):
KBmKCT:= 1/16*(2*p+18-s^2)^8*T^4+1/128*s^2*(p+8)^2*(5832+1944*p+216*p^2+8*p^3-\
4536*s^2-960*s^2*p-51*s^2*p^2+312*s^4+24*s^4*p-8*s^6)*(2*p+18-s^2)^4*T^2+1/128
*s^4*(p+8)^4*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p
^2+2916+972*p)*(2*p+18-s^2)^2*T-1/4096*s^6*(p+8)^4*(73903104+39377664*p+
8386416*p^2+892368*p^3+47440*p^4+1008*p^5-25629696*s^2-10526976*s^2*p-1615248*
s^2*p^2-109696*s^2*p^3-2781*s^2*p^4+3621888*s^4+1043712*s^4*p+98448*s^4*p^2+
3024*s^4*p^3-211968*s^6-32512*s^6*p-1008*s^6*p^2+4096*s^8):

##poly(JB*JC+JC*JA+JA*JB):
JBmJCT:= (p+9)^8*T^4+1/8*s^2*(p+8)*(p+9)^4*(8*p^4+280*p^3-3*s^2*p^3+3672*p^2-88*s
^2*p^2+21384*p-840*s^2*p+46656-2592*s^2)*T^2+1/8*s^4*(p+9)^2*(p+8)^2*(4*p^5+
172*p^4-s^2*p^4-40*s^2*p^3+2956*p^3+25380*p^2-588*s^2*p^2+108864*p-3744*s^2*p-\
8640*s^2+186624)*T+1/256*s^6*(p+8)^2*(16*p^7+944*p^6-3*s^2*p^6+23856*p^5-176*s
^2*p^5-4240*s^2*p^4+334736*p^4+2815488*p^3-53568*s^2*p^3-373248*s^2*p^2+
14183424*p^2+39564288*p-1354752*s^2*p+47029248-1990656*s^2):

##poly(cb*cc+cc*ca+ca*cb):
cbmccT:= 1/64*(2*p^3+54*p^2+486*p+s^2*p+1458+10*s^2)^4*T^4+1/16*s^2*(p+8)*(720*s^
4+252*s^4*p+28*s^4*p^2+s^4*p^3-151632*s^2-86184*s^2*p-19692*s^2*p^2-2259*s^2*p
^3-130*s^2*p^4-3*s^2*p^5+1889568+1285956*p+364500*p^2+55080*p^3+4680*p^4+212*p
^5+4*p^6)*(2*p^3+54*p^2+486*p+s^2*p+1458+10*s^2)^2*T^2+1/8*s^4*(p+8)^2*(4*p^5+
172*p^4-s^2*p^4-40*s^2*p^3+2956*p^3+25380*p^2-588*s^2*p^2+108864*p-3744*s^2*p-\
8640*s^2+186624)*(2*p^3+54*p^2+486*p+s^2*p+1458+10*s^2)^2*T+1/4*s^6*(p+9)*(p+8
)^2*(9421386048*p-183358080*s^2-78839568*s^2*p^2-183031488*s^2*p-5313600*s^4+
5051760048*p^2+1596824928*p^3+329802516*p^4-1771536*s^4*p^2-361520*s^4*p^3-\
2886780*s^2*p^4-19179600*s^2*p^3-4734720*s^4*p+46538712*p^5+13292*p^8+303792*p
^7+4546572*p^6-43540*s^4*p^4-121*s^4*p^6-3100*s^4*p^5-275612*s^2*p^5-16316*s^2
*p^6-548*s^2*p^7-2*s^4*p^7-8*s^2*p^8+344*p^9+4*p^10+7856823744):

##poly(NB*NC+NC*NA+NA*NB):
NBmNCT:= -1/15*T^4+2/15*(3*p+23-s^2)*(3*p+15-s^2)*T^2-8/15*(p+8)*(4*p^2+40*p+100-\
4*s^2-s^2*p)*T+740*p+76/15*s^6+14444/15*s^2+68*s^2*p^2+444*s^2*p-626/5*s^4+198
*p^2+116/5*p^3+p^4-46/15*s^4*p^2+4/5*s^6*p+52/15*s^2*p^3-196/5*s^4*p-1/15*s^8+
1025:

##poly(nb*nc+nc*na+na*nb):
nbmncT:= 1/16*(p+8)^2*T^4+1/8*s^2*(p+8)*(8*p^2-3*s^2*p+112*p-16*s^2+360)*T^2+1/2*
s^4*(p+8)*(4*p^2+40*p+100-4*s^2-s^2*p)*T+1/16*s^6*(16*p^3-3*s^2*p^2+224*p^2-32
*s^2*p+1104*p-64*s^2+1664):

##poly(ha/ma+hb/mb+hc/mc):
hadmaT:= 1/256*(p+8)^8*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^
3+108*p^2+2916+972*p)^4*T^8+1/4*(p+8)^6*(p^2+18*p+18*s^2-2*s^2*p+s^4+81)*(81-\
14*s^2+s^4+18*p-2*s^2*p+p^2)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052
*s^2+4*p^3+108*p^2+2916+972*p)^3*T^6+2*(p+8)^4*(114791256*p+133686936*s^2+
27474552*s^2*p^2+93166200*s^2*p+72914580*s^4+44641044*p^2+9920232*p^3+1377810*
p^4-6321240*s^6+1066770*s^8-6360*s^10-2540*s^12+12342348*s^4*p^2+1813200*s^4*p
^3-4016520*s^6*p-1053936*s^6*p^2+419400*s^2*p^4-142864*s^6*p^3+384840*s^8*p+
52204*s^8*p^2+4429080*s^2*p^3+45942552*s^4*p+153668*s^4*p^4-9928*s^6*p^4+1528*
s^10*p^2+140*s^4*p^6+3400*s^8*p^3+106*s^8*p^4+10024*s^10*p-280*s^6*p^5+7112*s^
4*p^5+23144*s^2*p^5+680*s^2*p^6+8*s^2*p^7-24*s^14*p-440*s^12*p-8*s^10*p^3+52*s
^12*p^2+122472*p^5+3*p^8+216*p^7+24*s^14+3*s^16+6804*p^6+129140163)*(-4*s^6+12
*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^2*T^4+64
*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+
2916+972*p)*(376572715308*p+835278574284*s^2+540150255108*s^2*p^2+996445497708
*s^2*p+1086453534114*s^4+230127770466*p^2+85232507580*p^3+21308126895*p^4+
756116697564*s^6+260623360431*s^8-9928643688*s^10-1049325732*s^12+569721088890
*s^4*p^2+164369589552*s^4*p^3+736986973572*s^6*p+319565548080*s^6*p^2+
38055427128*s^2*p^4+80881778448*s^6*p^3+231566210424*s^8*p+90055279332*s^8*p^2
+175624244388*s^2*p^3+1171984002948*s^4*p+31171391676*s^4*p^4+13163780952*s^6*
p^4-384865128*s^10*p^2+367989772*s^4*p^6+20023318728*s^8*p^3+2784567234*s^8*p^
4-4501195272*s^10*p+1428182568*s^6*p^5+4060530216*s^4*p^5+5770268280*s^2*p^5+
624729672*s^2*p^6+48294792*s^2*p^7-4073016*s^14*p-697246776*s^12*p+140129080*s
^10*p^3-180665244*s^12*p^2+248085864*s^8*p^5+22911760*s^4*p^7-22615312*s^12*p^
3-3495888*s^14*p^2+958492*s^16*p+103249424*s^6*p^6+39218920*s^10*p^4+4172552*s
^10*p^5-606000*s^14*p^3+93626*s^16*p^2+16732*s^18*p+3788111448*p^5+3247695*p^8
+46766808*p^7+16536600*s^14+2251087*s^16-15460*s^18-2270*s^20+491051484*p^6-\
1318388*s^12*p^4+160380*p^9+2612412*s^2*p^8+12*s^22+s^24+22804*s^4*p^9+129676*
s^6*p^8-40440*s^14*p^4+3844*s^18*p^2+210280*s^10*p^6-524*s^20*p-932*s^16*p^3-\
21992*s^12*p^5+441624*s^8*p^7+6183*s^8*p^8-185*s^16*p^4+34*s^20*p^2+516*s^12*p
^6-12*s^22*p+4794160*s^6*p^7+13833684*s^8*p^6+938018*s^4*p^8+94172*s^2*p^9+68*
s^18*p^3-936*s^14*p^5+4168*s^10*p^7+108*p^11+282429536481+5346*p^10+p^12+1556*
s^6*p^9+250*s^4*p^10+2036*s^2*p^10+20*s^2*p^11)*T^2+256*(38263752*p+125183880*
s^2+31568616*s^2*p^2+96000552*s^2*p+75066588*s^4+14880348*p^2+3306744*p^3+
459270*p^4-6309576*s^6+1019142*s^8-6216*s^10-2212*s^12+11994372*s^4*p^2+
1638384*s^4*p^3-4085208*s^6*p-1019088*s^6*p^2+633240*s^2*p^4-123440*s^6*p^3+
392472*s^8*p+47908*s^8*p^2+5770440*s^2*p^3+46584072*s^4*p+125052*s^4*p^4-7288*
s^6*p^4+2152*s^10*p^2+84*s^4*p^6+1560*s^8*p^3-34*s^8*p^4+9144*s^10*p-168*s^6*p
^5+5048*s^4*p^5+41720*s^2*p^5+1528*s^2*p^6+24*s^2*p^7-8*s^14*p-488*s^12*p+104*
s^10*p^3-4*s^12*p^2+40824*p^5+p^8+72*p^7+8*s^14+s^16+2268*p^6+43046721)^2:

##poly(ma/ha+mb/hb+mc/hc):
madhaT:= 16*s^4*T^8-8*s^2*(s^4-6*s^2-2*s^2*p+81+p^2+18*p)*T^6+(-92*s^2*p^2-1620*s
^2+p^4+76*s^4*p+6*s^4*p^2-4*s^2*p^3+6561-20*s^6+2916*p+342*s^4-4*s^6*p-684*s^2
*p+s^8+486*p^2+36*p^3)*T^4+1/4*(568*s^2*p^3+4*p^5+3244*p^3+8*s^8+204*s^4*p^2+
180*p^4+29268*p^2+12*s^4*p^3-4*s^6*p^2-96*s^6*p+864*s^4*p+132192*p+8004*s^2*p^
2-448*s^6-144*s^4+15*s^2*p^4+239112+115776*s^2+49824*s^2*p)*T^2+(p+9-s^2)^4:

##poly(wa/IA+wb/IB+wc/IC):
wadIAT:= (2*s^2+p+10)*T-18-10*s^2-2*p:

##poly(ma/a+mb/b+mc/c):
madaT:= s^8*(p+8)^8*T^8+s^6*(p+8)^6*(4*p^3+108*p^2-3*s^2*p^2+972*p-56*s^2*p+12*s
^4*p+2916+92*s^4-252*s^2-4*s^6)*T^6+1/8*s^4*(p+8)^4*(17006112*p-2916000*s^2-\
339336*s^2*p^2-1578528*s^2*p+638928*s^4+4723920*p^2+699840*p^3+58320*p^4+50904
*s^4*p^2+3888*s^4*p^3-46272*s^6*p-5496*s^6*p^2-1912*s^2*p^4-216*s^6*p^3+7456*s
^8*p+472*s^8*p^2-36184*s^2*p^3+295104*s^4*p-129216*s^6+29392*s^8-2208*s^10+48*
s^12+2592*p^5+48*p^6+111*s^4*p^4-288*s^10*p-40*s^2*p^5+25509168)*T^4+1/16*s^2*
(p+8)^2*(24794911296*p-2074745664*s^2-619463376*s^2*p^2-1723286016*s^2*p-\
668860416*s^4+11019960576*p^2+2857026816*p^3+476171136*p^4-181964448*s^4*p^2-\
34505504*s^4*p^3+185817600*s^6*p+52361424*s^6*p^2-15649200*s^2*p^4+7835840*s^6
*p^3-17795712*s^8*p-3902400*s^8*p^2-125574624*s^2*p^3-532935936*s^4*p+
24794911296+273701376*s^6-32056704*s^8-1352320*s^10+967168*s^12+52907904*p^5+
5184*p^8+186624*p^7-105472*s^14+4416*s^16-64*s^18+3919104*p^6-3923876*s^4*p^4+
656476*s^6*p^4-171824*s^10*p^2-10124*s^4*p^6-421312*s^8*p^3-22300*s^8*p^4-\
798208*s^10*p+29176*s^6*p^5-267532*s^4*p^5-1221696*s^2*p^5-57904*s^2*p^6-1504*
s^2*p^7-27136*s^14*p+371456*s^12*p-16096*s^10*p^3+47456*s^12*p^2-460*s^8*p^5-\
164*s^4*p^7+2016*s^12*p^3-1744*s^14*p^2+576*s^16*p+537*s^6*p^6-556*s^10*p^4-16
*s^2*p^8+64*p^9)*T^2+1/256*(5668704*p+23328*s^2+22248*s^2*p^2+54432*s^2*p-\
561168*s^4+1574640*p^2+233280*p^3+19440*p^4-44792*s^4*p^2-3440*s^4*p^3+1984*s^
6*p+24*s^6*p^2+280*s^2*p^4-8*s^6*p^3+2144*s^8*p+136*s^8*p^2+3704*s^2*p^3-\
259008*s^4*p+10176*s^6+8432*s^8-736*s^10+16*s^12+864*p^5+16*p^6-99*s^4*p^4-96*
s^10*p+8*s^2*p^5+8503056)^2:

##poly(wa/a+wb/b+wc/c):
wadaT:= (2*s^2+p+10)^4*(p+8)^4*s^4*T^4-8*s^2*(p+8)^2*(6561+2916*p+2709*s^2-3*s^6
*p^2-2*s^4*p^3-50*s^6*p-378*s^4*p-48*s^4*p^2+36*p^3+486*p^2+105*s^2*p^2+922*s^
2*p+p^4-966*s^4-198*s^6-11*s^8+4*s^2*p^3+s^10-2*s^8*p)*(2*s^2+p+10)^2*T^2-64*s
^5*(p+8)^4*(2*s^2+p+10)^3*T+612220032*p+568759968*s^2+445446864*s^4+238085568*
p^2+446357952*s^2*p+106718816*s^4*p^2+18883328*s^4*p^3+150208992*s^2*p^2+
33768672*s^6*p^2+3155040*s^2*p^4+5047424*s^6*p^3+19526400*s^8*p+4526048*s^8*p^
2+28097280*s^2*p^3+333623808*s^4*p+688747536+52907904*p^3+7348320*p^4+1182656*
s^10+267552*s^12+120390400*s^6*p+653184*p^5+16*p^8+1152*p^7+38784*s^14-4400*s^
16-352*s^18+16*s^20+36288*p^6+178775936*s^6+33729824*s^8+16*s^12*p^4+1994064*s
^4*p^4+423808*s^6*p^4-45408*s^10*p^2+4352*s^4*p^6+524672*s^8*p^3+30400*s^8*p^4
+259200*s^10*p+18944*s^6*p^5+125504*s^4*p^5+212672*s^2*p^5+7968*s^2*p^6+128*s^
2*p^7+18176*s^14*p+115200*s^12*p-18432*s^10*p^3+17440*s^12*p^2+704*s^8*p^5+64*
s^4*p^7+1024*s^12*p^3+2720*s^14*p^2-896*s^16*p+352*s^6*p^6-1888*s^10*p^4-64*s^
10*p^5+128*s^14*p^3-32*s^16*p^2-64*s^18*p:

##poly(IA/a+IB/b+IC/c):
IAdaT:= s^4*(p+8)^4*T^4-2*s^2*(p+8)^2*(p^2+2*s^2*p^2+18*p+30*s^2*p-4*s^4*p+115*s
^2+81+s^6-29*s^4)*T^2-8*s^3*(p+8)^4*T-18234*s^2-1630*s^2*p^2+4431*s^4+486*p^2+
36*p^3-8920*s^2*p+198*s^4*p^2+8*s^4*p^3-2624*s^6*p+p^4+2916*p-16*s^6*p^3+292*s
^8*p+20*s^8*p^2-132*s^2*p^3+1624*s^4*p+6561-6508*s^6+1071*s^8-58*s^10+s^12-8*s
^10*p-354*s^6*p^2-4*s^2*p^4:

##poly(a/IA+b/IB+c/IC):
adIAT:= (p+8)^2*T^4-2*(p+8)*(2*p+s^2*p+2*s^2+18)*T^2-8*s*(p+8)^2*T+s^2*(-388-4*p
^2-76*p+120*s^2+s^2*p^2+20*s^2*p-4*s^4):

##poly(ma/ra+mb/rb+mc/rc):
madraT:= 1/16*s^4*T^8-1/8*s^2*(-51*s^2+p^2+18*p+81-6*s^2*p+2*s^4)*T^6+1/16*(486*p
^2+6561+36*p^3+6*s^8-542*s^2*p^2+58*s^4*p^2+p^4+4347*s^4-14742*s^2-20*s^2*p^3-\
302*s^6-36*s^6*p+2916*p+1006*s^4*p-4896*s^2*p)*T^4+1/16*(-66*s^2*p^4-443610*s^
2+8*p^5+527796+368*p^4-4*s^10+36*s^8*p+286740*p+298*s^8-2398*s^2*p^3-196686*s^
2*p-32613*s^2*p^2+6772*p^3-1880*s^6*p+93384*s^4+136*s^4*p^3-110*s^6*p^2-8008*s
^6+31878*s^4*p+3612*s^4*p^2+62316*p^2)*T^2+1/16*(3240+1044*p+112*p^2+4*p^3-711
*s^2-161*s^2*p-9*s^2*p^2+49*s^4+6*s^4*p-s^6)^2:

##poly(ra/ma+rb/mb+rc/mc):
radmaT:= 1/256*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^
2+2916+972*p)^4*T^8+1/16*(6561+2916*p+486*p^2+36*p^3+p^4+4698*s^2+1368*s^2*p+
130*s^2*p^2+4*s^2*p^3+81*s^4+40*s^4*p+4*s^4*p^2-8*s^6)*(-4*s^6+12*s^4*p-36*s^4
+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^3*T^6+1/8*(114791256*
p+186831036*s^2+42984756*s^2*p^2+137098656*s^2*p+69542226*s^4+44641044*p^2+
9920232*p^3+1377810*p^4+10359468*s^4*p^2+1382136*s^4*p^3+1425168*s^6*p+460692*
s^6*p^2+774180*s^2*p^4+63688*s^6*p^3-44208*s^8*p+136*s^8*p^2+7461720*s^2*p^3+
41545224*s^4*p+1154412*s^6-160893*s^8-2832*s^10+128*s^12+122472*p^5+3*p^8+216*
p^7+6804*p^6+104250*s^4*p^4+4032*s^6*p^4-192*s^10*p^2+72*s^4*p^6+768*s^8*p^3+
48*s^8*p^4-1536*s^10*p+96*s^6*p^5+4224*s^4*p^5+47984*s^2*p^5+1644*s^2*p^6+24*s
^2*p^7+129140163)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+
108*p^2+2916+972*p)^2*T^4+(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^
2+4*p^3+108*p^2+2916+972*p)*(376572715308*p+619097941422*s^2+389056264398*s^2*
p^2+728350519320*s^2*p+454819430943*s^4+230127770466*p^2+85232507580*p^3+
21308126895*p^4+216990588312*s^4*p^2+59511215160*s^4*p^3+104628319488*s^6*p+
43116002244*s^6*p^2+26544415068*s^2*p^4+10404078264*s^6*p^3+2852062812*s^8*p+
1841614218*s^8*p^2+124542135468*s^2*p^3+468507048192*s^4*p+113299835724*s^6+
544270671*s^8-314528994*s^10-2025135*s^12+3788111448*p^5+3247695*p^8+46766808*
p^7+174600*s^14+2176*s^16+491051484*p^6-9360*s^12*p^4+10704248658*s^4*p^4+
1619564940*s^6*p^4-27413586*s^10*p^2+112945108*s^4*p^6+535328172*s^8*p^3+
87501351*s^8*p^4-188287416*s^10*p+168587280*s^6*p^5+1319634072*s^4*p^5+
3954865824*s^2*p^5+420262668*s^2*p^6+31848552*s^2*p^7+75264*s^14*p-6211368*s^
12*p+3689404*s^10*p^3-2448900*s^12*p^2+8623104*s^8*p^5+6628328*s^4*p^7-329472*
s^12*p^3-14784*s^14*p^2+2048*s^16*p+11728620*s^6*p^6+1531040*s^10*p^4+180320*s
^10*p^5-5632*s^14*p^3+512*s^16*p^2+1686582*s^2*p^8+160380*p^9+5832*s^4*p^9+
13752*s^6*p^8-384*s^14*p^4+9504*s^10*p^6+1152*s^12*p^5+16896*s^8*p^7+240*s^8*p
^8+64*s^12*p^6+525528*s^6*p^7+511400*s^8*p^6+255335*s^4*p^8+59432*s^2*p^9+192*
s^10*p^7+282429536481+108*p^11+5346*p^10+p^12+160*s^6*p^9+60*s^4*p^10+1254*s^2
*p^10+12*s^2*p^11)*T^2+(38263752*p+63536724*s^2+14483772*s^2*p^2+46399392*s^2*
p+23274054*s^4+14880348*p^2+3306744*p^3+459270*p^4+3444660*s^4*p^2+459528*s^4*
p^3+323568*s^6*p+140076*s^6*p^2+259020*s^2*p^4+20856*s^6*p^3-13392*s^8*p-200*s
^8*p^2+2504520*s^2*p^3+13843224*s^4*p-157788*s^6-23679*s^8-240*s^10+40824*p^5+
p^8+72*p^7+2268*p^6+34702*s^4*p^4+1344*s^6*p^4-64*s^10*p^2+24*s^4*p^6+256*s^8*
p^3+16*s^8*p^4-256*s^10*p+32*s^6*p^5+1408*s^4*p^5+16016*s^2*p^5+548*s^2*p^6+8*
s^2*p^7+43046721)^2:

##poly(wa/ra+wb/rb+wc/rc):
wadraT:= 1/16*(2*s^2+p+10)^4*T^4+1/2*(2*p^3+56*p^2+3*s^2*p^2+520*p+50*s^2*p+2*s^4
*p+205*s^2+13*s^4+1599-s^6)*(2*s^2+p+10)^2*T^2-4*(p+8)*(2*s^2+p+10)^3*T-282650
*s^2-32902*s^2*p^2+14735*s^4+112*p^2+4*p^3-152884*s^2*p+802*s^4*p^2+48*s^4*p^3
+1880*s^6*p+214*s^6*p^2+1040*p+8*s^6*p^3-48*s^8*p-2*s^8*p^2-3524*s^2*p^3+5696*
s^4*p+5460*s^6-241*s^8-26*s^10+s^12+s^4*p^4-4*s^10*p-4*s^2*p^5-188*s^2*p^4+
3201:

##poly(ra/IA+rb/IB+rc/IC):
radIAT:= (p+8)^2*T^4-2*(p+8)*(p^3+26*p^2+225*p-3*s^2*p-22*s^2+648)*T^2-8*s^2*(p+8
)*T+291600*p-29088*s^2-2502*s^2*p^2-13924*s^2*p+608*s^4+84321*p^2+12996*p^3+
1126*p^4+9*s^4*p^2-6*s^2*p^4-200*s^2*p^3+148*s^4*p+p^6-4*s^6+52*p^5+419904:

##poly(IA/ra+IB/rb+IC/rc):
IAdraT:= -1/16*s^2*T^4+1/8*(34*p+144-31*s^2-4*s^2*p+s^4+2*p^2)*T^2+1/2*(p+8)*T+
769/4*p+31/8*s^4-1249/16*s^2-5/4*s^2*p^2-79/4*s^2*p+24*p^2+p^3+1/2*s^4*p-1/16*
s^6+514:

##poly(IA/ha+IB/hb+IC/hc):
IAdhaT:= -s^2*T^4+(p+9)*(p+8)*T^2+(p+8)^2*T+1/4*(p+8)^2:

##poly(ha/IA+hb/IB+hc/IC):
hadIAT:= (p+8)^4*T^4-8*(p+8)^2*(p^2+18*p+81+s^2)*T^2-64*s^2*(p+8)^2*T+46656*p-\
6624*s^2-96*s^2*p^2-1600*s^2*p+16*s^4+7776*p^2+576*p^3+16*p^4+104976:

##poly(IA/ma+IB/mb+IC/mc):
IAdmaT:= 1/256*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^
2+2916+972*p)^4*T^8-1/16*(5103+1782*p+207*p^2+8*p^3+45*s^2-6*s^2*p-2*s^2*p^2-3
*s^4+4*s^4*p-s^6)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+
108*p^2+2916+972*p)^3*T^6+1/8*(36855324*p-14671854*s^2-1977642*s^2*p^2-8499816
*s^2*p+1407213*s^4+10685682*p^2+1651212*p^3+143427*p^4+68706*s^4*p^2+3768*s^4*
p^3+6432*s^6*p+1322*s^6*p^2-13564*s^2*p^4+16*s^6*p^3-452*s^8*p+44*s^8*p^2-\
231084*s^2*p^3+520776*s^4*p-17604*s^6-2547*s^8+18*s^10+3*s^12+6640*p^5+128*p^6
+72*s^4*p^4-24*s^10*p-320*s^2*p^5+52927587)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2
+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^2*T^4+(-4*s^6+12*s^4*p-36*s^4+15
*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*(4018048254*p+
91774172313*s^2+31592611764*s^2*p^2+81450287910*s^2*p-2671951212*s^4+
1609065567*p^2+368077932*p^3+52605855*p^4-689090247*s^4*p^2-116211960*s^4*p^3-\
74227266*s^6*p+6189102*s^6*p^2+967044573*s^2*p^4+3517336*s^6*p^3-14995818*s^8*
p-3605295*s^8*p^2+6995089584*s^2*p^3-2132041662*s^4*p-304085340*s^6-14660082*s
^8+1846062*s^10+7204*s^12+4810158*p^5+128*p^8+8968*p^7-2412*s^14+9*s^16+s^18+
274801*p^6-10830279*s^4*p^4+397039*s^6*p^4-15912*s^10*p^2-10680*s^4*p^6-301596
*s^8*p^3-6020*s^8*p^4+497010*s^10*p+17648*s^6*p^5-530316*s^4*p^5+85479186*s^2*
p^5+4717950*s^2*p^6+148672*s^2*p^7-470*s^14*p+23734*s^12*p-8904*s^10*p^3+3959*
s^12*p^2+128*s^8*p^5+40*s^12*p^3+38*s^14*p^2-12*s^16*p+256*s^6*p^6-312*s^10*p^
4+2048*s^2*p^8+4388108337)*T^2+(-481140*p+15590394*s^2+1931310*s^2*p^2+8698104
*s^2*p-1464399*s^4-109350*p^2-12420*p^3-705*p^4-42966*s^4*p^2-504*s^4*p^3-\
12768*s^6*p-2222*s^6*p^2+11716*s^2*p^4-80*s^6*p^3+428*s^8*p-4*s^8*p^2+213300*s
^2*p^3-461592*s^4*p-3348*s^6+2385*s^8-6*s^10-s^12-16*p^5+64*s^4*p^4+8*s^10*p+
256*s^2*p^5-846369)^2:

##poly(ma/IA+mb/IB+mc/IC):
madIAT:= (p+8)^4*T^8+(p+8)^3*(4*p^2+66*p-s^2*p-18*s^2+270)*T^6+1/8*(p+8)^2*(48*p^
4+1616*p^3-24*s^2*p^3-836*s^2*p^2+3*s^4*p^2+20376*p^2-8772*s^2*p+114048*p+124*
s^4*p-28980*s^2+960*s^4+239112-4*s^6)*T^4+1/16*(p+8)*(64*p^6+3296*p^5-48*s^2*p
^5+12*s^4*p^4-2512*s^2*p^4+70720*p^4+809216*p^3-49848*s^2*p^3+702*s^4*p^3-s^6*
p^3+13194*s^4*p^2+5208192*p^2-476160*s^2*p^2-86*s^6*p^2-1576*s^6*p+98052*s^4*p
-2207664*s^2*p+4*s^8*p+17877024*p-3992760*s^2+25567488+251352*s^4-7208*s^6+72*
s^8)*T^2+1/256*(93312+42768*p+7344*p^2+560*p^3+16*p^4-9540*s^2-2940*s^2*p-284*
s^2*p^2-8*s^2*p^3+312*s^4+52*s^4*p+s^4*p^2-4*s^6)^2:

##poly(HA/IA+HB/IB+HC/IC):
HAdIAT:= (16*(p+8)^2*T^4-8*(p+8)*(p^3+22*p^2+152*p-4*s^2*p+312-8*s^2)*T^2-16*(p+8
)^2*(p+10+2*s)*(p+10-2*s)*T+314368*p-64*s^6-77888*s^2-5536*s^2*p^2-33472*s^2*p
+3968*s^4+88448*p^2+13328*p^3+1136*p^4+48*s^4*p^2-12*s^2*p^4-416*s^2*p^3+832*s
^4*p+52*p^5+p^6+466944)*(16*(p+8)^2*T^4-8*(p+8)*(p^3+22*p^2+152*p-4*s^2*p+312-\
8*s^2)*T^2+16*(p+8)^2*(p+10+2*s)*(p+10-2*s)*T+314368*p-64*s^6-77888*s^2-5536*s
^2*p^2-33472*s^2*p+3968*s^4+88448*p^2+13328*p^3+1136*p^4+48*s^4*p^2-12*s^2*p^4
-416*s^2*p^3+832*s^4*p+52*p^5+p^6+466944):

##poly(ra/wa+rb/wb+rc/wc):
radwaT:= 16*(p+8)^2*T^4-8*(p+8)*(p^3+28*p^2-3*s^2*p+260*p-26*s^2+798)*T^2-16*(p+8
)*(2*s^2+p+10)*T+417040*p-220*s^2*p^3-3004*s^2*p^2-18108*s^2*p-40676*s^2+728*s
^4+112512*p^2+16164*p^3+1304*p^4-6*s^2*p^4+643200-4*s^6+9*s^4*p^2+p^6+164*s^4*
p+56*p^5:

##poly(rb*rc/wb/wc+rc*ra/wc/wa+ra*rb/wa/wb):
rbmrcdwbdwcT:= 4*(p+8)^4*T^4+1/2*(p+8)^2*(2*p^3+56*p^2+3*s^2*p^2+520*p+50*s^2*p+2*s^4*p
+205*s^2+13*s^4+1599-s^6)*T^2-1/2*(p+8)^2*(2*s^2+p+10)^2*T-16451/32*s^2*p^2-\
38221/16*s^2*p+7/4*p^2+1/16*p^3-141325/32*s^2+14735/64*s^4-13/32*s^10+1/64*s^
12+1365/16*s^6-241/64*s^8+65/4*p+107/32*s^6*p^2-47/16*s^2*p^4-3/4*s^8*p-1/32*s
^8*p^2-881/16*s^2*p^3+89*s^4*p+1/8*s^6*p^3+1/64*s^4*p^4-1/16*s^10*p-1/16*s^2*p
^5+401/32*s^4*p^2+3/4*s^4*p^3+235/8*s^6*p+3201/64:

##poly(b*c/mb/mc+c*a/mc/ma+a*b/ma/mb):
bmcdmbdmcT:= 1/16*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2
+2916+972*p)^2*T^4-2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p
^3+108*p^2+2916+972*p)*(4*p^3+108*p^2-3*s^2*p^2+972*p-56*s^2*p+12*s^4*p+2916+
92*s^4-252*s^2-4*s^6)*T^2+32*s^2*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+
360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T+373248*s^2+90699264*p+25194240*
p^2+3732480*p^3+311040*p^4+162816*s^6+134912*s^8-11776*s^10+256*s^12-716672*s^
4*p^2-55040*s^4*p^3+355968*s^2*p^2+870912*s^2*p+4480*s^2*p^4-8978688*s^4+2176*
s^8*p^2+59264*s^2*p^3-4144128*s^4*p-128*s^6*p^3-1584*s^4*p^4-1536*s^10*p+128*s
^2*p^5+13824*p^5+256*p^6+31744*s^6*p+384*s^6*p^2+136048896+34304*s^8*p:

##poly(mb*mc/b/c+mc*ma/c/a+ma*mb/a/b):
mbmmcdbdcT:= s^2*(p+8)^4*T^4+1/8*(p+8)^2*(5832+1944*p+216*p^2+8*p^3-4536*s^2-960*s^2*
p-51*s^2*p^2+312*s^4+24*s^4*p-8*s^6)*T^2+1/8*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+
15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T-153819*p-55773/16*p^
3-63/16*p^5-2965/16*p^4+100953/16*s^2*p^2+41121*s^2*p+828*s^6-16*s^8-14148*s^4
-524151/16*p^2+127*s^6*p+100116*s^2-288684-6153/16*s^4*p^2-4077*s^4*p+63/16*s^
6*p^2+2781/256*s^2*p^4-189/16*s^4*p^3+857/2*s^2*p^3:

##poly(b*c/wb/wc+c*a/wc/wa+a*b/wa/wb):
bmcdwbdwcT:= 256*s^8*(p+8)^4*T^4-32*s^4*(p+8)^2*(6561+2916*p+2709*s^2-3*s^6*p^2-2*s^4
*p^3-50*s^6*p-378*s^4*p-48*s^4*p^2+36*p^3+486*p^2+105*s^2*p^2+922*s^2*p+p^4-\
966*s^4-198*s^6-11*s^8+4*s^2*p^3+s^10-2*s^8*p)*T^2-32*s^6*(p+8)^4*(2*s^2+p+10)
^2*T+27897372*s^2*p+38263752*p+9388062*s^2*p^2+3306744*p^3+35547498*s^2+
27840429*s^4+14880348*p^2+73916*s^10+16722*s^12+6669926*s^4*p^2+1180208*s^4*p^
3+7524400*s^6*p+2110542*s^6*p^2+197190*s^2*p^4+1220400*s^8*p+282878*s^8*p^2+
1756080*s^2*p^3+459270*p^4+11173496*s^6+2108114*s^8+s^12*p^4+124629*s^4*p^4+
26488*s^6*p^4-2838*s^10*p^2+272*s^4*p^6+32792*s^8*p^3+1900*s^8*p^4+16200*s^10*
p+1184*s^6*p^5+7844*s^4*p^5+13292*s^2*p^5+498*s^2*p^6+8*s^2*p^7+1136*s^14*p+
7200*s^12*p-1152*s^10*p^3+1090*s^12*p^2+44*s^8*p^5+4*s^4*p^7+64*s^12*p^3+170*s
^14*p^2-56*s^16*p+22*s^6*p^6-118*s^10*p^4-4*s^10*p^5+8*s^14*p^3-2*s^16*p^2-4*s
^18*p+40824*p^5+p^8+72*p^7+2424*s^14-275*s^16-22*s^18+s^20+2268*p^6+43046721+
20851488*s^4*p+315464*s^6*p^3:

##poly(wb*wc/b/c+wc*wa/c/a+wa*wb/a/b):
wbmwcdbdcT:= (p+8)^2*(2*s^2+p+10)^4*T^4+32*(p+8)*(2*p^2-s^4*p+36*p+3*s^2*p-6*s^4+162+
28*s^2)*(2*s^2+p+10)^2*T^2-512*s^2*(p+8)^2*(2*s^2+p+10)^2*T+256*s^2*(108*s^4*p
-92*p^2-700*p+s^6*p^2-1764+2704*s^2-4*s^8+105*s^2*p^2+456*s^4+80*s^6+6*s^4*p^2
+20*s^6*p+4*s^2*p^3-4*p^3+924*s^2*p):

##poly(b*c/IB/IC+c*a/IC/IA+a*b/IA/IB):
bmcdIBdICT:=(p+8)^4*T^4-2*(p+8)^2*(p^2+2*s^2*p^2+18*p+30*s^2*p-4*s^4*p+115*s^2+81+s
^6-29*s^4)*T^2-8*s^2*(p+8)^4*T-1630*s^2*p^2-8920*s^2*p+486*p^2+36*p^3-18234*s^
2+4431*s^4-6508*s^6+1071*s^8+p^4+6561+2916*p+8*s^4*p^3-2624*s^6*p-354*s^6*p^2-\
4*s^2*p^4+292*s^8*p+20*s^8*p^2-132*s^2*p^3+1624*s^4*p-16*s^6*p^3-8*s^10*p-58*s
^10+s^12+198*s^4*p^2:## 3.028

##poly(IB*IC/b/c+IC*IA/c/a+IA*IB/a/b):
IBmICdbdcT:=s^2*(p+8)^2*T^4-2*(p+8)*(2*p+s^2*p+2*s^2+18)*T^
2-8*(p+8)^2*T-388-4*p^2-76*p+120*s^2+s^2*p^2+20*s^2*p-4*s^4: ##2.692

##poly(rb*rc/mb/mc+rc*ra/mc/ma+ra*rb/ma/mb):
rbmrcdmbdmcT:=1/16*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^2
*T^4+4*s^2*(-51*s^2+p^2+18*p+81-6*s^2*p+2*s^4)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*
p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T^2+32*s^4*(-4*s^6+12*s^4*p-\
36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T-256*s^6*(3240
+1044*p+112*p^2+4*p^3-711*s^2-161*s^2*p-9*s^2*p^2+49*s^4+6*s^4*p-s^6): ##7.595

##poly(mb*mc/rb/rc+mc*ma/rc/ra+ma*mb/ra/rb):
mbmmcdrbdrcT:=256*s^8*T^4-32*s^4*(6561+2916*p+486*p^2+36*p^3+p^4+4698*s^2+1368*s^2*p+130*s^
2*p^2+4*s^2*p^3+81*s^4+40*s^4*p+4*s^4*p^2-8*s^6)*T^2+32*s^4*(-4*s^6+12*s^4*p-\
36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T+14483772*s^2*
p^2+46399392*s^2*p+63536724*s^2+14880348*p^2+3306744*p^3+459270*p^4+23274054*s
^4-23679*s^8-240*s^10+3444660*s^4*p^2-157788*s^6+323568*s^6*p+140076*s^6*p^2+
259020*s^2*p^4-13392*s^8*p-200*s^8*p^2+2504520*s^2*p^3+13843224*s^4*p+20856*s^
6*p^3+34702*s^4*p^4+1344*s^6*p^4-64*s^10*p^2+24*s^4*p^6+459528*s^4*p^3+16*s^8*
p^4-256*s^10*p+32*s^6*p^5+1408*s^4*p^5+16016*s^2*p^5+548*s^2*p^6+8*s^2*p^7+
40824*p^5+p^8+72*p^7+2268*p^6+43046721+256*s^8*p^3+38263752*p:## 110.204

##poly(HB*HC/IB/IC+HC*HA/IC/IA+HA*HB/IA/IB):
HBmHCdIBdICT:=-64*(p+8)^4*T^4-8*(p+8)^2*(2*p^5-s^2*p^4+87*p^4-56*s^2*p^3+1504*p^3-992
*s^2*p^2+8*s^4*p^2+12904*p^2-7136*s^2*p+192*s^4*p+54880*p-16*s^6+976*s^4+92400
-18224*s^2)*T^2+8*(p+8)^4*(p+10+2*s)^2*(p+10-2*s)^2*T-519200000*p+673193600*s^
2-122287040*s^4+271166656*s^2*p^2-8983000*p^4+9566976*s^6-383936*s^8+641784320
*s^2*p-64*s^12-31563776*s^4*p^2-5837376*s^4*p^3+5613568*s^6*p+1329920*s^6*p^2+
10490336*s^2*p^4-150784*s^8*p-21056*s^8*p^2+66630976*s^2*p^3-94948864*s^4*p+
161472*s^6*p^3-651920*s^4*p^4+7808*s^10+64*s^10*p^2-1772*s^4*p^6-1216*s^8*p^3-\
24*s^8*p^4+1536*s^10*p+336*s^6*p^5-44480*s^4*p^5+1097104*s^2*p^5+76196*s^2*p^6
+3388*s^2*p^7-36*s^4*p^7+4*s^6*p^6+10464*s^6*p^4-962720*p^5-337/4*p^8-3152*p^7
-68732*p^6-p^9+175/2*s^2*p^8-1/4*s^4*p^8+s^2*p^9-223000000*p^2-55840000*p^3-\
537000000:## 37.752

##poly(Hb*Hc/IB/IC+Hc*Ha/IC/IA+Ha*Hb/IA/IB):
HbmHcdIBdICT:=-64*(p+8)^6*T^4-8*(p+8)^3*(192+39*p+2*p^2-s^2*p-8*s^2)*(p
+10+2*s)^2*(p+10-2*s)^2*T^2+8*(p+8)^2*(p+10+2*s)^4*(p+10-2*s)^4*T+1/4*(-4*p^3+
4*s^2*p^3-113*p^2-s^4*p^2+94*s^2*p^2-1056*p+720*s^2*p-16*s^4*p+1856*s^2-3264-\
64*s^4)*(p+10+2*s)^4*(p+10-2*s)^4:## 149.488

##poly(hb*hc/mb/mc+hc*ha/mc/ma+ha*hb/ma/mb):
hbmhcdhbdhcT:=1/16*(p+8)^4*(-4*s^6+12*s^4*p-36
*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)^2*T^4+64*s^2*(p+8
)^2*(s^4-6*s^2-2*s^2*p+81+p^2+18*p)*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2
*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T^2+2048*s^4*(p+8)^2*(-4*s^6+12*s^4*p-36
*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T-262144*s^6*(p+9
-s^2)^2:##17.016

##poly(mb*mc/hb/hc+mc*ma/hc/ha+ma*mb/ha/hb):
mbmmcdhbdhcT:=65536*s^8*T^4-512*s^4*(81-14*s^2+s^4+18*p-2*s^2*p+p^2)*(p^2
+18*p+18*s^2-2*s^2*p+s^4+81)*T^2+128*s^4*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^
2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T+31568616*s^2*p^2+38263752
*p+14880348*p^2+96000552*s^2*p+125183880*s^2-6309576*s^6+1019142*s^8-6216*s^10
-2212*s^12+11994372*s^4*p^2+1638384*s^4*p^3-4085208*s^6*p-1019088*s^6*p^2+
633240*s^2*p^4+392472*s^8*p+47908*s^8*p^2+5770440*s^2*p^3+46584072*s^4*p-\
123440*s^6*p^3+125052*s^4*p^4-7288*s^6*p^4+2152*s^10*p^2+84*s^4*p^6+1560*s^8*p
^3-34*s^8*p^4+9144*s^10*p-168*s^6*p^5+5048*s^4*p^5+41720*s^2*p^5+1528*s^2*p^6+
24*s^2*p^7-8*s^14*p-488*s^12*p+104*s^10*p^3-4*s^12*p^2+40824*p^5+p^8+72*p^7+8*
s^14+s^16+2268*p^6+75066588*s^4+43046721+3306744*p^3+459270*p^4:## 120.418

##poly(hb*hc/IB/IC+hc*ha/IC/IA+ha*hb/IA/IB):
hbmhcdIBdICT:=(p+8)^6*T^4-64*s^2*(p+9)*(p+8)^3*T^2-512*s^4*(p+8)^2*T-1024*s^6:## 15.913

##poly(mb*mc/wb/wc+mc*ma/wc/wa+ma*mb/wa/wb):
mbmmcdwbdwcT:=-4096*s^8*(p+8)^4*T^4+32*s^4*(p+8)^2*(6561+65205*s^2-54630*s^4+2458*s^6
+21*s^8+s^10+2916*p+27450*s^2*p-17978*s^4*p+366*s^6*p-2*s^8*p+486*p^2+4333*s^2
*p^2-1952*s^4*p^2+9*s^6*p^2+36*p^3+304*s^2*p^3-70*s^4*p^3+p^4+8*s^2*p^4)*T^2-8
*s^4*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p
^2+2916+972*p)*(2*s^2+p+10)^2*T-4782969/2*p+37146195/16*s^4+116072109/8*s^2*p^
2+147655305/4*s^2*p+328017195/8*s^2+1493289/8*s^4*p^2-3720087/4*p^2-413343/2*p
^3-229635/8*p^4+3638205/8*s^2*p^4+26266838*s^6*p^3-114711471*s^8*p-240432611/8
*s^8*p^2+6504543/2*s^2*p^3+1198962*s^4*p+1181879505/2*s^6-1455181929/8*s^8+
60585585/4*s^10-5214121/8*s^12-6225*s^4*p^3+449081793*s^6*p+1167125301/8*s^6*p
^2+5662035/2*s^6*p^4+12880863/8*s^10*p^2-36*s^4*p^6-8374787/2*s^8*p^3-1309011/
4*s^8*p^4+15696495/2*s^10*p+365353/2*s^6*p^5-2655/4*s^4*p^5+162505/4*s^2*p^5+
18115/8*s^2*p^6+72*s^2*p^7+69*s^14*p-244854*s^12*p+326847/2*s^10*p^3-253229/8*
s^12*p^2-54413/4*s^8*p^5-3/4*s^4*p^7-1542*s^12*p^3-1729/8*s^14*p^2+159/2*s^16*
p+52281/8*s^6*p^6+65619/8*s^10*p^4+651/4*s^10*p^5-13*s^14*p^3+21/8*s^16*p^2+1/
4*s^18*p-5103/2*p^5-1/16*p^8-9/2*p^7+14449/2*s^14+5907/16*s^16-21/8*s^18-1/16*
s^20-567/4*p^6-43046721/16+s^2*p^8+100*s^6*p^7-235*s^8*p^6-281/16*s^12*p^4-\
84957/16*s^4*p^4:## 46.056

##poly(wb*wc/mb/mc+wc*wa/mc/ma+wa*wb/ma/mb):
wbmwcdmbdmcT:=1/16*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+
2052*s^2+4*p^3+108*p^2+2916+972*p)^2*(2*s^2+p+10)^4*T^4-32*s^2*(p+8)*(2*p^2+4*
s^2*p^2+36*p+162+59*s^2*p+204*s^2-s^4*p-22*s^4)*(-4*s^6+12*s^4*p-36*s^4+15*s^2
*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*(2*s^2+p+10)^2*T^2+2048*s^4*
(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+
2916+972*p)*(2*s^2+p+10)^2*T+4096*s^6*(p+8)^2*(16*s^2*p^4-16*p^4-8*s^4*p^3-692
*p^3+748*s^2*p^3+12761*s^2*p^2-330*s^4*p^2+s^6*p^2-10972*p^2+94076*s^2*p-4468*
s^4*p+52*s^6*p-75996*p+400*s^6-18808*s^4-4*s^8+253008*s^2-194724):## 64.312

##poly(HB*HC/mb/mc+HC*HA/mc/ma+HA*HB/ma/mb):
HBmHCdmbdmcT:=1/32*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+
972*p)^2*T^4-1/8*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+
108*p^2+2916+972*p)*(124320*p-2224*s^2*p^2-15680*s^2*p-40416*s^2+2016*s^4+
26036*p^2+2728*p^3+143*p^4+20*s^4*p^2-3*s^2*p^4-136*s^2*p^3+416*s^4*p+3*p^5+
237600-32*s^6)*T^2+1/4*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+
2052*s^2+4*p^3+108*p^2+2916+972*p)*(p+10+2*s)^2*(p+10-2*s)^2*T+143827200*s^2+
1360800000*p+49760352*s^2*p^2+136460000*p^3+21207000*p^4+3090176*s^4*p^2+
786368*s^4*p^3-2911744*s^6*p-724992*s^6*p^2+1505672*s^2*p^4-91584*s^6*p^3+
153856*s^8*p+21536*s^8*p^2+10974784*s^2*p^3+5365248*s^4*p-4682240*s^6+393088*s
^8-12032*s^10+128*s^12+108168*s^4*p^4-6072*s^6*p^4-96*s^10*p^2+348*s^4*p^6+
1248*s^8*p^3+24*s^8*p^4-2304*s^10*p-192*s^6*p^5+8400*s^4*p^5+131632*s^2*p^5+
7164*s^2*p^6+222*s^2*p^7+6*s^4*p^7-2*s^6*p^6+2196480*p^5+174*p^8+6726*p^7+
151618*p^6+2*p^9+3*s^2*p^8+128259840*s^2*p+1458000000+1322880*s^4+564300000*p^
2:## 82.910

##poly(mb*mc/IB/IC+mc*ma/IC/IA+ma*mb/IA/IB):
mbmmcdIBdICT:=(p+8)^4*T^4+1/8*(p+8)^2*(5103+1782*p+207*p^2+8*p^3+45*s^2-6*s^2*p-2*s^2
*p^2-3*s^4+4*s^4*p-s^6)*T^2+1/8*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360
*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T-7795197/128*s^2+120285/64*p+54675/
128*p^2+3105/64*p^3+705/256*p^4+1464399/256*s^4+837/64*s^6-2385/256*s^8+3/128*
s^10+1/256*s^12+21483/128*s^4*p^2-965655/128*s^2*p^2-1087263/32*s^2*p+1111/128
*s^6*p^2-2929/64*s^2*p^4+5/16*s^6*p^3-107/64*s^8*p+1/64*s^8*p^2-53325/64*s^2*p
^3+57699/32*s^4*p+1/16*p^5-1/4*s^4*p^4-1/32*s^10*p-s^2*p^5+63/32*s^4*p^3+399/8
*s^6*p+846369/256:## 6.442


##poly(IB*IC/mb/mc+IC*IA/mc/ma+IA*IB/ma/mb):
IBmICdmbdmcT:=1/16*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+
2052*s^2+4*p^3+108*p^2+2916+972*p)^2*T^4-2*(p+8)*(4*p^2+66*p-s^2*p-18*s^2+270)
*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*
p)*T^2+32*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+
108*p^2+2916+972*p)*T+16*(p+8)^2*(93312+42768*p+7344*p^2+560*p^3+16*p^4-9540*s
^2-2940*s^2*p-284*s^2*p^2-8*s^2*p^3+312*s^4+52*s^4*p+s^4*p^2-4*s^6):## 8.268

##poly(Hb*Hc/mb/mc+Hc*Ha/mc/ma+Ha*Hb/ma/mb):
HbmHcdmbdmcT:=1/32*(p+8)^4*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p
^2+2916+972*p)^2*T^4-1/8*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+
2052*s^2+4*p^3+108*p^2+2916+972*p)*(3*p^3+79*p^2+696*p+2052-3*s^2*p^2-56*s^2*p
-216*s^2+4*s^4)*(p+10+2*s)^2*(p+10-2*s)^2*T^2+1/4*(p+8)^2*(-4*s^6+12*s^4*p-36*
s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*(p+10+2*s)^4*(p+10
-2*s)^4*T-2*(-96*s^4+208*s^4*p+51*s^4*p^2+3*s^4*p^3+46656+27216*p+6345*p^2+739
*p^3+43*p^4+p^5+36432*s^2+16368*s^2*p+2773*s^2*p^2+210*s^2*p^3+6*s^2*p^4-48*s^
6-16*s^6*p-s^6*p^2)*(p+10+2*s)^4*(p+10-2*s)^4:## 270.011

##poly(HB*HC/wb/wc+HC*HA/wc/wa+HA*HB/wa/wb):
HBmHCdwbdwcT:=-16384*s^8*(p+8)^4*T
^4+128*s^4*(p+8)^2*(504000*p+242272*s^2*p^2+916640*s^2*p+1445200*s^2+33696*s^4
+130600*p^2+18040*p^3+1401*p^4+4000*s^6-688*s^8+16*s^10+2880*s^4*p^2+232*s^4*p
^3+2528*s^6*p+512*s^6*p^2+2703*s^2*p^4+40*s^6*p^3-160*s^8*p-8*s^8*p^2+34136*s^
2*p^3+15968*s^4*p+58*p^5+p^6+7*s^4*p^4+s^6*p^4+114*s^2*p^5+2*s^2*p^6+810000)*T
^2+32*s^4*(p+8)^4*(p+10+2*s)^2*(2*s^2+p+10)^2*(p+10-2*s)^2*T+336294000000*s^2-\
204120000000*p+274563000000*s^2*p^2-40217400000*p^3-9377575000*p^4+93798310400
*s^6-116397000000*p^2-621367040*s^10+52128640*s^12+97444745600*s^4*p^2+
32261975040*s^4*p^3+118773908480*s^6*p+449850400000*s^2*p+25069396000*s^2*p^4+
144138360000*s^4-4901315584*s^8*p-1794428672*s^8*p^2+101159680000*s^2*p^3+
176079104000*s^4*p-5490840704*s^8-1554554000*p^5-4316641/4*p^8-16676420*p^7+
320000*s^14-150336*s^16+5504*s^18-64*s^20-187866700*p^6+82464*s^12*p^4+
7102575776*s^4*p^4+5364819296*s^6*p^4-298501888*s^10*p^2+119694324*s^4*p^6-\
319196032*s^8*p^3-17041488*s^8*p^4-654350848*s^10*p+857827536*s^6*p^5+
1092068336*s^4*p^5+4403978640*s^2*p^5+562517484*s^2*p^6+52651544*s^2*p^7+
635904*s^14*p+36890624*s^12*p-77078528*s^10*p^3+10417792*s^12*p^2+4244176*s^8*
p^5+9353572*s^4*p^7+1431040*s^12*p^3+285312*s^14*p^2-75264*s^16*p+97827852*s^6
*p^6-12327968*s^10*p^4+68199449984*s^6*p^2+55296*s^14*p^3+23447875584*s^6*p^3+
1280*s^18*p+7170009/2*s^2*p^8-49649*p^9+18570*s^4*p^9+452463*s^6*p^8+5280*s^14
*p^4+64*s^18*p^2-78716*s^10*p^6-960*s^16*p^3-1584*s^12*p^5+110836*s^8*p^7+
26401/4*s^8*p^8-24*s^16*p^4-452*s^12*p^6+7957472*s^6*p^7+1044892*s^8*p^6+
2043265/4*s^4*p^8+173208*s^2*p^9+240*s^14*p^5-2808*s^10*p^7-29*p^11-3083/2*p^
10-1/4*p^12+777/2*s^6*p^10+4*s^6*p^11+17128*s^6*p^9-1/4*s^12*p^8+809/2*s^4*p^
10+4*s^4*p^11+s^2*p^12+11275/2*s^2*p^10+111*s^2*p^11-87/2*s^10*p^8+215*p^9*s^8
-20*s^12*p^7+3*p^10*s^8+4*s^14*p^6-1251152*s^10*p^5-164025000000-13248*s^16*p^
2:## 384.128

##poly(wb*wc/IB/IC+wc*wa/IC/IA+wa*wb/IA/IB):
wbmwcdIBdICT:=(2*s^2+p+10)*T-16*s^2:## .127

##poly(IB*IC/wb/wc+IC*IA/wc/wa+IA*IB/wa/wb):
IBmICdwbdwcT:=-4*s^2*T+5*s^2+p+9:## .119

##poly(rb*rc/IB/IC+rc*ra/IC/IA+ra*rb/IA/IB):
rbmrcdIBdICT:=(p+8)^4*T^4-2*s^2*(p+8)^2*(34*p+144-31*s^2-4*s^2*p+s^4+2*p^2)*T^2-8*s^4*(p+8)^2*T-s
^6*(16*p^3-20*s^2*p^2+384*p^2+8*s^4*p-316*s^2*p+3076*p-s^6+62*s^4-1249*s^2+
8224):## 2.840

##poly(IB*IC/rb/rc+IC*IA/rc/ra+IA*IB/ra/rb):
IBmICdrbdrcT:=s^8*T^4-2*s^4*(p+8)*(p^3+26*p^2+225*p-3*s^2*p-22*s^2+648)*T^2-\
8*s^4*(p+8)^2*T+(p+8)^2*(p^6+52*p^5+1126*p^4-6*s^2*p^4-200*s^2*p^3+12996*p^3+
84321*p^2-2502*s^2*p^2+9*s^4*p^2+291600*p+148*s^4*p-13924*s^2*p-29088*s^2+
419904-4*s^6+608*s^4):## 4.203

##poly(1/wa^2+1/wb^2+1/wc^2):
dwap2T:=s^2*(p+8)*T-1/4*s^2*p-5/2*s^2-9/2-1/2*p:

##poly(Ha^2/wa^2+Hb^2/wb^2+HC^2/wc^2):
Hap2dwap2T := -16*s^2*(p+8)^2*T+2*p^4+s^2*p^4+42*s^2*p^3+74*p^3-4*s^4*p^2+636*s^2*p^2+
1024*p^2-88*s^4*p+4176*s^2*p+6280*p-384*s^4+10176*s^2+14400:

##poly(HA^2/wa^2+HB^2/wb^2+HC^2/wc^2):
HAp2dwap2T := 4*s^2*(p+8)*T+s^4*p+6*s^4-1/4*s^2*p^3-13/2*s^2*p^2-1/2*p^3-59*s^2*p-188*
s^2-450-29/2*p^2-140*p:

##poly(Hb*Hc/wb/wc+Hc*Ha/wc/wa+Ha*Hb/wa/wb):
HbmHcdwbdwcT := s^8*(p+8)^6*T^4-1/128*s^4*(p+8)^3*(648+2456*s^2-232*s^4+66*s^2*p^2+225*p
+26*p^2+8*s^6+p^3+703*s^2*p+s^6*p+2*s^2*p^3-17*s^4*p)*(p+10+2*s)^2*(2*s-p-10)^
2*T^2-1/512*s^4*(p+8)^2*(2*s^2+p+10)^2*(p+10+2*s)^4*(2*s-p-10)^4*T+1/65536*(
291600*p-2577024*s^2-643136*s^4+84321*p^2+12996*p^3-440002*s^2*p^2-1647712*s^2
*p+1126*p^4-2834176*s^6-8256*s^8+2432*s^10+64*s^12-94817*s^4*p^2-11336*s^4*p^3
-1270336*s^6*p-228444*s^6*p^2-5078*s^2*p^4-20512*s^6*p^3-22544*s^8*p-5377*s^8*
p^2-62880*s^2*p^3-392976*s^4*p+52*p^5-674*s^4*p^4-914*s^6*p^4+30*s^10*p^2-444*
s^8*p^3-12*s^8*p^4+672*s^10*p-16*s^6*p^5-16*s^4*p^5-220*s^2*p^5-4*s^2*p^6+16*s
^12*p+s^12*p^2+p^6+419904)*(p+10+2*s)^4*(2*s-p-10)^4:##3418.77s/2

##poly(hb*hc/mb/mc+hc*ha/mc/ma+ha*hb/ma/mb):
hbmhcdmbdmcT:= 1/16*(p+8)^4*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3
+108*p^2+2916+972*p)^2*T^4+64*s^2*(p+8)^2*(s^4-6*s^2-2*s^2*p+81+p^2+18*p)*(-4*
s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3+108*p^2+2916+972*p)*T^
2+2048*s^4*(p+8)^2*(-4*s^6+12*s^4*p-36*s^4+15*s^2*p^2+360*s^2*p+2052*s^2+4*p^3
+108*p^2+2916+972*p)*T-262144*s^6*(p+9-s^2)^2:

##poly(ha^2/wa^2+hb^2/wb^2+hc^2/wc^2):
hap2dwap2T:= (p+8)^2*T-4*s^2-84-18*p-p^2:

##poly(hb*hc/wb/wc+hc*ha/wc/wa+ha*hb/wa/wb):
hbmhcdwbdwcT := (p+8)^6*T^4+2*(p+8)^3*(2*p^2-5*s^2*p+39*p-64*s^2+192)*T^2-8*(p+8)^2*(2*s
^2+p+10)^2*T+4*p^3+1056*p-11456*s^2*p+9*s^4*p^2-36*s^2*p^3+3264+288*s^4*p+2112
*s^4-39616*s^2-1110*s^2*p^2+113*p^2-64*s^6:

##poly(wa^2/IA^2+wb^2/IB^2+wc^2/IC^2):
wap2dIAp2T:= (2*s^2+p+10)^2*T-36*s^4-72*p-324-8*s^2*p-40*s^2-4*p^2:

##poly(ra^2/wa^2+rb^2/wb^2+rc^2/wc^2):
rap2dwap2T := -4*(p+8)*T+p^3+28*p^2-3*s^2*p+260*p-26*s^2+798:

##poly(IA^2/wa^2+IB^2/wb^2+IC^2/wc^2):
IAp2dwap2T:= 2*s^2*T-3*s^2+p+9:

##poly(IB*IC/hb/hc+IC*IA/hc/ha+IA*IB/ha/hb):
IBmICdhbdhcT := 256*s^8*T^4-32*s^4*(p+8)^2*(p^2+18*p+81+s^2)*T^2-32*s^4*(p+8)^4*T+(p+8)^
4*(p^4+36*p^3-6*s^2*p^2+486*p^2-100*s^2*p+2916*p-414*s^2+6561+s^4):

##poly(wb*wc/hb/hc+wc*wa/hc/ha+wa*wb/ha/hb):
wbmwcdhbdhcT:= (2*s^2+p+10)^4*T^4-2*(p+8)^2*(p^2+18*p+84+4*s^2)*(2*s^2+p+10)^2*T^2
-8*(p+8)^4*(2*s^2+p+10)^2*T+(5040*p+712*p^2+p^4+13200-12*s^2*p^2+44*p^3-1376*s^2
-272*s^2*p+16*s^4)*(p+8)^4:

##poly(wa^2/ha^2+wb^2/hb^2+wc^2/hc^2):
wap2dhap2T:= 1/2*(2*s^2+p+10)^2*T+1/2*(p+8)*(2*p^2-5*s^2*p+39*p-64*s^2+192):

##poly(ma^2/wa^2+mb^2/wb^2+mc^2/wc^2):
map2dwap2T:= 4*s^2*(p+8)*T+s^2*p^2+1/2*p^2+9*p-1/4*s^4*p+59/4*s^2*p+81/2-11/2*s^4+51*
s^2:


##poly(FA+FB+FC):

ctest:=proc(expr1,expr2,cstr)
   local i,po1,po2,ret,cs,ns:
   global gg,hh,aa;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:

   if nargs=3 then
      print(`Start to solve the left polynomial  `,time());
      po1:=psTpoly(expr1):
      print(`Start to solve the right polynomial  `,time());
      po2:=psTpoly(expr2):
   elif nargs=5 then
      print(`Start to solve the left polynomial  `,time());
      po1:=psTpoly(expr1,x);
      print(`Start to solve the right polynomial  `,time());
      po2:=psTpoly(expr2,x);
   else
   	print(`invalid arguments in ctest procedure.`);
   fi;
   cs:=cstr:
   ns:=nops(cs):
   for i to ns do 
   	if type(cs[i],`<`) or type(cs[i],`<=`) then 
   		cs:=subsop(i=primpart(solve(psTpoly(rhs(cs[i])-lhs(cs[i])),T)),cs)
   	else
   		cs:=subsop(i=primpart(solve(psTpoly(cs[i]),T)),cs)
   	fi;
   od:

   cs:=subs(q=s^2-4*p-27,cs);
   if has(po1,{q}) then po1:=subs(q=s^2-4*p-27,po1);fi;
   if has(po2,{q}) then po2:=subs(q=s^2-4*p-27,po2);fi;
   print(`LpolypsT:  length= `,nops(po1),` T degree := `,degree(po1,T));
   print(`RpolypsT:  length= `,nops(po2),` T degree := `,degree(po2,T));

   if nargs=3 then ret:=cie2(po1,po2,p,s,T,cs);
   elif nargs=5 then ret:=cie2(po1,po2,p,s,T,cs,args[4],args[5]):
   fi;
   RETURN(ret)
end:

cie2:=proc(poly1,poly2,par1,par2,var,cstr)
   local p1,p2,po1,po2,res,su,fa,rs,i,fb,bz,dt,fac,fc,j,fd,ret,k,fe,temp,t,F,nd,
         n,m,rr,rs1,rs2,nr,ff,fs,cs,lc,nf,df,tp,tps,ma,mi,fq,r1,r2,tts,N,xfp,xp,co,
         np,fh,nq,tq,tqs,fg,ng,pr,ns,eq1,eq2,flist,ml,dp,lp,nn,ex,ep1,ep2,sturmlist:

   global gg,hh,aa;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:

   po1:=poly1:
   po2:=poly2:

   p1:=subs(var=sqrt(var),po1):
   p2:=subs(var=sqrt(var),po2):
   p1:=collect(p1,var);p2:=collect(p2,var);

   while type(p1,polynom) and type(p2,polynom) do
      po1:=p1;po2:=p2;
      p1:=subs(var=sqrt(var),po1):
      p2:=subs(var=sqrt(var),po2):
      p1:=collect(p1,var);p2:=collect(p2,var);
   od;

print(`Start to eliminate T.`,time());
   if degree(po1,var)=1 then res:=prem(po2,po1,var);
   elif degree(po2,var)=1 then res:=prem(po1,po2,var);
   else  res:=resultant(po1,po2,var);
   fi;

   if res=0 then
      gcd(po1,po2,'po1');
      if degree(po1,var)=1 then res:=prem(po2,po1,var);
      elif degree(po2,var)=1 then res:=prem(po1,po2,var);
      else  res:=resultant(po1,po2,var);
      fi;
   fi;

   su:=numer(normal(res)):
   readlib(factors):
   fa:=factors(su)[2]:
print(`finding the border curve(s)`,time()):
   ff:=[gg]:
   for i to nops(fa) do fb:=fa[i][1]:
      cs:=[coeffs(fb)]: ret:=1:
      for j from 2 to nops(cs) while ret=1 do
         if sign(cs[j])<>sign(cs[1]) then ret:=-1 fi
      od:
      if ret=-1 and (divide(gg,fb)=false or divide(fb,gg)=false) then
         ff:=[op(ff),fb]:
         print(`OK`):
      fi:
      print(`all right`):
   od:

   lc:=[lcoeff(po1,var),lcoeff(po2,var)]:
   for i to 2 do fb:=expand(lc[i]):
      cs:=[coeffs(fb)]: ret:=1:
      if nops(cs)>1 then
         for j from 2 to nops(cs) while ret=1 do
            if sign(cs[j])<>sign(cs[1]) then ret:=-1 fi
         od:
         if ret=-1 then
            ff:=[op(ff),fb]:
            print(`OK`):
         fi:
         print(`all right`):
      fi
   od:

   ff:=[op(ff),op(cstr)]:

print(`found the border curve(s)`,time()):
   fs:=subsop(1=NULL,ff):
   nf:=nops(ff):

print(`finding the intersection point(s)`):
   fg:=[]:
   for i to nf-1 do
      for j from i+1 to nf do
         dt:=resultant(ff[i],ff[j],par2):
         fac:=factors(dt):
print(i,j,`Good`):
         fc:=fac[2]:
         for k to nops(fc) do fd:=fc[k][1]: ret:=1:
            for n from 0 to degree(fd,par1)-1 while ret=1 do
               if sign(lcoeff(fd,par1))<>sign(coeff(fd,par1,n)) then ret:=-1 fi
            od:
            if ret=-1 then fg:=[op(fg),fd]:fi
         od:
         print(`OK`):
      od:
      print(`all right`):
   od:
print(`finding the critical point(s)`,time()):
   if nf>1 then
      for i from 2 to nf do
         if degree(ff[i],s)>1 then
            df:=resultant(ff[i],diff(ff[i],par2),par2);
            fc:=pwrfr(df,{par1}):
            for k to nops(fc) do fd:=fc[k]: ret:=1:
               for n from 0 to degree(fd,par1)-1 while ret=1 do
                  if sign(lcoeff(fd,par1))<>sign(coeff(fd,par1,n)) then ret:=-1 fi
               od:
               if ret=-1 then fg:=[op(fg),fd]:fi:
               print(`OK`):
            od:
            print(`all right`):
         fi
      od
   fi:
   rs:=[]:
   readlib(realroot):
   F:=product('fg[k]','k'=1..nops(fg));
   fg:=map(numer,[op({op(pwrfr(F,{par1}))} minus {par1})]);
   if fg=[] then tp:=[1];
   else tp:=samplepoint(fg,par1);
   fi:

print(`output one-dimension test point(s).`);
print(tp);
print(`setting the test point(s) and doing test`,time()):

   tps:=[]:
   np:=nops(tp):
   for i to np do
      fq:=subs(par1=tp[i],ff):
      F:=product('fq[k]','k'=1..nops(fq));
      fg:=pwrfr(F,{par2});
      fg:=[op({op(fg)} minus {par2})];
      fg:=map(numer,fg);
      rr:=samplepoint(fg,par2);
      nd:=nops(rr);
      for j to nops(rr) do
         if subs(par2=rr[j],fq[1])>=0 then tps:=[op(tps),[tp[i],rr[j]]];fi;
      od;
   od:
   nq:=nops(cstr):
   tts:=[];
   np:=nops(tps);
   for i to np do
      ret:=1:
      for j to nq while ret=1 do
         ex:=subs(par1=tps[i][1],par2=tps[i][2],cstr[j]):
         if ex<0 then ret:=0  fi:
      od:
      if ret=1 then tts:=[op(tts),tps[i]] fi
   od:
   tps:=tts:

print(tps):
np:=nops(tps);
print(`the number of test point(s) is`, np):
print(`The test result follows ---`):
print(`Either always 1 or always -1 means the inequality holds accordingly`):
   np:=nops(tps):
if np=0 then RETURN(`less`);fi;  #The inequality holds for ever.
   ret:=0:
   if nargs=8 then
#     print(`please go on waiting `.(np*50).` seconds or so..in pentium 586/75/32M`);
   fi;
   temp:=0;co:=[];
   for i to np while temp=0 do
      if nargs=6 then
         eq1:=numer(subs(par1=tps[i][1],par2=tps[i][2],po1)):
         eq2:=numer(subs(par1=tps[i][1],par2=tps[i][2],po2)):
         rr:=realroot(eq1*eq2);
         nr:=nops(rr):
         rs1:=[];rs2:=[];
         for j to nr do
            rs1:=[op(rs1),rr[j][1]];rs2:=[op(rs2),rr[j][2]];
         od;
         rs1:=sort(rs1);rs2:=sort(rs2);
         r1:=rs1;r2:=rs2;

         if subs(var=r1[nr],eq1)*subs(var=r2[nr],eq1)<0 then
            ret:=ret+1;print(1);co:=[op(co),1];
            N:={par1=tps[i][1],par2=tps[i][2]};
         else
            if r1[nr]=r2[nr] and subs(var=r1[nr],eq1)=0 then
               ret:=ret+1;print(1);co:=[op(co),1];
               N:={par1=tps[i][1],par2=tps[i][2]};
            else print(-1): ret:=ret-1;co:=[op(co),-1];
            fi
         fi:
         temp:=changenum(co);
         if temp<>0 then
            xfp:=subs(N,t^3-s*t^2+(p+9)*t-s):
            xp:=solvecubic(coeff(xfp,t,2),coeff(xfp,t,1),coeff(xfp,t,0));
            print(`output a counter-example`);
            lprint([xp[1]+xp[2],xp[2]+xp[3],xp[3]+xp[1]]);
            print(`whose approximate value is the following:`);
            lprint(`a=`,evalf(xp[1]+xp[2]),`b=`,evalf(xp[2]+xp[3]),`c=`,evalf(xp[3]+xp[1]));
         fi;

      elif nargs=8 then
         xfp:=subs({par1=tps[i][1],par2=tps[i][2]},t^3-s*t^2+(p+9)*t-s):
         xp:=solvecubic(coeff(xfp,t,2),coeff(xfp,t,1),coeff(xfp,t,0));
         ep1:=subs({x=xp[1],y=xp[2],z=xp[3]},args[7]);
         ep2:=subs({x=xp[1],y=xp[2],z=xp[3]},args[8]);

         if op(0,ep1)=mid then ep1:=x_mid(op(ep1));fi;
         if op(0,ep2)=mid then ep2:=x_mid(op(ep2));fi;
         if op(0,ep1)=min then ep1:=min(op(ep1));
         elif op(0,ep1)=max then ep1:=max(op(ep1));
         fi;
         if op(0,ep2)=min then ep2:=min(op(ep2));
         elif op(0,ep2)=max then ep2:=max(op(ep2));
         fi;

         if max(ep1-ep2,0)=0 then ret:=ret-1;print(-1);co:=[op(co),-1];
         else 
            ret:=ret+1;print(1);co:=[op(co),1];
            N:={par1=tps[i][1],par2=tps[i][2]};
         fi;
         temp:=changenum(co);
         if temp<>0 then
            xfp:=subs({par1=tps[i][1],par2=tps[i][2]},t^3-s*t^2+(p+9)*t-s):
            xp:=solvecubic(coeff(xfp,t,2),coeff(xfp,t,1),coeff(xfp,t,0));
            print(`output a counter-example`);
            lprint([xp[1]+xp[2],xp[2]+xp[3],xp[3]+xp[1]]);
            print(`whose approximate value is the following:`);
            lprint(`a=`,evalf(xp[1]+xp[2]),`b=`,evalf(xp[2]+xp[3]),`c=`,evalf(xp[3]+xp[1]));
         fi;
      fi;
   od:
   if ret=np then ret:=`greater`
   elif ret=-np then ret:=`less`
   else ret:=`The inequality doesn't hold.`
   fi:
   print(ret):
   RETURN(ret)
end:

samplepoint:=proc(a,var)
   local i,n,b,f,xl,yl,m,k,temp,inf,sup,range;
   
   b:=a;n:=nops(b);
   readlib(rootbound): readlib(realroot):
   xl:=[];k:=34:yl:=[];
   for i to n do
      f:=findproot(b[i],var,k);
      if f<>[] then
         xl:=[op(xl),op(f)];
         yl:=[op(yl),b[i]];
      fi;
   od;

   if xl=[] then RETURN([1]);fi;

   m:=nops(xl);inf:=[];sup:=[];
   for i to m do inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];od;
   inf:=sort(inf);sup:=sort(sup);
   range:=[[0,inf[1]]];
   temp:=1;
   for i to m-1 while temp=1 do
      if sup[i]>=inf[i+1] then temp:=-1;fi;
      range:=[op(range),[sup[i],inf[i+1]]];
   od;
   range:=[op(range),[sup[m],sup[m]+2]];

   b:=yl;n:=nops(b);
   while temp=-1 do
      k:=k+33;
      xl:=[];
      for i to n do xl:=[op(xl),op(findproot(b[i],var,k))];od;
      m:=nops(xl);inf:=[];sup:=[];
      for i to m do inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];od;
      inf:=sort(inf);sup:=sort(sup);
      range:=[[0,inf[1]]];
      temp:=1;
      for i to m-1 while temp=1 do
         if sup[i]>=inf[i+1] then temp:=-1;fi;
         range:=[op(range),[sup[i],inf[i+1]]];
      od;
      range:=[op(range),[sup[m],sup[m]+2]];
   od;

   xl:=[];for i to m+1 do xl:=[op(xl),(range[i][1]+range[i][2])/2];od;
   n:=nops(xl); inf:=[];
   k:=13:
   for i to n do
      m:=1:
      temp:=convert(evalf(xl[i],k),fraction,m);
      while temp<=range[i][1] or temp>=range[i][2] do
         m:=m+1;
         k:=k+1:
         temp:=convert(evalf(xl[i],k),fraction,m);
      od;
      inf:=[op(inf),temp];
   od;
   inf;
end:

findproot:=proc(f,var,k)
   local i,g,B,n,L,tk;
   
   readlib(rootbound):readlib(realroot):
   B:=rootbound(f,var);
   g:=expand(subs(var=B*var,f));
   if B<1 then g:=numer(g);fi;
   n:=degree(g,var);
   L:=zero_one(g,var,n,1/B/2^k);
   tk:=k+1:
   while has(L,0) do
   		L:=zero_one(g,var,n,1/B/2^tk);
   		tk:=tk+1:
   od:
   if L=[] then RETURN([]);fi;
   L:=map(proc(x,y) [op(1,x)*y,op(2,x)*y];end,L,B);
end:

changenum:=proc(ll) 
   local i,l,n,m;

   l:=ll;
   n:=nops(l);
   m:=0;
   for i to n-1 do
      if x_sign(l[i])<>x_sign(l[i+1]) then m:=m+1 fi;
   od;
   m;
end:

x_sign:=proc(x)
   local y;
   
   if x=0 then y:=1
   elif min(x,0)=0 then y:=1
   elif min(x,0)=x then y:=-1
   fi;
   y;
end:

x_sort:=proc(fpoly)
   local poly,xl,ttemp,n,its;
   
   poly:=fpoly;
   its:=[x,y,z];
   xl:=[];
   while poly<>0 do
      ttemp:=_sort(poly,its);
      poly:=op(1,ttemp);
      xl:=[op(xl),op(2,ttemp)];
   od;
   n:=nops(xl);
   poly:=sum('xl[i]','i'=1..n);
   RETURN(poly);
end:

_sort:=proc(fpoly,vars)
   local poly,its,_x1,_x2,_x3,xl,yl,n,i,j,k,temp,t,temp1,temp2;
   
   poly:=sort(expand(fpoly),[x,y,z],`plex`);
   its:=vars;
   _x1:=its[1]+its[2]+its[3];
   _x2:=its[2]*its[3]+its[3]*its[1]+its[1]*its[2];
   _x3:=its[1]*its[2]*its[3];
   if type(poly,`+`) then xl:=[op(poly)]; else xl:=[poly] fi;
   if xl[1]=0 then RETURN([0,0]);fi;

   temp1:=poly-lcoeff(xl[1],its)*_x1^(degree(xl[1],its[1])-degree(xl[1],its[2]))
          *_x2^(degree(xl[1],its[2])-degree(xl[1],its[3]))*_x3^degree(xl[1],its[3]);
   temp1:=simplify(temp1);
   temp2:=lcoeff(xl[1],its)*s^(degree(xl[1],its[1])-degree(xl[1],its[2]))*
          (p+9)^(degree(xl[1],its[2])-degree(xl[1],its[3]))
          *s^degree(xl[1],its[3]);
   temp2:=expand(temp2);
   yl:=[temp1,temp2];
   RETURN(yl);
end:

fsplit:=proc(al,bl)
   local i,n,xl,l,res,result;

xl:={x=y,y=z,z=x,a=b,b=c,c=a,s=s,ra=rb,rb=rc,rc=ra,ha=hb,hb=hc,hc=ha,
ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,IC=IA,
Ha=Hb,Hb=Hc,Hc=Ha,sin(A)=sin(B),sin(B)=sin(C),sin(C)=sin(A),cos(A)=cos(B),
cos(B)=cos(C),cos(C)=cos(A),sin(A/2)=sin(B/2),sin(B/2)=sin(C/2),sin(C/2)=sin(A/2),
cos(A/2)=cos(B/2),cos(B/2)=cos(C/2),cos(C/2)=cos(A/2),r=r,R=R,S=S,Ra=Rb,Rb=Rc,
Rc=Ra,GA=GB,GB=GC,GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja
}:

   n:=nops(al);
   if subs(xl,al[1])-al[1]=0 then result:=[op(bl),[al[1]]];l:=subsop(1=NULL,al);
   else
      res:=[al[1]];
      for i from 2 to n do
         if subs(xl,al[1])-al[i]=0 or subs(xl,subs(xl,al[1]))-al[i]=0 then
            res:=[op(res),al[i]];
         fi;
      od;
      l:=[op({op(al)} minus {op(res)})];
      result:=[op(bl),res];
   fi;
   if l<>[] then result:=fsplit(l,result) fi;
   result;
end:

x_mid:=proc(x,y,z)  x+y+z-max(x,y,z)-min(x,y,z);end:

testroot:=proc(f,var,a,b)
   local g,d;
   
   g:=numer(subs(var=a+(b-a)*var,f));
   readlib(realroot):
   d:=degree(g,var);
   zero_one(g,var,d,1);
end:

trans:=proc(ineq)
   local iq,mts,nts,np,nm,ns,i,ex,ls,rs:

   iq:=numer(expand(lhs(ineq)-rhs(ineq))):
   iq:=simplify(iq,symbolic):
   mts:=0:    nts:=0:
   np:=0:     nm:=0:
   ns:=nops(iq):
   if type(iq,`+`)=true then 
      for i to ns do ex:=op(i,iq):
         if (hastype(ex,radical)=true or has(ex,{wa,wb,wc,ma,mb,mc,d})=true) then 
            if max(op(1,ex),0)=0 then mts:=mts+ex: nm:=nm+1
            elif min(op(1,ex),0)=0 then np:=np+1
            fi
         else nts:=nts+ex
         fi
      od
   fi:
   ls:=iq-mts:
   rs:=-mts:
   if nm<np then ls:=ls-nts: rs:=rs-nts fi:
   RETURN(factor(ls)<=factor(rs))
end:

###################################################################
xprove:=proc(ineq)
   local i,m,m1,m2,n,xl,curves,pointl,N,l,ll,plist,k,its,temp,nn,vars,ep,poly,j,cp,ITS,cl,cq;

if whattype(args[1])=`=` then RETURN(`The input argument should be inequality.`);fi;

   if nargs>3 then RETURN(`invalid arguments`);fi;
   if nargs>=2 then
      if not type(args[2],list) then RETURN(`invalid second argument`);fi;
   fi;

   curves:=lhs(ineq)-rhs(ineq);
   if nargs>=2 then
      xl:=args[2];
      m:=nops(xl);
      for i to m do
         curves:=curves*(lhs(xl[i])-rhs(xl[i]));
      od;
   fi;

   curves:=expand(numer(curves)*denom(curves));
   curves:=elimfracrad(curves);
	curves:=numer(curves)*denom(curves);
	curves:=combine(curves,radical,symbolic);
   curves:=expand(curves);


   its:=[op(indets(curves))];
   ITS:=[];
   for i to nops(its) do 
      if not hastype(its[i],radical) then ITS:=[op(ITS),its[i]]; fi; 
   od;
   its:=ITS;
   curves:=expand(simplify(curves,radical,symbolic));
   while hastype(curves,radical) do
      curves:=rads(curves);
   od;

   xl:=discardpl(curves);
   n:=nops(xl);curves:=1;
   for i to n do
      temp:=[coeffs(xl[i])];
      if changenum(temp)<>0 then curves:=curves*xl[i];fi;
   od;

   curves:=curves*product(its[k],k=1..nops(its));
   
print(`Found border curves..`);
print(curves);

   print(`Start to project curves..`,time());
   plist:=proj(curves);
   n:=nops(plist);
   print(`Start to find the sample points.`,time());
   N:=n;
   print(cat(`in `,1,`-dimensional space....`));
   pointl:=xsamplepoint(pwrfr(plist[n][1],{plist[n][2][1]}),plist[n][2][1]);

   print(cat(`finished in `,1,`-dimensional space.`));
   n:=n-1;
   while n>0 do
      print(cat(`in `,(N-n+1),`-dimensional space....`));
      m:=nops(pointl);
      temp:=plist[n+1][2];
      k:=nops(temp);
      ll:=pointl;
      pointl:=[];
      for i to m do
         poly:=subs({seq(op(mm,temp)=ll[i][mm],mm=1..k)},plist[n][1]);
         vars:=plist[n][2][1];
         poly:=primpart(expand(poly),vars);
         poly:=pwrfr(poly,{vars});
         l:=xsamplepoint(poly,vars);
         nn:=nops(l);
         for j to nn do
            pointl:=[op(pointl),[op(l[j]),op(ll[i])]];
         od;
      od;
      print(cat(`finished in `,(N-n+1),`-dimensional space.`));
      n:=n-1;
      pointl;
   od;
   its:=plist[1][2];
   m:=nops(its);
#print(pointl);
   if nargs>=2 then
      l:=pointl;
      nn:=nops(pointl);
      pointl:=[];
      m1:=args[2];
      m2:=nops(m1);
      for i to nn do
         temp:=1;
         for j to m2 while temp=1 do
            ep:=lhs(m1[j])-rhs(m1[j]);
            if subs({seq(its[k]=l[i][k],k=1..m)},denom(ep))=0 then temp:=-1;
            else
	            ep:=subs({seq(its[k]=l[i][k],k=1..m)},ep);       
	            if hastype(m1[j],`<`) then if max(ep,0)<>0 or ep=0 then temp:=-1 fi;
	            else if max(ep,0)<>0 then temp:=-1; fi;
	            fi;
            fi;
         od;
         if temp=1 then pointl:=[op(pointl),op(i,l)] fi;
      od;
   fi;

   print(`number(s) of sample points:`,nops(pointl),time());
   print(its);
print(pointl);    

   if iscgr(ineq)=1 then 

      if nargs<=2 then temp:=callCgrTest(ineq,pointl,its);
      elif nargs=3 then temp:=callCgrTest(ineq,pointl,its,aaaa);
      fi;
      if nargs=3 and type(args[3],set) then
		  cl:=map(coeffs,subs(args[3],its));
	      cp:=temp[2];
	      cq:=cp;
	      if type(cq,list) then cp:=[seq(its[k]=cq[k]*cl[k],k=1..nops(cl))];fi;
	      temp:=[temp[1],cp];
	  fi;
      RETURN(temp);
   fi;
        
   temp:=-1;
   if nops(pointl)>0 then
      temp:=1;
      for i to nops(pointl) while temp=1 do
         ep:=lhs(ineq)-rhs(ineq);
         ep:=subs({seq(its[k]=pointl[i][k],k=1..m)},ep);
print(ep);         
         ep:=simplify(ep);      
         if max(ep,0)=0 then
            print(`OK`);
         else
            temp:=-1;
            if nargs<3 then print(` output a counter-example: `);fi;
            cp:=[seq(its[k]=pointl[i][k],k=1..m)];
            if nargs<3 then print(pointl[i]);fi;
         fi;
      od;
	  if nargs<3 then
	      if temp=1 then
	         print(`The inequality holds !`) ;
                if nargs=1 then RETURN(true) fi:
	         print(ineq);
	         if nargs>1 and args[2]<>[] then print(`when`); print(op(args[2])); RETURN(true) fi;
	      else
	         print(`The inequality does not hold !`)
	      fi;
      fi;
   else temp:=1; print(`The inequality holds for ever!`): RETURN(true) 
   fi;
#       print(`time=`,time());
	if nargs<3 then RETURN();fi;
	if nargs=3 and type(args[3],set) then
		cl:=map(coeffs,subs(args[3],its));
		cq:=cp;
		if type(cq,list) then cq:=map(proc(x) op(2,x) end,cq);cp:=[seq(its[k]=cq[k]*cl[k],k=1..nops(cl))];fi;
	fi;
	RETURN([temp,cp]):
end:

yprove:=proc(ineq)
   local id,nd,sb,i,j,iq,ids,cp:

if whattype(args[1])=`=` then RETURN(`The input argument should be inequality.`);fi;
   if nargs>2 then RETURN(`invalid arguments`);fi;
   id:=[op(indets(ineq))]:
   if nargs=2 then
   if not type(args[2],list) then RETURN(`invalid second argument`); fi;
      ids:={op(id)};
      for i to nops(args[2]) do
         ids:={op(ids),op(indets(args[2][i]))}
      od;
      id:=[op(ids)];
   fi;

   nd:=nops(id): ids:=[];
   for i to nd do if not type(id[i],radical) then ids:=[op(ids),id[i]];fi;od;
   id:=ids;nd:=nops(id);
#print(id);
   sb:=[{}]:
   for i to nd do
      sb:=map(xx->({op(xx)},{op(xx),id[i]=-id[i]}),sb)
   od:
#print(sb);   
   for j to 2^(nd) do
print(sb[j]);
      if nargs=2 then
         iq:=subs(sb[j],args[2]):
         cp:=xprove(subs(sb[j],args[1]),iq,sb[j]);
         if cp[1]<>1 then print(`   `);print(`output a counter example`);print(cp[2]);print(`The inequality does not hold.`);  RETURN(): fi
      else
         cp:=xprove(subs(sb[j],args[1]),[],sb[j]);
         if cp[1]<>1 then print(`   `);print(`output a counter example`);print(cp[2]);print(`The inequality does not hold.`); RETURN(): fi
      fi;
   od:
   print(`  `);
   print(`The inequality holds!`):
   RETURN()
end:

discardpl:=proc(f)
   local i,n,g,p;
   
   if nargs=1 then g:=factor(f);else g:=f;fi;
   if whattype(g)=`+` then RETURN([g])
   elif whattype(g)=`^` then RETURN([op(1,g)])
   elif whattype(g)=`*` then
      n:=nops(g);
      p:=[];
      for i to n do
         p:=[op(p),op(discardpl(op(i,g),x))];
      od;
      RETURN(p);
   else RETURN([g]);
   fi;
end:

proj:=proc(curves)
   local i,j,l,m,n,ll,its,vars,poly,temp;
   
   if nargs>2 then ERROR(`invalid arguments in procedure proj.`);fi;
   poly:=expand(curves);
   if nargs=1 then
      its:=[op(indets(poly))];
      n:=nops(its);
      if n>1 then
         l:=[];
         for i to n do l:=[op(l),degree(poly,its[i])];od;
         l:=sort(l);vars:=[];
         for i to n do
            for j to n do
               if its[j]<>0 and degree(poly,its[j])=l[i] then vars:=[op(vars),its[j]];its:=subsop(j=0,its);fi;
            od;
         od;
         its:=vars;
      fi;
   else
      its:=[op(indets(poly) minus {op(args[2])})];
      n:=nops(its);
      if n>1 then
         l:=[];
         for i to n do l:=[op(l),degree(poly,its[i])];od;
         l:=sort(l);vars:=[];
         for i to n do
            for j to n do
               if its[j]<>0 and degree(poly,its[j])=l[i] then vars:=[op(vars),its[j]];its:=subsop(j=0,its);fi;
            od;
         od;
         its:=vars;
      fi;
      its:=[op(its),op(args[2])];
   fi;
print(its);
   l:=[[poly,its]];
   vars:=its:
   m:=1;

   while nops(its)>1 do
      print(cat(`do `,m,`-th partition...`));
      if nargs=1 then ll:=cad(poly,its,vars);
      else
         ll:=cad(poly,its,vars,{op(args[2])});
      fi;
      l:=[op(l),ll];
      poly:=op(1,ll);
      its:=op(2,ll);
      m:=m+1;
   od;
   l;
end:

cad:=proc(expr,varlist)
   local i,j,k,xl,yl,m,l,n,var,varl,poly,temp;
   
   if nargs>4 then ERROR(`invalid arguments in procedure cad.`);fi;
   var:=op(1,varlist);
   poly:=primpart(expr);
   varl:=subsop(1=NULL,varlist);
   if degree(poly)=0 then RETURN([1,varl]);fi;
   l:=discardpl(poly);
   n:=nops(l);
   poly:=1;

   if n>1 then
      for i to n-1 do
         if not has(l[i],var) then poly:=poly*l[i];next;fi;
         for j from i+1 to n do
            if not has(l[j],var) then poly:=poly*l[j];next;fi;
            temp:=resultant(l[i],l[j],var);
            temp:=primpart(temp);
            xl:=discardpl(temp);temp:=1;m:=nops(xl);
            for k to m do
               if member(xl[k],args[3]) then temp:=temp*xl[k];
               else
                  yl:=[coeffs(xl[k])];
                  if nargs=3 then
                     if changenum(yl)<>0 then temp:=temp*xl[k];fi;
                  else
                     if has(xl[k],args[4]) then temp:=temp*xl[k];
                     else
                        if changenum(yl)<>0 then temp:=temp*xl[k];fi;
                     fi;
                  fi;
               fi;
            od;
            poly:=poly*temp;
         od;
      od;
   fi;

   for i to n do
      if has(l[i],var) then
         temp:=resultant(l[i],diff(l[i],var),var);
         temp:=primpart(temp);
         xl:=discardpl(temp);temp:=1;m:=nops(xl);
         for k to m do
            if member(xl[k],args[3]) then temp:=temp*xl[k]
            else
               yl:=[coeffs(xl[k])];
               if nargs=3 then
                  if changenum(yl)<>0 then temp:=temp*xl[k];fi;
               else
                  if has(xl[k],args[4]) then temp:=temp*xl[k];
                  else
                     if changenum(yl)<>0 then temp:=temp*xl[k];fi;
                  fi;
               fi;
            fi;
         od;
         poly:=poly*temp;
      else poly:=poly*l[i];
      fi;
   od;

   l:=discardpl(poly);
   n:=nops(l);
   poly:=1:
   for i to n do
      if member(l[i],args[3]) then poly:=poly*l[i];
      else
         temp:=[coeffs(l[i])];
         if nargs=3 then
            if changenum(temp)<>0 then  poly:=poly*l[i];  fi;
         else
            if has(l[i],args[4]) then poly:=poly*l[i];
            else
               if changenum(temp)<>0 then  poly:=poly*l[i];  fi;
            fi;
         fi;
      fi;
   od;
   [poly,varl];
end:

xsamplepoint:=proc(a,var)
   local i,n,b,f,xl,yl,m,k,temp,inf,sup,range;
   
   b:=a;n:=nops(b);
   readlib(rootbound): readlib(realroot):
   xl:=[];k:=34:yl:=[];
   for i to n do
      f:=findproot(b[i],var,k);
      if f<>[] then
         xl:=[op(xl),op(f)];
         yl:=[op(yl),b[i]];
      fi;
   od;

   if xl=[] then if nargs=2 then RETURN([[1]]);else RETURN([[[1],[1]]]);fi;fi;

   m:=nops(xl);inf:=[];sup:=[];
   for i to m do inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];od;
   inf:=sort(inf);sup:=sort(sup);
   range:=[[0,inf[1]]];
   temp:=1;
   for i to m-1 while temp=1 do
      if sup[i]>=inf[i+1] then temp:=-1;fi;
      range:=[op(range),[sup[i],inf[i+1]]];
   od;
   range:=[op(range),[sup[m],sup[m]+2]];

   b:=yl;n:=nops(b);
   while temp=-1 do
      k:=k+33;
      xl:=[];
      for i to n do xl:=[op(xl),op(findproot(b[i],var,k))];od;
      m:=nops(xl);inf:=[];sup:=[];
      for i to m do inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];od;
      inf:=sort(inf);sup:=sort(sup);
      range:=[[0,inf[1]]];
      temp:=1;
      for i to m-1 while temp=1 do
         if sup[i]>=inf[i+1] then temp:=-1;fi;
         range:=[op(range),[sup[i],inf[i+1]]];
      od;
      range:=[op(range),[sup[m],sup[m]+2]];
   od;

   xl:=[];for i to m+1 do xl:=[op(xl),(range[i][1]+range[i][2])/2];od;
   n:=nops(xl); inf:=[];
   k:=13:
   for i to n do
      m:=1:
      temp:=convert(evalf(xl[i],k),fraction,m);
      while temp<=range[i][1] or temp>=range[i][2] do
         m:=m+1;
         k:=k+1:
         temp:=convert(evalf(xl[i],k),fraction,m);
      od;
      inf:=[op(inf),temp];
   od;
   if nargs=2 then
      n:=nops(inf);sup:=[];
      for i to n do sup:=[op(sup),[inf[i]]];od;
      RETURN(sup);
   else
      n:=nops(inf);sup:=[];
      for i to n do sup:=[op(sup),[[i],[inf[i]]]];od;
      RETURN(sup);
   fi;
end:

sgm:=proc(expr)
   local rap,ex2,ex3,ex:
   
   rap:={a=b,b=c,c=a,A=B,B=C,C=A,x=y,y=z,z=x,ha=hb,hb=hc,hc=ha,Ra=Rb,Rb=Rc,Rc=Ra,
         ra=rb,rb=rc,rc=ra,ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,ka=kb,kb=kc,kc=ka,
         HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
         IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
         GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:
         
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr+ex2+ex3:
   RETURN(ex)
end:

data:=proc()
   local xlst;

   xlst:=
   {
   a=y+z,b=z+x,c=x+y,s=x+y+z,
   ra=(x+y+z)/x,rb=(x+y+z)/y,rc=(x+y+z)/z,
   ha=2*(x+y+z)/(y+z),hb=2*(x+y+z)/(z+x),hc=2*(x+y+z)/(x+y),
   ma=((y-z)^2/4+x*(x+y+z))^(1/2),mb=((z-x)^2/4+y*(x+y+z))^(1/2),mc=((x-y)^2/4+z*(x+y+z))^(1/2),
   wa=2*(x^2+1)^(1/2)*(x+y+z)/(2*x+y+z),wb=2*(y^2+1)^(1/2)*(x+y+z)/(2*y+z+x),wc=2*(z^2+1)^(1/2)*(x+y+z)/(2*z+x+y),
   HA=(y+z)*(x^2-1)/2/x,HB=(z+x)*(y^2-1)/2/y,HC=(x+y)*(z^2-1)/2/z,
   IA=(x^2+1)^(1/2),IB=(y^2+1)^(1/2),IC=(z^2+1)^(1/2),
   p=x*y+y*z+x*z-9,q=x^2-2*x*y-2*x*z+y^2-2*y*z+z^2+9,
   Ha=(y*z+1)/2-x*(y^2+z^2-2)/2/(y+z),Hb=(z*x+1)/2-y*(z^2+x^2-2)/2/(z+x),Hc=(x*y+1)/2-z*(x^2+y^2-2)/2/(x+y),

   sin(A)=2*(y+z)/(x*y+y*z+z*x-1),sin(B)=2*(z+x)/(x*y+y*z+z*x-1),sin(C)=2*(x+y)/(x*y+y*z+z*x-1),
   cos(A)=1-2*y*z/(x+y)/(x+z),cos(B)=1-2*z*x/(y+z)/(y+x),cos(C)=1-2*x*y/(x+z)/(y+z),
   sin(A/2)=(x^2+1)^(-1/2),sin(B/2)=(y^2+1)^(-1/2),sin(C/2)=(z^2+1)^(-1/2),
   cos(A/2)=x/(x^2+1)^(1/2),cos(B/2)=y/(y^2+1)^(1/2),cos(C/2)=z/(z^2+1)^(1/2),

   tan(A/2)=1/x,tan(B/2)=1/y,tan(C/2)=1/z,
   cot(A/2)=x,cot(B/2)=y,cot(C/2)=z,
   tan(A)=2*x/(x^2-1),tan(B)=2*y/(y^2-1),tan(C)=2*z/(z^2-1),
   cot(A)=(x^2-1)/2/x,cot(B)=(y^2-1)/2/y,cot(C)=(z^2-1)/2/z,
   sec(A)=1/(1-2*y*z/((x+y)*(z+x))),sec(B)=1/(1-2*x*z/((x+y)*(y+z))),sec(C)=1/(1-2*y*x/((y+z)*(z+x))),
   sec(A/2)=sqrt(x^2+1)/x,sec(B/2)=sqrt(y^2+1)/y,sec(C/2)=sqrt(z^2+1)/z,
   csc(A)=1/2*(y*z+z*x+x*y-1)/(y+z),csc(B)=1/2*(y*z+z*x+x*y-1)/(z+x),csc(C)=1/2*(y*z+z*x+x*y-1)/(x+y),
   csc(A/2)=sqrt(x^2+1),csc(B/2)=sqrt(y^2+1),csc(C/2)=sqrt(z^2+1),

   K=(x^2+y^2+z^2+3*x*y+3*y*z+3*z*x),H=(x^2+y^2+z^2+x*y+y*z+z*x),
   r=1,R=(y*z+z*x+x*y-1)/4,S=x+y+z,Q=-2*x*y+2*x^2+2*y^2+2*z^2-2*y*z-2*x*z,
   Ra=(x+z)*(x+y)/x^2,Rb=(x+y)*(y+z)/y^2,Rc=(y+z)*(x+z)/z^2,
   GA=2/3*((y-z)^2/4+x*(x+y+z))^(1/2),GB=2/3*((z-x)^2/4+y*(x+y+z))^(1/2),GC=2/3*((x-y)^2/4+z*(x+y+z))^(1/2),
   JA=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*y^2*z^2*(x+y+z))^(1/2)/(y*z+z*x+x*y)/2,
   JB=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*x^2*z^2*(x+y+z))^(1/2)/(y*z+z*x+x*y)/2,
   JC=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*y^2*x^2*(x+y+z))^(1/2)/(y*z+z*x+x*y)/2,
   ca=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*y^2*z^2*(x+y+z))^(1/2)/(2*y*z+z*x+x*y),
   cb=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*x^2*z^2*(x+y+z))^(1/2)/(y*z+2*z*x+x*y),
   cc=((x+y+z)^2*(y*z+z*x+x*y)^2-4*(x+y+z)^2*(y*z+z*x+x*y)+(x+y+z)^2-2*(x+y+z)^4-4*y^2*x^2*(x+y+z))^(1/2)/(y*z+z*x+2*x*y),
   Ja=x*(x+y+z)/(y*z+z*x+x*y),Jb=y*(x+y+z)/(y*z+z*x+x*y),Jc=z*(x+y+z)/(y*z+z*x+x*y)
   }:
end:

filterrads:=proc(indetslst)
   local radlst,rad,i,np,ob;
   
   rad:=indetslst;
   radlst:=[op(rad)];rad:={};
   np:=nops(radlst);
   for i to np do 
      ob:=radlst[i];
      if type(ob,radical) then
         rad:={op(rad),ob};#rad:={op(rad),op(1,ob)^(1/denom(op(2,ob)))};#if rads use findrads
      fi;
   od;
   rad
end:

findrads:=proc(expr)
   local ep,np,rad,i,j,ob,nq,radlst;
   
   ep:=expr;
   rad:=indets(ep,radical);
   if rad={} then RETURN(rad);fi;
   rad:=filterrads(rad);
   if rad={} then RETURN(rad);fi;
   
   radlst:=[op(rad)];
   while radlst<>[] do
      radlst:=map(proc(x) op(1,x);end,radlst);
      radlst:=map(proc(x) indets(x,radical);end,radlst);
      radlst:=map(filterrads,radlst);
      radlst:=map(proc(x) op(x);end,radlst);
      rad:=rad union {op(radlst)};
      radlst:=[op({op(radlst)})];
   od;
   rad:=[op(rad)];
   rad:=sort(rad,has);
end:

iscgr:=proc(expr)
   local ep,np,i,nq,j,rad,nr,rp,ob,ob1,ob2,tmp1,tmp2,_rad:

   if TURNOFFCGR=1 then RETURN(0);fi;
   if CGR=1 then RETURN(1);fi;

   ep:=expand(expr);

   if hastype(expr,`<`) or hastype(expr,`<=`) then ep:=lhs(expr)+rhs(expr);fi;
   
   if has(ep,abs) then ep:=deleteabs(ep);fi;
   
   ep:=expand(subs(data(),ep));

   if has(ep,{min,mid}) then RETURN(0);fi;
   if not hastype(ep,radical) then RETURN(1) fi;

   if nops(indets(denom(ep),radical))>=1 then RETURN(0);fi;

   rad:=findrads(ep);
   
   if rad=[] then RETURN(1)
   else 
      nr:=nops(rad):
      _rad:=rad;

      for i to nr do
         ep:=subs(rad[i]=uu[i],ep);
         if i<nr then
         	for j from i+1 to nr do
         		rad[j]:=subs(rad[i]=uu[i],rad[j]);
         	od;
         fi;
      od;

      if cgrornot(ep,nr)=0 then RETURN(0);fi;

      while hastype(_rad,radical) do    
         _rad:=map(proc(x) op(1,x);end,_rad);
         _rad:=map(iscgr,_rad);
      od;
      if has(_rad,0) then RETURN(0);fi;
   fi:
   RETURN(1);
end:

cgrornot:=proc(expr,nr)
   local n,i,j,k,ep,ob;

   ep:=expand(expr);
   if hastype(ep,radical) then ERROR(`error arguments in cgrornot`,args);fi;
   if not has(ep,uu) then RETURN(1);fi;
      
   n:=nops(ep);
   if type(ep,`^`) then
      RETURN(cgrornot(op(1,ep),nr));
   elif type(ep,`*`) then
      ep:=expand(numer(ep)*denom(ep));
      for i to nr do 
         if has(ep,uu[i]) then
            for j from ldegree(ep,uu[i]) to degree(ep,uu[i]) do
               if j<>0 then
                  ob:=coeff(ep,uu[i],j);
                  ob:=expand(numer(ob)*denom(ob));
                  ob:=[coeffs(ob)];
                  ob:=map(proc(x) sign(x) end,ob);
#print(ob);
                  if has(ob,-1) then RETURN(0);fi;
               fi;
            od;
         fi;
      od;
      RETURN(1);   
   elif type(ep,`+`) then
      ob:=1;
      for i to n while ob=1 do
         ob:=cgrornot(op(i,ep),nr);
      od;
      RETURN(ob);
   fi;
   RETURN(1);
end:

cgrtest:=proc(lftPoly,rgtPoly)
   local rr,m,n,i,rr1,k,poly,tt,temp,lstL,lstR,j,T,lftpoly,rgtpoly;

	lftpoly:=lftPoly;
	rgtpoly:=rgtPoly;
   if not type(lftpoly,polynom) or not type(rgtpoly,polynom) then
      ERROR(`invalid arguments.`);
   fi;

   if lftpoly-rgtpoly=0 then RETURN(1) fi;
   rr:=indets(lftpoly) union indets(rgtpoly);

   if nops(rr)<>1 then ERROR(`invalid arguments.`);fi;

   T:=op(rr);

   if prem(rgtpoly,lftpoly,T) = 0 then RETURN(1) fi;
   
   lftpoly:=pwrfree(lftpoly,{T});
   rgtpoly:=pwrfree(rgtpoly,{T});

   readlib(realroot):
   poly:=pwrfr(lftpoly*rgtpoly,{T});
   readlib(realroot):  m:=nops(poly);

   k:=-10;tt:=1;
   while tt=1 do
      rr:=[];
      for i to m do rr:=[op(rr),op(realroot(poly[i],2^k))];od;
      n:=nops(rr);lstL:=[]: lstR:=[]:
      rr1:=array(1..n); for i to n do rr1[i]:=rr[i];od;

      for i to n-1 do 
         for j from i+1 to n do
            if rr1[i][1]>rr1[j][1] or (rr1[i][1]=rr1[j][1] and rr1[i][2]>rr1[j][2]) then 
               temp:=rr1[i];rr1[i]:=rr1[j];rr1[j]:=temp;
            fi;
         od;
      od;
#print(k,rr1);
      for i to n do lstL:=[op(lstL),rr1[i][1]];lstR:=[op(lstR),rr1[i][2]] od;
      lstL:=sort(lstL); lstR:=sort(lstR);

      tt:=0;
      for i to n-1 while tt=0 do
         if lstR[i]>lstL[i+1] then tt:=1;fi;
      od;
      k:=k-10;
   od;

   if subs(T=lstL[n],lftpoly)*subs(T=lstR[n],lftpoly)<0 then  
      RETURN(0)
   else
      if lstL[n]=lstR[n] and subs(T=lstL[n],lftpoly)=0 then
         RETURN(0)
      else RETURN(1)
      fi;
   fi:
end:

callCgrTest:=proc(in_eq,pointl,its)
   local lftPoly,rgtPoly,i,j,np,pp,cp,n,tt,tp,temp,ineq;

   if nops(pointl)=0 then
      if nargs=3 then 
#         print(`The inequality does not hold.`);
         print(`The inequality holds.`);
         RETURN();
      else
#         RETURN([-1,cp]);
         RETURN([1,cp]);
      fi;
   fi;

#	ineq:=simplify(in_eq,radical,symbolic);
ineq:=simplify(in_eq);
   lftPoly:=lhs(ineq)-T;
   lftPoly:=denom(lftPoly)*numer(lftPoly);
   rgtPoly:=rhs(ineq)-T;
   rgtPoly:=denom(rgtPoly)*numer(rgtPoly);
   while hastype(lftPoly,radical) do
      lftPoly:=rads(lftPoly);
   od;
   while hastype(rgtPoly,radical) do
      rgtPoly:=rads(rgtPoly);
   od;
    
   n:=nops(pointl);
   np:=0;pp:=0;
   for i to n do
      cp:=pointl[i];
      tp:={seq(its[j]=pointl[i][j],j=1..nops(its))};
      tt:=cgrtest(subs(tp,lftPoly),subs(tp,rgtPoly));
      if tt=1 then pp:=pp+1;print(-1);
      else np:=np+1;print(1);temp:=cp;
      fi;
      if pp>0 and np>0 then 
      	cp:=temp;
         if nargs=3 then 
            print(`output a counter-example`);
            print(cp);
            print(`The inequality does not hold.`);
            RETURN();
         else
            RETURN([0,cp]);
         fi;
      fi;
   od;
   if pp=n then 
      if nargs=3 then
         print(`The inequality holds.`); RETURN(true)
      else
         RETURN([1,cp]);
      fi;
   fi;
   if np=n then
      if nargs=3 then
         print(`The inequality inversely holds.`);
      else
         RETURN([-1,cp]);
      fi;
   fi;
end:

#################################################################
cmin:=proc(ineq,list1,var)
   local i,j,n,p1,p2,f1,f2,f3,f4,xl,inf,sup,m,temp,iq,tt,flag1,flag2,xsh,dl,ep1,ep2,iqlst,nret,bstop;
   global gg,aa,hh;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:
   
   dl:=data():
   if (cyclicornot(ineq)<>1) or (args[2]<>[aa] and args[2]<>[]) then 
   	iqlst:=[ineq];
      for i to nops(args[2]) do
         if not (type(args[2][i],`<`) or type(args[2][i],`<=`)) then
            if args[2][i]=aa then iqlst:=[op(iqlst),(x-1)*(y-1)*(z-1)>=0];else iqlst:=[op(iqlst),args[2][i]>=0];fi;
         else iqlst:=[op(iqlst),args[2][i]];
         fi;
      od;
		iqlst:=map(expand,iqlst);
		iqlst:=subs(dl,iqlst);
      xmin(subs(z=(x+y)/(x*y-1),subs(dl,iqlst[1])),[x*y>1,op(subs(z=(x+y)/(x*y-1),subs(dl,subsop(1=NULL,iqlst))))],var);
      RETURN();
   fi;

   #if args[2]<>[aa] and args[2]<>[] then RETURN(`invalid second argument`);fi;   
print(`Start to find the border curves of `.var,time());
   p1:=subs(var=_xk,lhs(ineq));
   p2:=subs(var=_xk,rhs(ineq));
   p1:=psTpoly(p1);
   p2:=psTpoly(p2);
   p1:=subs(q=s^2-4*p-27,p1);
   p2:=subs(q=s^2-4*p-27,p2);
   p1:=subs(_xk=var,p1);
   p2:=subs(_xk=var,p2);
   f1:=resultant(p1,p2,T);
   f1:=pwrfree(f1,{p,s,var});
   f2:=gg;
   if args[2]<>[] then
      n:=nops(list1);
      for i to n do f2:=f2*subs(T=0,psTpoly(list1[i]));od;
   fi;
   f4:=gcd(f1,f2);
   f1:=f1/f4;f2:=f2/f4;
   f3:=resultant(f1,f2,p);
   if f3=0 then f3:=1;fi;

   xl:=pwrfr(f1*f4,{p,s,var});
   for i to nops(xl) do xsh:=resultant(xl[i],diff(xl[i],p),p);if xsh<>0 then f3:=f3*xsh;fi;od;
   xl:=pwrfr(f2*f4,{p,s,var});
   for i to nops(xl) do xsh:=resultant(xl[i],diff(xl[i],p),p);if xsh<>0 then f3:=f3*xsh;fi;od;

   xl:=pwrfr(f3,{s,var});
   n:=nops(xl);
   f3:=1;
   if n>1 then
      for i to n-1 do
         f3:=f3*pwrfree(resultant(xl[i],diff(xl[i],s),s),{var});
         for j from i+1 to n do
            if has(xl[i],s) or has(xl[j],s) then
               f3:=f3*pwrfree(resultant(xl[i],xl[j],s),{var});
            else f3:=f3*xl[i];
            fi;
         od;
      od;
   fi;
   f3:=f3*pwrfree(resultant(xl[n],diff(xl[n],s),s),{var});
   f4:=pwrfr(f3,{var});
   n:=nops(f4); xl:=[];

print(`the border curves have `.n.` factors`);
   for i to n do xl:=[op(xl),[nops(f4[i]),degree(f4[i])]];od;
print(`output the factor-list of the border curves`,time());
print(op(xl));
   if n=1 then
      f3:=f4[1];
      readlib(realroot):
      xl:=realroot(f3);
      n:=nops(xl);
      inf:=[]: sup:=[]:
      for i to n do
         inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
      od;
      inf:=sort(inf);sup:=sort(sup);
      temp:=1;
      for i to n-1 while temp=1 do
         if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
      od;
      m:=1;
      while temp=-1 do
         xl:=realroot(f3,2^(-m));
         n:=nops(xl);
         inf:=[]: sup:=[]:
         for i to n do
            inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
         od;
         inf:=sort(inf);sup:=sort(sup);
         temp:=1;
         for i to n-1 while temp=1 do
            if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
         od;
         m:=m+1;
      od;
      xl:=sup;
      for i to n-1 do
         if inf[i]=sup[i] then xl:=subsop(i=(inf[i+1]+sup[i])/2,xl);fi;
      od;
      if inf[n]=sup[n] then xl:=subsop(n=sup[n]+1,xl);fi;
      xl:=[inf[1]-1,op(xl)];

   else
      xl:=findsamp(f4,var);
   fi;
   n:=nops(xl);  
   #while xl[1]<0 and xl[2]<0 do xl:=subsop(1=NULL,xl) od:
   #n:=nops(xl):

print(`the number of test points is `,n);
print(`output the test points of `.var.` and doing test`,time());
print(xl);

   f1:=p1;f2:=p2;
   ep1:=lhs(ineq);ep2:=rhs(ineq);
   
	nret:=[];
	bstop:=0;
	for i from 1 to n while bstop = 0 do
print(cat(var,`=`,xl[i]));		
    if args[2]=[] then
       if iscgr(args[1])=1 then tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2));
       else
          tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2),subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    else
       if iscgr(args[1])=1 then tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2]);
       else
          tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2],subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    fi;
    if tt<>`less` then nret:=[op(nret),0];
    else nret:=[op(nret),1];
    fi;

		if sum('nret[k]',k=1..nops(nret))<>nops(nret) and sum('nret[k]',k=1..nops(nret))<>0 then
			bstop:=1;
		fi;
	od;

lprint(`OUTPUT RESULT:`);
	i:=i-1;

	if bstop = 0 then
		if sum('nret[k]',k=1..nops(nret))>0 then
			lprint(`The inequality holds for any `.var);
		else
			lprint(`The inequality does not hold for any `.var); 
		fi;
	else

		if nret[i] = 0 then
			lprint(`The minimum value of variable `.var.` is the negative infinity.`);
		else
			temp:=1;
	    for j to nops(f4) while temp=1 do
	    	if testroot(f4[j],var,xl[i-1],xl[i])<>[] then f3:=f4[j];temp:=0;fi;
	    od;    
	    lprint(`The best possible minimal const `.var.` is a root of the following polynomial :`);
	    lprint(f3);
	    lprint(`which is between （`,xl[i-1],`，`,xl[i],`）`);			
	  fi;
	fi;   
   
end:

cmax:=proc(ineq,list1,var)
   local i,j,n,p1,p2,f1,f2,f3,f4,xl,inf,sup,m,temp,iq,tt,flag1,flag2,xsh,dl,ep1,ep2,iqlst,nret,bstop;
   global gg,aa,hh;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:
   
   dl:=data():

   if (cyclicornot(ineq)<>1) or (args[2]<>[aa] and args[2]<>[]) then 
   	iqlst:=[ineq];
      for i to nops(args[2]) do
         if not (type(args[2][i],`<`) or type(args[2][i],`<=`)) then
            if args[2][i]=aa then iqlst:=[op(iqlst),(x-1)*(y-1)*(z-1)>=0];else iqlst:=[op(iqlst),args[2][i]>=0];fi;
         else iqlst:=[op(iqlst),args[2][i]];
         fi;
      od;
		iqlst:=map(expand,iqlst);
		iqlst:=subs(dl,iqlst);
      xmax(subs(z=(x+y)/(x*y-1),subs(dl,iqlst[1])),[x*y>1,op(subs(z=(x+y)/(x*y-1),subs(dl,subsop(1=NULL,iqlst))))],var);
      RETURN();
   fi;

   #if args[2]<>[aa] and args[2]<>[] then RETURN(`invalid second argument`);fi;
print(`Start to find the border curves of `.var,time());
   p1:=subs(var=_xk,lhs(ineq));
   p2:=subs(var=_xk,rhs(ineq));
   p1:=psTpoly(p1);
   p2:=psTpoly(p2);
   p1:=subs(q=s^2-4*p-27,p1);
   p2:=subs(q=s^2-4*p-27,p2);
   p1:=subs(_xk=var,p1);
   p2:=subs(_xk=var,p2);
   f1:=numer(resultant(p1,p2,T));
   f1:=pwrfree(f1,{p,s,var});
   f2:=gg;
   if args[2]<>[] then
      n:=nops(list1);
      for i to n do f2:=f2*subs(T=0,psTpoly(list1[i]));od;
   fi;
   f4:=gcd(f1,f2);
   f1:=f1/f4;f2:=f2/f4;
   f3:=resultant(f1,f2,p);
   if f3=0 then f3:=1;fi;

   xl:=pwrfr(f1*f4,{p,s,var});
   for i to nops(xl) do xsh:=resultant(xl[i],diff(xl[i],p),p);if xsh<>0 then f3:=f3*xsh;fi;od;
   xl:=pwrfr(f2*f4,{p,s,var});
   for i to nops(xl) do xsh:=resultant(xl[i],diff(xl[i],p),p);if xsh<>0 then f3:=f3*xsh;fi;od;

   xl:=pwrfr(f3,{s,var});
   n:=nops(xl);
   f3:=1;
   if n>1 then
      for i to n-1 do
         f3:=f3*pwrfree(resultant(xl[i],diff(xl[i],s),s),{var});
         for j from i+1 to n do
            if has(xl[i],s) or has(xl[j],s) then f3:=f3*pwrfree(resultant(xl[i],xl[j],s),{var});
            else f3:=f3*xl[i];
            fi;
         od;
      od;
   fi;
   f3:=f3*pwrfree(resultant(xl[n],diff(xl[n],s),s),{var});

   f4:=pwrfr(f3,{var});
   n:=nops(f4);xl:=[];
print(`the border curves have `.n.` factors`);
   for i to n do xl:=[op(xl),[nops(f4[i]),degree(f4[i])]];od;
print(`output the factor-list of the border curves`,time());
print(op(xl));

   if n=1 then
      f3:=f4[1];
      readlib(realroot):
      xl:=realroot(f3);
      n:=nops(xl);
      inf:=[]: sup:=[]:
      for i to n do
         inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
      od;
      inf:=sort(inf);sup:=sort(sup);
      temp:=1;
      for i to n-1 while temp=1 do
         if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
      od;
      m:=1;
      while temp=-1 do
         xl:=realroot(f3,2^(-m));
         n:=nops(xl);
         inf:=[]: sup:=[]:
         for i to n do
            inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
         od;
         inf:=sort(inf);sup:=sort(sup);
         temp:=1;
         for i to n-1 while temp=1 do
            if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
         od;
         m:=m+1;
      od;
      xl:=sup;
      for i to n-1 do
         if inf[i]=sup[i] then xl:=subsop(i=(inf[i+1]+sup[i])/2,xl);fi;
      od;
      if inf[n]=sup[n] then xl:=subsop(n=sup[n]+1,xl);fi;
      xl:=[inf[1]-1,op(xl)];
   else xl:=findsamp(f4,var);
   fi;
   n:=nops(xl);
   #while xl[1]<0 and xl[2]<0 do xl:=subsop(1=NULL,xl) od:
   #n:=nops(xl):

print(`the number of test points is `,n);
print(`output the test points of `.var.` and doing test`,time());
print(xl);

   f1:=p1;f2:=p2;
   ep1:=lhs(ineq);ep2:=rhs(ineq);
   
	nret:=[];
	bstop:=0;
	for i from n to 1 by -1 while bstop = 0 do
print(cat(var,`=`,xl[i]));		
    if args[2]=[] then
       if iscgr(args[1])=1 then tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2));
       else
          tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2),subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    else
       if iscgr(args[1])=1 then tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2]);
       else
          tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2],subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    fi;
		if tt=`less` then nret:=[op(nret),1];
		else nret:=[op(nret),0];
		fi;

		if sum('nret[k]',k=1..nops(nret))<>nops(nret) and sum('nret[k]',k=1..nops(nret))<>0 then
			bstop:=1;
		fi;
	od;

lprint(`OUTPUT RESULT:`);
	i:=i+1;

	if bstop = 0 then
		if sum('nret[k]',k=1..nops(nret))>0 then
			lprint(`The inequality holds for any `.var);
		else
			lprint(`The inequality does not hold for any `.var); 
		fi;
	else

		if nret[nops(nret)] = 0 then
			lprint(`The maximal value of variable `.var.` is the positive infinity.`);
		else
			temp:=1;
	    for j to nops(f4) while temp=1 do
	    	if testroot(f4[j],var,xl[i],xl[i+1])<>[] then f3:=f4[j];temp:=0;fi;
	    od;    
	    lprint(`The best possible maximal const `.var.` is a root of the following polynomial :`);
	    lprint(f3);
	    lprint(`which is between （`,xl[i],`，`,xl[i+1],`）`);			
	  fi;
	fi;   
 
end:

xmin:=proc(ineq,list1,list2)
   local i,m,m1,m2,n,mm,xl,yl,curves,pointl,plist,k,its,temp,
   nn,vars,f1,f2,f3,f4,p1,p2,tt,var,flag1,flag2,j,bstop,nret;

   curves:=lhs(ineq)-rhs(ineq);
   if list1<>[] then
      xl:=args[2];
      m:=nops(xl);
      for i to m do
         curves:=curves*(lhs(xl[i])-rhs(xl[i]));
      od;
   fi;
   curves:=expand(numer(curves)*denom(curves));

   while hastype(curves,radical) do
      curves:=rads(curves);
   od;
   its:=[op(indets(curves))];
   xl:=discardpl(curves);
   n:=nops(xl);curves:=1;
   for i to n do
      temp:=[coeffs(xl[i])];
      if changenum(temp)<>0 then curves:=curves*xl[i];fi;
   od;

   curves:=curves*product(its[k],k=1..nops(its));

   var:=list2;

   print(`Start to find the border curves of `.var,time());

   plist:=proj(curves*curves,[list2]);

   n:=nops(plist);

#  print(plist[n][1]);
   print(`found the border curves.`);

   f4:=pwrfr(plist[n][1],{plist[n][2][1]});

   pointl:=findsamp(f4,plist[n][2][1]);
   n:=nops(pointl);
   xl:=[];
   for i to n do xl:=[op(xl),pointl[i]];od;
   xl:=sort(xl);
print(cat(`output the test points of `,var,` and doing test`),time());
print(xl);

	f1:=args[1];f2:=args[2];
	nret:=[];
	bstop:=0;
	for i from 1 to n while bstop = 0 do
print(cat(var,`=`,xl[i]));		
	  if args[2]=[] then  tt:=xprove(subs(var=xl[i],f1),[],iireturn);
	  else  tt:=xprove(subs(var=xl[i],f1),subs(var=xl[i],f2),iireturn);
	  fi;
		if tt[1] = 1 then nret:=[op(nret),1];
		else nret:=[op(nret),0];
		fi;

		if sum('nret[k]',k=1..nops(nret))<>nops(nret) and sum('nret[k]',k=1..nops(nret))<>0 then
			bstop:=1;
		fi;
	od;

lprint(`OUTPUT RESULT:`);
	i:=i-1;

	if bstop = 0 then
		if sum('nret[k]',k=1..nops(nret))>0 then
			lprint(`The inequality holds for any `.var);
		else
			lprint(`The inequality does not hold for any `.var); 
		fi;
	else

		if nret[i] = 0 then
			lprint(`The minimum value of variable `.var.` is the negative infinity.`);
		else
			temp:=1;
	    for j to nops(f4) while temp=1 do
	    	if testroot(f4[j],var,xl[i-1],xl[i])<>[] then f3:=f4[j];temp:=0;fi;
	    od;    
	    lprint(`The best possible minimal const `.var.` is a root of the following polynomial :`);
	    lprint(f3);
	    lprint(`which is between （`,xl[i-1],`，`,xl[i],`）`);			
	  fi;
	fi;

end:

xmax:=proc(ineq,list1,list2)
   local i,m,m1,m2,n,mm,xl,yl,curves,pointl,plist,k,its,temp,
   nn,vars,f1,f2,f3,f4,p1,p2,tt,var,flag1,flag2,j,bstop,nret;

   curves:=lhs(ineq)-rhs(ineq);
   if list1<>[] then
      xl:=args[2];
      m:=nops(xl);
      for i to m do
         curves:=curves*(lhs(xl[i])-rhs(xl[i]));
      od;
   fi;
   curves:=expand(numer(curves)*denom(curves));

   while hastype(curves,radical) do
      curves:=rads(curves);
   od;
   its:=[op(indets(curves))];
   xl:=discardpl(curves);
   n:=nops(xl);curves:=1;
   for i to n do
      temp:=[coeffs(xl[i])];
      if changenum(temp)<>0 then curves:=curves*xl[i];fi;
   od;

   curves:=curves*product(its[k],k=1..nops(its));

   var:=list2;

   print(`Start to find the border curves of `.var,time());

   plist:=proj(curves,[list2]);

   n:=nops(plist);

#  print(plist[n][1]);
   print(`found the border curves.`);

   f4:=pwrfr(plist[n][1],{plist[n][2][1]});
   pointl:=findsamp(f4,plist[n][2][1]);
   n:=nops(pointl);
   xl:=[];
   for i to n do xl:=[op(xl),pointl[i]];od;
   xl:=sort(xl);
print(f4);
print(`output the test points of `.var.` and doing test`,time());
print(xl);


	f1:=args[1];f2:=args[2];
	nret:=[];
	bstop:=0;
	for i from n to 1 by -1 while bstop = 0 do
print(cat(var,`=`,xl[i]));		
	  if args[2]=[] then  tt:=xprove(subs(var=xl[i],f1),[],iireturn);
	  else  tt:=xprove(subs(var=xl[i],f1),subs(var=xl[i],f2),iireturn);
	  fi;
		if tt[1]=1 then nret:=[op(nret),1];
		else nret:=[op(nret),0];
		fi;

		if sum('nret[k]',k=1..nops(nret))<>nops(nret) and sum('nret[k]',k=1..nops(nret))<>0 then
			bstop:=1;
		fi;
	od;

lprint(`OUTPUT RESULT:`);
	i:=i+1;

	if bstop = 0 then
		if sum('nret[k]',k=1..nops(nret))>0 then
			lprint(`The inequality holds for any `.var);
		else
			lprint(`The inequality does not hold for any `.var); 
		fi;
	else

		if nret[nops(nret)] = 0 then
			lprint(`The maximal value of variable `.var.` is the positive infinity.`);
		else
			temp:=1;
	    for j to nops(f4) while temp=1 do
	    	if testroot(f4[j],var,xl[i],xl[i+1])<>[] then f3:=f4[j];temp:=0;fi;
	    od;    
	    lprint(`The best possible maximal const `.var.` is a root of the following polynomial :`);
	    lprint(f3);
	    lprint(`which is between （`,xl[i],`，`,xl[i+1],`）`);			
	  fi;
	fi;

end:

crival:=proc(iq,clist,var)
   local ls,rs,p1,p2,ps,ds,ns,dq,pq,cr,np,cc,i,co,sn,nq,pr,j,cv,ineq:

   ineq:=subs(var=_xk,iq):
   ls:=lhs(ineq):
   rs:=rhs(ineq):
   p1:=psTpoly(ls):
   p2:=psTpoly(rs):
   p1:=subs(_xk=var,p1):
   p2:=subs(_xk=var,p2):

   ps:=resultant(p1,p2,T):
   ps:=pwrfree(ps,{var}):
print(ps):
   pq:=subs(s=sqrt(q+4*p+27),ps):
   if type(pq,polynom)=false then
      ds:=expand(diff(ps,s)):
      co:=[coeffs(ds)]:
      sn:=map(primpart,co):
      nq:=nops(co):
      pr:=1:
      for j to nq-1 while pr<>0 do
         pr:=pr*(sn[1]+sn[j+1]):
      od:
      if pr<>0 then 
         print(ds):
         print(`No critical point in the interior`):
         RETURN([])
      fi:
      cr:=resultant(ps,diff(ps,s),s)#cr:=discrim(ps,s)
   else
      dq:=expand(diff(pq,q)):
      co:=[coeffs(dq)]:
      sn:=map(primpart,co):
      nq:=nops(co):
      pr:=1:
      for j to nq-1 while pr<>0 do
         pr:=pr*(sn[1]+sn[j+1]):
      od:
      if pr<>0 then 
         print(dq):
         print(`No critical point in the interior`):
         RETURN([])
      fi:
      cr:=resultant(pq,diff(pq,q),q)#cr:=discrim(pq,q)
   fi:
   
   cr:=pwrfr(cr,{var}):
   np:=nops(cr):
   cc:=1:
   for i to np do
      co:=[coeffs(cr[i])]:
      sn:=map(primpart,co):
      nq:=nops(co):
      pr:=1:
      for j to nq-1 while pr<>0 do
         pr:=pr*(sn[1]+sn[j+1]):
      od:
      if pr=0 then cc:=cc*cr[i] fi:
   od:
   cv:=resultant(cc,diff(cc,p),p):#discrim(cc,p):
   cv:=pwrfr(cc,{var}):
   if cv=[] then 
      print(cv):
      print(`No critical point in the interior`)
   fi:
   RETURN(cv)
end:

findmax:=proc(ineq,clist,var)
    local cr,cma:
    
    cr:=crival(ineq,clist,var):

    if cr=[] then cma:=ccmax(ineq,clist,var)
    else cma:=cmax(ineq,clist,var)
    fi:
    RETURN(cma)
end:

findmin:=proc(ineq,clist,var)
    local cr,cmi:
    
    cr:=crival(ineq,clist,var):
    if cr=[] then cmi:=ccmin(ineq,clist,var):
    else cmi:=cmin(ineq,clist,var):
    fi:
    RETURN(cmi)
end:

ccmax:=proc(ineq,list1,var)
   local i,j,n,p1,p2,f1,f2,f3,f4,xl,inf,sup,m,temp,iq,tt,dl,iqlst,nret,bstop,ep1,ep2;
   global gg,aa,hh;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:

   #if args[2]<>[aa] and args[2]<>[] then RETURN(`invalid second argument`);fi;
   dl:=data():
   if args[2]<>[aa] and args[2]<>[] then 
   	
   	iqlst:=[ineq];
      for i to nops(args[2]) do
         if not (type(args[2][i],`<`) or type(args[2][i],`<=`)) then
            if args[2][i]=aa then iqlst:=[op(iqlst),(x-1)*(y-1)*(z-1)>=0]; else iqlst:=[op(iqlst),args[2][i]>=0];fi;
         else iqlst:=[op(iqlst),args[2][i]];
         fi;
      od;
		iqlst:=map(expand,iqlst);
		iqlst:=subs(dl,iqlst);
      xmax(subs(z=(x+y)/(x*y-1),subs(dl,iqlst[1])),[x*y>1,op(subs(z=(x+y)/(x*y-1),subs(dl,subsop(1=NULL,iqlst))))],var);
      RETURN();
   fi;
   
print(`Start to find the border curves of `.var,time());
   p1:=subs(var=_xk,lhs(ineq));
   p2:=subs(var=_xk,rhs(ineq));
   p1:=psTpoly(p1);
   p2:=psTpoly(p2);
   p1:=subs(q=s^2-4*p-27,p1);
   p2:=subs(q=s^2-4*p-27,p2);
   p1:=subs(_xk=var,p1);
   p2:=subs(_xk=var,p2);
   f1:=numer(resultant(p1,p2,T));
   f1:=pwrfree(f1,{p,s,var});
   f2:=gg;
   if args[2]<>[] then
      n:=nops(list1);
      for i to n do f2:=f2*subs(T=0,psTpoly(list1[i]));od;
   fi;
   f4:=gcd(f1,f2);
   f1:=f1/f4;f2:=f2/f4;
   f3:=resultant(f1,f2,p);
   xl:=pwrfr(f3,{s,var});
   n:=nops(xl);
   f3:=1;
   if n>1 then
      for i to n-1 do
         f3:=f3*pwrfree(resultant(xl[i],diff(xl[i],s),s),{var});
         for j from i+1 to n do
            if has(xl[i],s) or has(xl[j],s) then f3:=f3*pwrfree(resultant(xl[i],xl[j],s),{var});
            else f3:=f3*xl[i];
            fi;
         od;
      od;
   fi;
   f3:=f3*pwrfree(resultant(xl[n],diff(xl[n],s),s),{var});

   f4:=pwrfr(f3,{var});
   n:=nops(f4);xl:=[];
print(`the border curves have `.n.` factors`);
   for i to n do xl:=[op(xl),[nops(f4[i]),degree(f4[i])]];od;
print(`output the factor-list of the border curves`,time());
print(op(xl));

   if n=1 then
      f3:=f4[1];
      readlib(realroot):
      xl:=realroot(f3);
      n:=nops(xl);
      inf:=[]: sup:=[]:
      for i to n do
         inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
      od;
      inf:=sort(inf);sup:=sort(sup);
      temp:=1;
      for i to n-1 while temp=1 do
         if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
      od;
      m:=1;
      while temp=-1 do
         xl:=realroot(f3,2^(-m));
         n:=nops(xl);
         inf:=[]: sup:=[]:
         for i to n do
            inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
         od;
         inf:=sort(inf);sup:=sort(sup);
         temp:=1;
         for i to n-1 while temp=1 do
            if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
         od;
         m:=m+1;
      od;
      xl:=sup;
      for i to n-1 do
         if inf[i]=sup[i] then xl:=subsop(i=(inf[i+1]+sup[i])/2,xl);fi;
      od;
      if inf[n]=sup[n] then xl:=subsop(n=sup[n]+1,xl);fi;
      xl:=[inf[1]-1,op(xl)];
   else xl:=findsamp(f4,var);
   fi;
   
   n:=nops(xl);
   #while xl[1]<0 and xl[2]<0 do xl:=subsop(1=NULL,xl) od:
   #n:=nops(xl):
print(`the number of test points is `,n);
print(`output the test points of `.var.` and doing test`,time());
print(xl);

   f1:=p1;f2:=p2;
   ep1:=lhs(ineq);ep2:=rhs(ineq);
   
	nret:=[];
	bstop:=0;
	for i from n to 1 by -1 while bstop = 0 do
print(cat(var,`=`,xl[i]));		
    if args[2]=[] then
       if iscgr(args[1])=1 then tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2));
       else
          tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2),subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    else
       if iscgr(args[1])=1 then tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2]);
       else
          tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2],subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    fi;
		if tt=`less` then nret:=[op(nret),1];
		else nret:=[op(nret),0];
		fi;

		if sum('nret[k]',k=1..nops(nret))<>nops(nret) and sum('nret[k]',k=1..nops(nret))<>0 then
			bstop:=1;
		fi;
	od;

lprint(`OUTPUT RESULT:`);
	i:=i+1;

	if bstop = 0 then
		if sum('nret[k]',k=1..nops(nret))>0 then
			lprint(`The inequality holds for any `.var);
		else
			lprint(`The inequality does not hold for any `.var); 
		fi;
	else

		if nret[nops(nret)] = 0 then
			lprint(`The maximal value of variable `.var.` is the positive infinity.`);
		else
			temp:=1;
	    for j to nops(f4) while temp=1 do
	    	if testroot(f4[j],var,xl[i],xl[i+1])<>[] then f3:=f4[j];temp:=0;fi;
	    od;    
	    lprint(`The best possible maximal const `.var.` is a root of the following polynomial :`);
	    lprint(f3);
	    lprint(`which is between （`,xl[i],`，`,xl[i+1],`）`);			
	  fi;
	fi;   

end:

ccmin:=proc(ineq,list1,var)
   local i,j,n,p1,p2,f1,f2,f3,f4,xl,inf,sup,m,temp,iq,tt,dl,iqlst,nret,bstop,ep1,ep2;
   global gg,aa,hh;

   gg:=54*s^2+9*s^2*p+1/4*s^2*p^2-s^4-p^3-27*p^2-243*p-729:
   hh:=-p^2+4*p*q+p^2*q-4*q^2:
   aa:=2*s-p-10:
   #if args[2]<>[aa] and args[2]<>[] then RETURN(`invalid second argument`);fi;
   dl:=data():
   if args[2]<>[aa] and args[2]<>[] then 
   	
   	iqlst:=[ineq];
      for i to nops(args[2]) do
         if not (type(args[2][i],`<`) or type(args[2][i],`<=`)) then
            if args[2][i]=aa then iqlst:=[op(iqlst),(x-1)*(y-1)*(z-1)>=0]; else iqlst:=[op(iqlst),args[2][i]>=0];fi;
         else iqlst:=[op(iqlst),args[2][i]];
         fi;
      od;
		iqlst:=map(expand,iqlst);
		iqlst:=subs(dl,iqlst);
      xmin(subs(z=(x+y)/(x*y-1),subs(dl,iqlst[1])),[x*y>1,op(subs(z=(x+y)/(x*y-1),subs(dl,subsop(1=NULL,iqlst))))],var);
      RETURN();
   fi;
   
print(`Start to find the border curves of `.var,time());
   p1:=subs(var=_xk,lhs(ineq));
   p2:=subs(var=_xk,rhs(ineq));
   p1:=psTpoly(p1);
   p2:=psTpoly(p2);
   p1:=subs(q=s^2-4*p-27,p1);
   p2:=subs(q=s^2-4*p-27,p2);
   p1:=subs(_xk=var,p1);
   p2:=subs(_xk=var,p2);
   f1:=resultant(p1,p2,T);
   f1:=pwrfree(f1,{p,s,var});
   f2:=gg;
   if args[2]<>[] then
      n:=nops(list1);
      for i to n do f2:=f2*subs(T=0,psTpoly(list1[i]));od;
   fi;
   f4:=gcd(f1,f2);
   f1:=f1/f4;f2:=f2/f4;
   f3:=resultant(f1,f2,p);
   xl:=pwrfr(f3,{s,var});
   n:=nops(xl);
   f3:=1;
   if n>1 then
      for i to n-1 do
         f3:=f3*pwrfree(resultant(xl[i],diff(xl[i],s),s),{var});
         for j from i+1 to n do
            if has(xl[i],s) or has(xl[j],s) then
               f3:=f3*pwrfree(resultant(xl[i],xl[j],s),{var});
            else f3:=f3*xl[i];
            fi;
         od;
      od;
   fi;
   f3:=f3*pwrfree(resultant(xl[n],diff(xl[n],s),s),{var});
   f4:=pwrfr(f3,{var});
   n:=nops(f4); xl:=[];
print(`the border curves have `.n.` factors`);
   for i to n do xl:=[op(xl),[nops(f4[i]),degree(f4[i])]];od;
print(`output the factor-list of the border curves`,time());
print(op(xl));

   if n=1 then
      f3:=f4[1];
      readlib(realroot):
      xl:=realroot(f3);
      n:=nops(xl);
      inf:=[]: sup:=[]:
      for i to n do
         inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
      od;
      inf:=sort(inf);sup:=sort(sup);
      temp:=1;
      for i to n-1 while temp=1 do
         if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
      od;
      m:=1;
      while temp=-1 do
         xl:=realroot(f3,2^(-m));
         n:=nops(xl);
         inf:=[]: sup:=[]:
         for i to n do
            inf:=[op(inf),xl[i][1]];sup:=[op(sup),xl[i][2]];
         od;
         inf:=sort(inf);sup:=sort(sup);
         temp:=1;
         for i to n-1 while temp=1 do
            if inf[i]=inf[i+1] or sup[i]=sup[i+1] then temp:=-1;fi;
         od;
         m:=m+1;
      od;
      xl:=sup;
      for i to n-1 do
         if inf[i]=sup[i] then xl:=subsop(i=(inf[i+1]+sup[i])/2,xl);fi;
      od;   
      if inf[n]=sup[n] then xl:=subsop(n=sup[n]+1,xl);fi;
      xl:=[inf[1]-1,op(xl)];
   else
      xl:=findsamp(f4,var);
   fi;
   n:=nops(xl);
   #while xl[1]<0 and xl[2]<0 do xl:=subsop(1=NULL,xl) od:
   #n:=nops(xl):
print(`the number of test points is `,n);
print(`output the test points of `.var.` and doing test`,time());
print(xl);

   f1:=p1;f2:=p2;
   ep1:=lhs(ineq);ep2:=rhs(ineq);
   
	nret:=[];
	bstop:=0;
	for i from 1 to n while bstop = 0 do
print(cat(var,`=`,xl[i]));		
    if args[2]=[] then
       if iscgr(args[1])=1 then tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2));
       else
          tt:=test(subs(var=xl[i],f1),subs(var=xl[i],f2),subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    else
       if iscgr(args[1])=1 then tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2]);
       else
          tt:=ctest(subs(var=xl[i],f1),subs(var=xl[i],f2),args[2],subs(dl,subs(var=xl[i],ep1)),subs(dl,subs(var=xl[i],ep2)));
       fi;
    fi;
    if tt<>`less` then nret:=[op(nret),0];
    else nret:=[op(nret),1];
    fi;

		if sum('nret[k]',k=1..nops(nret))<>nops(nret) and sum('nret[k]',k=1..nops(nret))<>0 then
			bstop:=1;
		fi;
	od;

lprint(`OUTPUT RESULT:`);
	i:=i-1;

	if bstop = 0 then
		if sum('nret[k]',k=1..nops(nret))>0 then
			lprint(`The inequality holds for any `.var);
		else
			lprint(`The inequality does not hold for any `.var); 
		fi;
	else

		if nret[i] = 0 then
			lprint(`The minimum value of variable `.var.` is the negative infinity.`);
		else
			temp:=1;
	    for j to nops(f4) while temp=1 do
	    	if testroot(f4[j],var,xl[i-1],xl[i])<>[] then f3:=f4[j];temp:=0;fi;
	    od;    
	    lprint(`The best possible minimal const `.var.` is a root of the following polynomial :`);
	    lprint(f3);
	    lprint(`which is between （`,xl[i-1],`，`,xl[i],`）`);			
	  fi;
	fi;   
	
end:

fmin:=proc(ob,vol1,vol2,dig,var,opt)
   local u,v,w,d,g,i,pr,p1,p2:
   
   u:=vol1: v:=vol2:
   g:=v-u:
   d:=dig:

   p1:=subs(var=_xk,lhs(ob));p2:=subs(var=_xk,rhs(ob));
   p1:=psTpoly(p1);p2:=psTpoly(p2);
   p1:=subs(q=s^2-4*p-27,p1);p2:=subs(q=s^2-4*p-27,p2);
   p1:=subs(_xk=var,p1);p2:=subs(_xk=var,p2);

   for i from 1 while g>10^(-d) do
      w:=(u+v)/2:
      if nargs=5 then
         pr:=test(subs(var=w,p1),subs(var=w,p2));
      else
         pr:=ctest(subs(var=w,p1),subs(var=w,p2),opt);
      fi;
      if pr=`less` then v:=w
      else u:=w
      fi:
      g:=v-u:
      print(u,`< the smallest value <`,v):
      print(evalf(u,d+2),`< the smallest value <`,evalf(v,d+2)):
      lprint(`The `.i.`th Step is completed.`):
      save u,v, result:
   od:

   RETURN(ob,u,v):
end:

xfmin:=proc(ob,vol1,vol2,dig,k,opt)
   local u,v,w,d,g,i,pr:
   
   u:=vol1: v:=vol2:
   g:=v-u:
   d:=dig:
   for i from 1 while g>10^(-d) do
      w:=(u+v)/2:
      if nargs=5 then pr:=xprove(subs(k=w,ob),[],rreturn)
      else pr:=xprove(subs(k=w,ob),opt,rreturn)
      fi:
      if pr[1]=1 then v:=w
      else u:=w
      fi:
      g:=v-u:
      print(u,`< the smallest value <`,v):
      print(evalf(u,d+2),`< the smallest value <`,evalf(v,d+2)):
      lprint(`The `.i.`th Step is completed.`):
      save u,v, result:
   od:
   RETURN(ob,u,v):
end:

fmax:=proc(ob,vol1,vol2,dig,var,opt)
   local u,v,w,d,g,i,pr,p1,p2:
   
   u:=vol1: v:=vol2:
   g:=v-u:
   d:=dig:
   p1:=subs(var=_xk,lhs(ob));p2:=subs(var=_xk,rhs(ob));
   p1:=psTpoly(p1);p2:=psTpoly(p2);
   p1:=subs(q=s^2-4*p-27,p1);p2:=subs(q=s^2-4*p-27,p2);
   p1:=subs(_xk=var,p1);p2:=subs(_xk=var,p2);

   for i from 1 while g>10^(-d) do
      w:=(u+v)/2:
      if nargs=5 then
         pr:=test(subs(var=w,p1),subs(var=w,p2));
      else
         pr:=ctest(subs(var=w,p1),subs(var=w,p2),opt);
      fi;
      if pr=`less` then u:=w
      else v:=w
      fi:
      g:=v-u:
      print(u,`< the greatest value <`,v):
      print(evalf(u,d+2),`< the greatest value <`,evalf(v,d+2)):
      lprint(`The `.i.`th Step is completed.`):
      save u,v, result:
   od:
   RETURN(ob,u,v):
end:

xfmax:=proc(ob,vol1,vol2,dig,k,opt)
   local u,v,w,d,g,i,pr:
   
   u:=vol1: v:=vol2:
   g:=v-u:
   d:=dig:
   for i from 1 while g>10^(-d) do
      w:=(u+v)/2:
      if nargs=5 then pr:=xprove(subs(k=w,ob),[],rreturn)
      else pr:=xprove(subs(k=w,ob),opt,rreturn)
      fi:
      if pr[1]=1  then u:=w
      else v:=w
      fi:
      g:=v-u:
      print(u,`< the greatest value <`,v):
      print(evalf(u,d+2),`< the greatest value <`,evalf(v,d+2)):
      lprint(`The `.i.`th Step is completed.`):
      save u,v, result:
   od:
   RETURN(ob,u,v):
end:

elimfracrad:=proc(crv)
local tmp,i,n,its,x;

	its:=indets(crv,radical);
	its:=[op(its)];
	if its=[] then RETURN(crv);fi;
	n:=nops(its);tmp:=crv;
	for i to n do
		x:=its[i];
		tmp:=subs(x=numer(op(1,x))^op(2,x)/denom(op(1,x))^op(2,x),tmp);
	od;
	tmp
end:

testf:=proc(ineq,trig) 
local x1,y1,z1,s1,dbs,ex,ev,k,n,a1,b1,c1; 

if nargs<2 then ERROR(`Invalid input arguments.`) fi; 
if not type(args[2],`list`) then ERROR(`Invalid second argument.`) fi; 

dbs:=data(); 
ex:=lhs(ineq)-rhs(ineq); 
ex:=subs(dbs,expand(ex)); 

if indets(ex) minus indets(ex,`radical`) minus {x,y,z}<>{} then RETURN(`Please refresh the database.`) fi; 

a1:=trig[1]; 
b1:=trig[2]; 
c1:=trig[3]; 
s1:=(a1+b1+c1)/2; 
x1:=s1-a1; 
y1:=s1-b1; 
z1:=s1-c1; 

if not evalb(x1>0) then ERROR(`The second argument cannot construct a triangle.`);fi; 
if not evalb(y1>0) then ERROR(`The second argument cannot construct a triangle.`);fi; 
if not evalb(z1>0) then ERROR(`The second argument cannot construct a triangle.`);fi; 

k:=sqrt((x1+y1+z1)/x1/y1/z1); 
x1:=k*x1; 
y1:=k*y1; 
z1:=k*z1; 

n:=Digits; 
if nargs=3 then n:=args[3];fi; 
ex:=evalf(subs({x=x1,y=y1,z=z1},ex),n); 
ev:=evalb(ex<=0); 
RETURN(ev,ex) 
end: 

  


 #########################################
 #    $ 齐5次变元取非负实数的多项式 $    #
 #                                       #
 #########################################

  
 
  #sprove51用于5次对称多项式的半正定判定(用常规表达式)
  #n1为变元个数,a1,b1,c1,d1,e1,g1,h1分别是项x[1]^5,x[1]^4*x[2],x[1]^3*x[2]^2,x[1]^3*x[2]*x[3],x[1]^2*x[2]^2*x[3], x[1]^2*x[2]*x[3]*x[4],x[1]*x[2]*x[3]*x[4]*x[5]前的系数
    
  p5test:=proc(poly)
        local po,id,np,c1,c2,c3,c4,c5,c6,c7:
          po:=poly:
          id:=indets(po):
          np:=nops(id):
          if np<3 then 
             print(`This is only for polynomials with at least 3 elements`):
             RETURN()
          fi: 
          c1:=coeff(po,id[1]^5):
          c2:=coeff(coeff(po,id[1]^4),id[2]):
          c3:=coeff(coeff(po,id[1]^3),id[2]^2):
          c4:=coeff(coeff(coeff(po,id[1]^3),id[2]),id[3]):
          c5:=coeff(coeff(coeff(po,id[1]^2),id[2]^2),id[3]):
          if np>3 then 
             c6:=coeff(coeff(coeff(coeff(po,id[1]^2),id[2]),id[3]),id[4])
          else c6:=0 
          fi:
          if np>4 then 
             c7:=coeff(coeff(coeff(coeff(coeff(po,id[1]),id[2]),id[3]),id[4]),id[5])
          else c7:=0 
          fi:    #print(c1,c2,c3,c4,c5,c6,c7):
          RETURN(sprove51(np,[c1,c2,c3,c4,c5,c6,c7])):
   end:
 
  #sprove51用于5次对称多项式的半正定判定(用常规表达式)
  #n1为变元个数,a1,b1,c1,d1,e1,g1,h1分别是项x[1]^5,x[1]^4*x[2],x[1]^3*x[2]^2,x[1]^3*x[2]*x[3],x[1]^2*x[2]^2*x[3], x[1]^2*x[2]*x[3]*x[4],x[1]*x[2]*x[3]*x[4]*x[5]前的系数
    
   sprove51:=proc(n1,coff::list)
        local n,a,b,c,d,e,g,h,a1,b1,c1,d1,e1,g1,h1,lis1,sol,P1,P2,P3,P4
            ,P5,f:
          n:=n1:
          a1:=coff[1]:
          b1:=coff[2]:
          c1:=coff[3]:
          d1:=coff[4]:
          e1:=coff[5]:
          g1:=coff[6]:
          h1:=coff[7]:  
          a:=a1-b1+h1/5+e1-c1-g1+d1:
          b:=b1-e1/2-h1/4+g1-d1:
          c:=c1-e1-h1/6+5*g1/6-d1/2:
          d:=d1/2+h1/6-g1/2:
          e:=e1/2+h1/8-g1/2:
          g:=g1/6-h1/12:
          h:=h1/120:
         print(n,[a,b,c,d,e,g,h]):
         sprove52(n,[a,b,c,d,e,g,h]):
         
      end:

  #sprove52用于5次对称多项式的半正定判定(用标准表达式)
  #f=a*P5+b*P4*P1+c*P3*P2+d*P3*P1^2+e*P2^2*P1+g*P2*P1^3+h*P1^5 

    sprove52:=proc(n,coff::list)   
        local a,b,c,d,e,g,h,f,F,A,B,C,Dx,E,H,r1,pt,T,Test,fs,su,g1,g2,nt,i,j,ss,r2,s2,t1,r4,s4,tn5
        ,r0,s0,pt1,de1,de2,de3,A1,nd1,ire,lco,F1,p,q,r,s,E2,p1,q1,r3,s1,de,tde,tn,tn1,tn2,tn3,tn4:
          a:=coff[1]:
          b:=coff[2]:
          c:=coff[3]:
          d:=coff[4]:
          e:=coff[5]:
          g:=coff[6]:
          h:=coff[7]: 
        t1:=time():
        T:=true;
        f:=a*(r*t^5+s)+b*(r*t^4+s)*(r*t+s)+c*(r*t^3+s)*(r*t^2+s)+d*(r*t^3+s)*(r*t+s)^2+e*(r*t^2+s)^2*(r*t+s)+g*(r*t^2+s)*(r*t+s)^3+h*(r*t+s)^5;
        F:=expand(f);
        for r1 from 1 to n do
          A:=lcoeff(subs(r=r1,s=n-r1,F),t): 
          if signum(A)<0 then T:=false:
          RETURN(([r1,1],[n-r1,0])=subs(r=r1,A),T,time()-t1);
          fi:
        od:
        print(Test1,T):
        pt:=ptn(n,5): 
        nt:=nops(pt):
        tn:=0:
        tn1:=0:
        tn2:=0:
        tn3:=0:
        tn4:=0:
        tn5:=0:
        for i to nt do 
            pt1:=pt[i];
            (r0,s0):=op(pt1);
            g1:=subs(r=r0,s=s0,F):
            lco:=signum(lcoeff(g1,t)):
            if lco<0 then print([r0*t,s0],2,g1); 
                  return(`This is not true`,time()-t1) ;fi;
            de1:=dec(g1,t):
               if de1=0 then (tn,tn1):=(tn+1, tn1+1):
               else 
               de2:=prad(g1,t);
               if de2=0 then (tn,tn2):=(tn+1,tn2+1) fi;
               if de2=1 then ire:=irem(de1,2);
                   if ire<>0 then print([r0*t,s0],3,g1); 
                           return(`This is not true`,time()-t1): 
                       else (tn,tn3):=(tn+1,tn3+1);fi;fi;
               if de2=2 then
                    tde:=degree(g1,t);
                    if tde=4 then 
                         F1:=(4,[1,1,0,0]);nd1:=discr(g1,t);
                         if (de1,nd1)<>F1 then print([r0*t,s0],4,g1); 
                               return(`This is not true`,time()-t1);
                       else
                         B:=coeff(g1,t^4);
                         C:=coeff(g1,t^3);
                         Dx:=coeff(g1,t^2);
                         E:=coeff(g1,t);
                         E2:=signum(8*B^2*E+C^3-4*B*C*Dx);
                         if E2<>0 then print([r0*t,s0],4,g1); 
                                return(`This is not true`,time()-t1);
                         else (tn,tn4):=(tn+1,tn4+1);
                         fi;fi;fi;
                   if tde=5 then 
                        F1:=(4,[1,1,1,0,0]);nd1:=discr(g1,t);
                        if (de1,nd1)<>F1 then print([r0*t,s0],5,g1); 
                                 return(`This is not true`,time()-t1);
                      else 
                        A:=coeff(g1,t^5);
                        B:=coeff(g1,t^4);
                        C:=coeff(g1,t^3);
                        Dx:=coeff(g1,t^2);
                        E:=coeff(g1,t);
                        H:=coeff(g1,t,0);
                        p1:=(5*C*A-2*B^2)/(5*A^2);
                        q1:=(25*Dx*A^2+4*B^3-15*C*B*A)/(25*A^3);
                        r3:=(3*B^4-50*Dx*B*A^2+15*C*B^2*A-125*E*A^3)/(125*A^4);
                        s1:=(3125*H*A^4+125*Dx*B^2*A^2+4*B^5-625*E*B*A^3-25*C*B^3*A)/(3125*A^5);
                        E2:=signum(subs(p=p1,q=q1,r4=r3,s4=s1,160*r4^2*p^3+900*q^2*r4^2-48*r4*p^5+60*q^2*p^2*r4+1500*r4*p*s4*q+16*q^2*p^4-1100*q*p^3*s4+625*s4^2*p^2-3375*q^3*s4));
                          if E2=0 then print([r0*t,s0],5,g1); 
                                   return(`This is not true`,time()-t1);
                          else (tn,tn5):=(tn+1,tn5+1);
                          fi;fi;                   
                    else print(i,[r0*t,s0],g1); 
                           return(`This is not true`,time()-t1);fi;fi;
                    if de2>=3 then print([r0*t,s0],5,g1); 
                         return(`This is not true`,time()-t1);fi;fi;od;
            print(tn,tn1,tn2,tn3,tn4,tn5):
            print(Test2,ture,time()-t1);
        end:
   
   #ptn用于计算方程不定方程的正整数解
   ptn:=proc(number,degree)
      local n,m,L,i,j,n1,S,t1:
      n:=number:
      m:=floor(degree/2):  
      L:={}:
      n1:=n:
      for i from 1 to n1 do
         for j from i to n1-i do
              L:=[op(L),[i,j]]:
            od:od;
        L:  
     end: 


  #xdin用于计算给定实序列的符号修定表
  xdin:=proc(list)
    local M,d1,d2,n1,n2,d11,i,n,p1,p2,j1,n3,j2,r;
    M:=list;
    d1:=dic1(M);
    d2:=dic2(M);
    n1:=nops(d1);
    n2:=nops(d2);
    if M<>d1 then 
    d11:=[];
    n:=0;
    for i to n2 do
        p1:=d2[i];
        if p1[1]<>0 then d11:=[op(d11),op(p1)]; n:=n;
          else n:=n+1;
          p2:=d2[i-1];
          if n<=n1 then 
          d11:=[op(d11),op(p2[1]*d1[n])];
          else d11:=[op(d11),op(p1)];fi;
        fi;
    od;
    else d11:=d1;   
    fi;
    d11;
   end:

   # dic1用于计算给定序列的修正部分
    dic1:=proc(list)
     local list1,n1,i,fli,lh,li2,j,li3,k,n2,n3,m;
     list1:=map(abs,list);
     if has(0,list1)<>true then return(list);else
     fli:=[0];
     n1:=nops(list1);
     for i to n1-1 do 
          lh:=abs(signum(list1[i]-list1[i+1]));
          fli:=[op(fli),lh];
      od;
     li2:=[];
     for j to n1 do
        if fli[j]=1 then li2:=[op(li2),j]
        else li2:=[op(li2)];fi;
     od;
     n2:=nops(li2);
     n3:=floor(n2/2)*2;
        if n3<>0 then 
        li3:=[];
        for k to n3/2 do         
          m:=seq((-1)^(floor((i+1)/2)),i=1..(li2[2*k]-li2[2*k-1]));
          li3:=[op(li3),[m]];
        od;
        else return(list);
        fi;
    fi;
  end:

  #dic2用于计算给定序列的变号分段
   dic2:=proc(list)
     local fli,n1,lh,i,j,li2,k,li3,duan,k1,k2;
     fli:=[1];
     n1:=nops(list);
     for i to n1-1 do 
         lh:=abs(signum(list[i]-list[i+1]));
         fli:=[op(fli),lh];
     od:
     li2:=[];
     for j to n1 do
        if fli[j]=1 then li2:=[op(li2),j]
         else li2:=[op(li2)];fi;
    od;
    duan:=[];
    for k to nops(li2)-1 do 
        k1:=li2[k];k2:=li2[k+1]-1;
        li3:=op(k1..k2,list);
        duan:=[op(duan),[li3]];
    od;
    li3:=op(k2+1..n1,list);
    duan:=[op(duan),[li3]];
  end:

  #dec用于计算给定多项式的笛卡尔符号法则(系数变号数)
  dec:=proc(f,x)
     local f1,de,coef,i,coef1,n,j,di,dic,sgi;
     f1:=expand(f);
     de:=degree(f1,x);
     coef:=[];
     for i to de+1 do
        coef1:=signum(coeff(f,x,i-1));
        if coef1<>0 then 
           sgi:=coef1;
           coef:=[sgi,op(coef)];
           else coef:=[op(coef)];
        fi;
     od;
     n:=nops(coef);
     dic:=[];
     for j to n-1 do di:=coef[j]*coef[j+1];
        if di=1 then dic:=[op(dic)];
        else dic:=[op(dic),di] ;
        fi;
     od;
    nops(dic);
  end:      

 
   #discr用于计算多项式判别矩阵的偶阶主子式
   discr:=proc(poly,var)
   local f,g,h,tt,d,bz,i,ar,j,mm,dd;
        f:=expand(poly);
        d:=degree(f,var);
        h:=tt*var^d+diff(f,var);
        bz:=subs(tt=0,bezout(f,h,var));
        ar:=[];
        for i to d do ar:=[op(ar),row(bz,d+1-i..d+1-i)] od;
        mm:=matrix(ar);
        dd:=[];
        for j to d do dd:=[op(dd),det(submatrix(mm,1..j,1..j))] od;
        dd:=map(signum,dd);
   end:
     
   #discr2用于计算多项式的奇阶主子式
   discr2:=proc(poly,var)
   local f,h,d,bz,i,ar,j,mm,dd;
        f:=expand(poly);
        d:=degree(f,var);
        h:=expand(var*diff(f,var));
        bz:=bezout(h,f,var);
        ar:=[];
        for i to d do ar:=[op(ar),row(bz,d+1-i..d+1-i)] od;
        mm:=matrix(ar);
        dd:=[1];
        for j to d do dd:=[op(dd),det(submatrix(mm,1..j,1..j))] od;
        dd:=map(signum,dd);
   end:   

   #prad用于计算多项式的相异正根数目
   prad:=proc(poly,var)
   local uu,vv,dd,i,d,v,xd,num1,k,j,k1:
       uu:=discr(poly,var);
       vv:=discr2(poly,var);
       d:=nops(uu);
       dd:=[];
       for i to d do
           k:=floor((2*i-1)/2):
           k1:=floor(i):
           dd:=[op(dd),(-1)^(k)*vv[i]*uu[i],(-1)^(k1)*uu[i]*vv[i+1]]
       od;
       xd:=xdin(dd);
       num1:=sum(abs(xd[j]),j=1..nops(xd));
       if num1<>nops(xd) then 
       v:=nops(dic2(xd))-2;
       else v:=nops(dic2(xd))-1;
       fi;
       floor(num1/2)-v;
    end:

nprove:=proc()
      local t0,lt,f,m,i,j,g,h,mm:
      t0:=time():
      if nargs=1 then lt:=args else lt:=args[1] fi:
      if nops(lt)=5 then         
         f:=lt[1]*(r*x^4+s)+lt[2]*(r*x^3+s)*(r*x+s)+lt[3]*(r*x^2+s)^2+lt[4]*(r*x^2+s)*(r*x+s)^2+lt[5]*(r*x+s)^4:
      elif nops(lt)=7 then
         f:=lt[1]*(r*x^5+s)+lt[2]*(r*x^4+s)*(r*x+s)+lt[3]*(r*x^3+s)*(r*x^2+s)+lt[4]*(r*x^3+s)*(r*x+s)^2+lt[5]*(r*x^2+s)^2*(r*x+s)+lt[6]*(r*x^2+s)*(r*x+s)^3+lt[7]*(r*x+s)^5:
      else print(`This can only deal with degree 4 or 5`):
         RETURN()
      fi: 
      f:=subs(s=r+t,f):
      if nargs=2 then
         m:=args[2]:
         while not(xprove(f>=0,[r>m])=true) do m:=m+1 od:     
      elif nargs=1 then m:=xmin(f>=0,[r>k],k): 
      fi:
      if m=false then
          print(`The form is not positive semi-definite`): print(time()-t0):
          RETURN()
      elif m=true then 
          print(`The form is positive semi-definite`): print(time()-t0,`seconds`): 
          RETURN()
      else m:=floor(m)
      fi:
      for i to m do
          g:=subs(r=i,f): #print(g):
          if not(xprove(g>=0)=true) then print(`Go on!`):
             mm:=xmin(g>=0,[t>k],k): 
             if type(mm,numeric)=false then
                print(`The form is not positive semi-definite`): print(time()-t0):
                RETURN()
             else
                for j from 0 to mm do
                    h:=expand(subs(t=j,g)): #print(i,j,degree(h)):
                    if type(h,constant)=true then print(`OK`):
                       if type(h,negative)=true then
                          print(`The form is not positive semi-definite`):
                          RETURN()
                       fi
                    elif not(xprove(h>=0)=true) then
                       print(`The form is not positive semi-definite`): print(time()-t0):
                       RETURN()
                    fi
                od
              fi
           fi
       od:  
       print(`The form is positive semi-definite`):
       print(time()-t0,`seconds`):
       RETURN()
end:

detail:=proc(lt)
        if nops(lt)=5 then
           lt[1]*sum(x[k]^4,k = 1 .. n)+lt[2]*sum(x[k]^3,k = 1 .. n)*sum(x[k],k = 1 .. n)+lt[3]*sum(x[k]^2,k = 1 .. n)^2+lt[4]*sum(x[k]^2,k = 1 .. n)*sum(x[k],k = 1 .. n)^2+lt[5]*sum(x[k],k = 1 .. n)^4:
        elif nops(lt)=7 then
           lt[1]*sum(x[k]^5,k=1..n)+lt[2]*sum(x[k]^4,k=1..n)*sum(x[k],k=1..n)+lt[3]*sum(x[k]^3,k=1..n)*sum(x[k]^2,k=1..n)+lt[4]*sum(x[k]^3,k=1..n)*sum(x[k],k=1..n)^2+lt[5]*sum(x[k]^2,k=1..n)^2*sum(x[k],k=1..n)+lt[6]*sum(x[k]^2,k=1..n)*sum(x[k],k=1..n)^3+lt[7]*sum(x[k],k=1..n)^5:
        fi
end:

abel:=proc(polys)
    local ps,np,gs,i:
    ps:=polys:
    if type(ps,polynom)=true then
       gs:=Abel(ps)
    elif type(ps,list)=true then
       np:=nops(ps):
       gs:=[]:
       for i to np do
           gs:=[op(gs),op(Abel(ps[i]))]
       od
    fi:
    if gs=[] then print(`The form is positive semi-definite`):
       RETURN()
    else print(nops(gs)): RETURN(gs)
    fi
end:

with(combinat,permute):

Abel:=proc(poly)
    local po,id,vs,nv,f,F,nF,gs,g,fs,i,h,pl,ff:
    po:=expand(poly):
    id:=indets(po):
    vs:=[op(id)]:  
    nv:=nops(vs):
    if type(po,symmfunc(op(id)))=true then F:=[po]: print(`It is symmetric`)
    else pl:=permute(nv):  
       F:={po}:  
       for i from 2 to nops(pl) do
           ff:=subs({seq(vs[k]=vs[pl[i][k]],k=1..nv)},po):  
           F:={op(F),ff}
       od:
       F:=[op(F)]
    fi: #print(F):
    nF:=nops(F):  
    gs:=[]:
    for i to nF do
        g:=subs(seq(vs[j]=vs[j+1]+pp[j],j=1..nv-1),F[i]):  
        gs:=[op(gs),g]
    od: 
    fs:=[]:
    for i to nF do  
        g:=expand(gs[i]):  
        if type(g,ratpoly(rational))=false then
           g:=collect(g,idets(g),distributed) 
        fi:
        h:=map(signum,[coeffs(g)]):  
        if has(-1,h)=true then 
           g:=subs(seq(pp[j]=vs[j],j=1..nv-1),g):  
           fs:=[op({op(fs),g})]
        fi 
    od:         
    RETURN(fs)
end:  

sprove:=proc(ineq)
        local sp,dg,id,n,iq,sq,ws,r3,r2,r1,r0,pp,cd,fs,i,j,nf,m,g,ns,ex,ss,pt,nt,su:
        if nargs>2 then RETURN(`invalid arguments`)
        elif nargs=2 then
             if not type(args[2],list) then 
                RETURN(`invalid second argument`)
             else print(`A conditional inequality, which will be verified by xprove( )`):
                xprove(args[1],args[2]):
                RETURN()
             fi 
        fi:

        sp:=rhs(ineq)-lhs(ineq):  
        if type(sp,polynom)=false then 
           print(`Warning:  not a polynomial  inequality, which will be verified by xprove( )`):
           xprove(ineq):
           RETURN()
        fi:  
        if type(sp,symmfunc(op(indets(sp))))=false then
           print(`Warning: the expression is not symmetric!`):
           xprove(ineq):
           RETURN()
        fi:
        dg:=degree(sp):
        id:=[op(indets(sp))]: #print(id):
        n:=nops(id):  
        print(`Doing Difference Substitution ...`):    
        sq:=subs(seq(id[k]=id[k+1]+b[k],k=1..n-1),sp): 
        ex:=expand(sq):
        if has(-1,map(signum,[coeffs(ex)]))=true then print(`NONTRIVIAL!`):
        else print(`This is trivial by Difference Substitution`):
             print(`The inequality holds.`):
             RETURN()
        fi:
        if n<=2 then
           xprove(ineq):
           RETURN()
        elif n=3 and dg>=2*n then  
           iq:=subs({id[1]=x,id[2]=y,id[3]=z},ineq):  
           prove(iq): 
           RETURN()
        fi:
        if dg>=2*n then 
           print(`Warning:  sometimes, sprove is not fast if the degree not less than twice the number of elements.`): 
           if member(id[n],indets(ex))=false then
              xprove(ex>=0):
              RETURN()
           elif n=4 then
              ws:=[c4-id[1]*c3+c2*id[1]^2+id[1]^4-c1*id[1]^3, -c3+id[1]^2*id[2]+id[1]*id[2]^2-c1*id[1]*id[2]+c2*id[1]+c2*id[2]
                   +id[1]^3+id[2]^3-c1*id[1]^2-c1*id[2]^2, id[1]*id[2]+id[1]*id[3]+id[2]*id[3]+c2+id[1]^2+id[2]^2+id[3]^2
                   -c1*id[1]-c1*id[2]-c1*id[3], id[1]+id[2]+id[3]+id[4]-c1]: 
              sp:=prem(sp-T,ws[4],id[4]):
              sp:=prem(sp,ws[3],id[3]):
              sp:=prem(sp,ws[2],id[2]):
              sp:=prem(sp,ws[1],id[1]):
              sp:=solve(sp,T):
              sp:=subs(c1=1,sp):
              cd:=[0 < -8*c2+3, 0 < 14*c2*c3-4*c2^3+16*c4*c2-3*c3+c2^2-6*c4-18*c3^2, 
                   0 < 256*c4^3+144*c4*c3^2*c2-128*c4^2*c2^2-4*c3^2*c2^3+16*c4*c2^4-192*c3*c4^2+18*c4*c3*c2-27*c3^4-27*c4^2
                   -4*c3^3+c3^2*c2^2-4*c4*c2^3-6*c3^2*c4+18*c3^3*c2+144*c4^2*c2-80*c4*c3*c2^2]:
              xprove(sp>=0,cd):
              RETURN()
           else xprove(ineq):
              RETURN()
           fi
        fi:

        fs:=[]:
        print(`Construct polynomials with few variants instead of the given one ___`,time()):
        m:=floor(dg/2)-1: 
        pt:=pttn(n,dg):  #print(pt):
        nt:=nops(pt):
        for i to nt do 
        ss[0]:=seq(id[k]=1, k=1..pt[i][1]):  
            for j to m do
                ss[j]:=seq(id[k]=mu[j], k=sum(pt[i][h],h=1..j)+1..sum(pt[i][h],h=1..j+1)):  
            od:
            ss[m+1]:=seq(id[k]=0, k=sum(pt[i][h],h=1..m+1)+1..n):
            su:={seq(ss[k],k=0..m+1)}:
            g:=subs(su,sp):
            fs:=[op(fs),g]
        od:
        ns:=nops(fs): print(`The number of the inequalities constructed is  ` || ns):   
        print(`Prove or disprove the inequalities one by one ___`,time()):
        for i to ns do  
            ex:=expand(fs[i]):  
            print(`Checking Inequalty ` || i):   
            if degree(ex)<1 then
               if signum(ex)=-1 then 
                  print(`This is not true.`):
                  RETURN()
               fi
            elif not(xprove(ex>=0)=true) then
                 print(`This is not true.`):
                 RETURN()
            fi 
        od: 
        print(`The inequality holds. ___`,time()):
        RETURN()
end:
        
pttn:=proc(number,degree)
      local n,m,L,i,j,n1,S,LL:
      n:=number:
      m:=floor(degree/2)-1:  
      L:=[seq([k],k=1..n)]:
      n1:=n:
      for j to m do    
          for i to n1 do
              S[i]:=seq([op(L[i]),k],k=1..min(L[i][-1],n-sum(L[i][k],k=1..j)))
          od:
          L:=[seq(S[i],i=1..n1)]:  
          n1:=nops(L)
      od:
      for i to n1 do
          S[i]:=[op(L[i]),n-sum(L[i][k],k=1..m+1)]
      od:
      LL:=[seq(S[i],i=1..n1)]:  
      RETURN(LL)
end: 

#readlib(showtime):
#showtime();
