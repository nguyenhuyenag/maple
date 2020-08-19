print("======================================================================");
print("Copyright(C) 2010-2015 by Deng HE ");
print("请在maple10或者maple11中运行,其他版本maple对运行及输出有较大影响");
print([sgm,sym,zsos,fsos]);
print([Sz*(x-y)^(2*n)+Sx*(y-z)^(2*n)+Sy*(z-x)^(2*n)]);
print("======================================================================");


sgm:=proc(expr)
   local rap,ex2,ex3,ex:
      rap:={x1=x2,x2=x3,x3=x1,a=b,b=c,c=a,A=B,B=C,C=A,x=y,y=z,z=x,u=v,v=w,w=u,ha=hb,hb=hc,hc=ha,Ra=Rb,Rb=Rc,Rc=Ra,ra=rb,rb=rc,rc=ra,ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,ka=kb,kb=kc,kc=ka,
         HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
         IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
         GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:     
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr+ex2+ex3:
   RETURN(ex)
end:

pro:=proc(expr)
   local rap,ex2,ex3,ex:
      rap:={x1=x2,x2=x3,x3=x1,a=b,b=c,c=a,A=B,B=C,C=A,x=y,y=z,z=x,u=v,v=w,w=u,ha=hb,hb=hc,hc=ha,Ra=Rb,Rb=Rc,Rc=Ra,ra=rb,rb=rc,rc=ra,ma=mb,mb=mc,mc=ma,wa=wb,wb=wc,wc=wa,ka=kb,kb=kc,kc=ka,
         HA=HB,HB=HC,HC=HA,IA=IB,IB=IC,
         IC=IA,Ha=Hb,Hb=Hc,Hc=Ha,A=B,B=C,C=A,Ra=Rb,Rb=Rc,Rc=Ra,GA=GB,GB=GC,
         GC=GA,JA=JB,JB=JC,JC=JA,ca=cb,cb=cc,cc=ca,Ja=Jb,Jb=Jc,Jc=Ja}:     
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr*ex2*ex3:
   RETURN(ex)
end:

sym:=proc(expr)
local rap,ex:
rap:=unapply(expr,x,y,z,a,b,c):ex:=rap(x,y,z,a,b,c)+rap(y,z,x,b,c,a)+rap(z,x,y,c,a,b)+rap(x,z,y,a,c,b)+rap(z,y,x,c,b,a)+rap(y,x,z,b,a,c):
RETURN(ex)
end:

sgm4:=proc(expr)
local rap,ex:
rap:=unapply(expr,x1,x2,x3,x4,a,b,c,d,x,y,z,w):
ex:=rap(x1,x2,x3,x4,a,b,c,d,x,y,z,w)+rap(x2,x3,x4,x1,b,c,d,a,y,z,w,x)+rap(x3,x4,x1,x2,c,d,a,b,z,w,x,y)+rap(x4,x1,x2,x3,d,a,b,c,w,x,y,z):
RETURN(ex)
end:

pro4:=proc(expr)
local rap,ex:
 rap:=unapply(expr,x1,x2,x3,x4,a,b,c,d,x,y,z,w):
ex:=rap(x1,x2,x3,x4,a,b,c,d,x,y,z,w)*rap(x2,x3,x4,x1,b,c,d,a,y,z,w,x)*rap(x3,x4,x1,x2,c,d,a,b,z,w,x,y)*rap(x4,x1,x2,x3,d,a,b,c,w,x,y,z):
RETURN(ex)
end:

clet:=proc(g)
 local i,h,temp,tempp:
 h:=collect([op(collect(expand(g),x,factor))],y,factor):
 temp:=h[1];
 for i from 2 to nops(h) do temp:=temp+h[i] od;
 tempp:=collect(subs(x=0,temp),y,factor)+(temp-(subs(x=0,temp))):
 return tempp:
 end:

###############################################################################################################
sosj:=proc(var)
local f,i,j,k,tt:
tt:=0:f:=0:for i from var by -1 to 0 do for j from var by -1  to 0 do for k from 0 to var do if i+j+k=var then tt:=tt+1:f:=f+MM[tt]*x^i*y^j*z^k else next:fi:od:od:od:f:=[tt,f]:
end:

sosjg:=proc(f,h,g,var) 
local Mm3,ff1,ff2,ff,temp,i,te,Mm,tt:tt:=0:
ff:=f:Mm3:=sosj(h-2*g)[2]:ff1:=unapply(Mm3,x,y,z):
if type(f, symmfunc(x,y,z)) then Mm3:=subs(solve(subs(x=1,y=1,z=1,{op(collect(ff1(x,y,z)-ff1(y,x,z), [x,y,z],distributed))})),Mm3):fi:
ff2:=sgm(Mm3*(x-y)^(2*g)):
Mm:=solve(subs(x=1,y=1,z=1,{op(collect(ff2-ff, [x,y,z],distributed))}),indets(Mm3) minus (indets(f) minus {x,y,z})):
if {Mm}={} then temp:={} else Mm3:=subs(Mm,Mm3):
for i from 1 to sosj(h-2*g)[1] do Mm3:=numer(subs(MM[i]=0,Mm3)):od:
if Mm3=0 then temp:={} else temp:={sgm(factor(Mm3)*(x-y)^(2*g))}:fi:
if  (indets(ff) minus {x,y,z})<>{} and Mm3<>0 then temp:={sgm(collect(Mm3,[x,y,z],distributed)*(x-y)^(2*g))}:fi:
if   (indets(ff) minus {x,y,z})={} and degree(Mm3,[x,y,z])>2  then print(var):
te:={op(expand(Mm3))}:for i from 1 to nops(te) do if evalf(subs(x=1,y=1,z=1,te[i]),5)<0 then tt:=tt+1:fi:od:
if tt>max(var,0) then temp:={}:fi:fi:fi:
temp:
end:

######################################################################################################################

#对称的(轮换对称和完全对称)分拆,Sz*(x-y)^(2*n)+Sx*(y-z)^(2*n)+Sy*(z-x)^(2*n),完全对称的时候,得到的Sz关于x,y对称,Sx关于y,z对称,Sy关于z,x对称.命令格式sos1(g,var,va),其中var为人为确定的实数,输出的负系数个数小于var,若需要输出的系数均为正,则var=0,va是对其中解方程组中残余的参数赋值,可取任意值,通常取为0#

zsos:=proc(g,var)
 local sj,i,j,k,qq,h,temp,tempp,ff,ff1,ff2,Mm3,pp,tt,pq:
sj:=time():tt:=0:tempp:={}:ff1:=unapply(subs(a=x,b=y,c=z,g),x,y,z):
 if      subs(a=c,b=c,x=z,y=z,numer(g))<>0 then    if   {x,y,z} subset indets(g)  then   print("ERROR,this polynomial does not vanish at x=y=z"):else print("ERROR,this polynomial does not vanish at a=b=c"):fi:
      else      for i from 2 to nops([op(expand(numer(g)))]) do if degree([op(expand(numer(g)))][i]/subs(a=1,b=1,c=1,x=1,y=1,z=1,[op(expand(numer(g)))][i]))<>degree([op(expand(numer(g)))][1]/subs(a=1,b=1,c=1,x=1,y=1,z=1,[op(expand(numer(g)))][1])) then tt:=tt+1:fi:od:
            if     tt>0 then  print("ERROR, this polynomial is not homonegeous!"):
                    elif tt=0 and nops(expand({ff1(x,y,z),ff1(x,z,y) ,ff1(y,z,x),ff1(z,x,y),ff1(z,y,x),ff1(y,x,z)}))>2 then  print("ERROR,This form is not circle symmetric!"):print(false):
                   
elif   tt=0 then if type(subs(a=x,b=y,c=z,g), symmfunc(x,y,z)) then print("This is a symmetric polynomial!"):else print("This is a cyclic symmetric polynomial!"):fi:

print(Degree=degree(numer(g),[x,y,z,a,b,c])):ff:=subs(a=x,b=y,c=z,numer(g)):for qq from floor(degree(numer(g),[a,b,c,x,y,z])/2) by -1 to 1 do 

 
                  if qq>1 or (indets(ff) minus {x,y,z})<>{}  then pq:=15:else pq:=80:fi:for i from 1 to pq do tempp:=tempp union sosjg(ff,degree(ff,[x,y,z]),qq,var) od:


       if {x,y,z} subset indets(g) and qq=1 and tempp<>{} then print("========================================================="):print([[[[[Sz*(x-y)^2+Sx*(y-z)^2+Sy*(z-x)^2]]]]]):print("========================================================="):if type(subs(a=x,b=y,c=z,f), symmfunc(x,y,z)) then
print("If [ x>=y>=z], just need to prove [ Sx>=0, Sy>=0, Sz>=0 ] or [ Sy>=0, Sy+Sx>=0, Sy+Sz>=0 ] or [ Sx>=0 , Sz>=0,  Sx+2*Sy>=0,  Sz+2*Sy>=0 ] or [  Sz>=0,  Sx>=0,  x^2*Sy+y^2*Sx>=0  ]");print("If [Sx+Sy+Sz>=0], just need to prove  [ Sx*Sy+Sy*Sz+Sz*Sx>=0 ] "):fi:
for i from 1 to nops(tempp) do print("======================================="):print([[[i]]]):print("======================================="):print(tempp[i]):od:
      elif {x,y,z} subset indets(g) and qq>1 and tempp<>{} then print("========================================================="):print([[[[[Sz*(x-y)^(2*qq)+Sx*(y-z)^(2*qq)+Sy*(z-x)^(2*qq)]]]]]):print("========================================================="):
for i to nops(tempp) do print("======================================="):print([[[i]]]):print("======================================="):print(tempp[i]):od:     
    elif {a,b,c} subset indets(g) and  qq=1 and   tempp<>{} then print("========================================================="):print([[[[[Sc*(a-b)^2+Sa*(b-c)^2+Sb*(c-a)^2]]]]]):print("========================================================="):if type(subs(a=x,b=y,c=z,f), symmfunc(x,y,z)) then print("If [ a>=b>=c], just need to prove [ Sa>=0, Sb>=0, Sc>=0 ] or [  Sb>=0 , Sb+Sa>=0,  Sb+Sc>=0  ] or [  Sa>=0 ,  Sc>=0 ,  Sa+2*Sb>=0 ,  Sc+2*Sb>=0 ] or [  Sc>=0 ,  Sa>=0 ,  a^2*Sb+b^2*Sa>=0  ]");print("If  Sa+Sb+Sc>=0, just need to prove  [  Sa*Sb+Sb*Sc+Sc*Sa>=0 ] "):fi:
for i to nops(tempp) do print("======================================="):print([[[i]]]):print("======================================="):print(subs(x=a,y=b,z=c,tempp[i])):od:     
    elif {a,b,c} subset indets(g) and qq>1 and tempp<>{}  then  print("========================================================="):print([[[[[Sc*(a-b)^(2*qq)+Sa*(b-c)^(2*qq)+Sb*(c-a)^(2*qq)]]]]]):print("========================================================="):for i to nops(tempp) do print("======================================="):print([[[i]]]):print("======================================="):print(subs(x=a,y=b,z=c,tempp[i])):od:
      elif {x,y,z} subset indets(g) and  tempp={} then print("========================================================="):print([[[[[Sz*(x-y)^(2*qq)+Sx*(y-z)^(2*qq)+Sy*(z-x)^(2*qq)]]]]]):print("========================================================="):print(false):
      elif {a,b,c} subset indets(g) and tempp={} then print("========================================================="):print([[[[[Sc*(a-b)^(2*qq)+Sa*(b-c)^(2*qq)+Sb*(c-a)^(2*qq)]]]]]):print("========================================================="):print(false):
fi:od:

print(-1):print(-1):
print("由于对输出结果的负系数个数做了限定,如果2次的无输出结果,可尝试多执行几次命令,或改变输入的参数的值"):
fi:fi:
print(1):print(1):
 print(`time is:`,time()-sj):
end:



####################################################################################################################
###对称或轮换对称分式的sos分拆,保留分母,格式是fsos(exp,sz),其中exp为一个待证分式,sz是形如,[]的形式的数组,里面为分母的集合,含a,b(x,y)字母#

##########寻找分母##########################
qufm:=proc(f)
local ex,ff,i,tem,exp,ex1,ex2,ex3,temp,te,tep,tepp:
ex:=1:ex1:=1:ex2:=1:ex3:=1:exp:={}:temp:=1:tep:=1:
if whattype(f)=`*` then te:={op(f)}:for i from 1 to nops(te) do if  indets(denom(te[i]))={} then tep:=tep*te[i]:fi:od:
tem:=denom({op(expand(subs(a=x,b=y,c=z,f/tep)))}):else tem:=denom({op(expand(subs(a=x,b=y,c=z,f)))}):fi:
if   indets(tem)<>{}  then tepp:=1:
for i from 1 to nops(tem) do if type(tem[i], symmfunc(x,y,z)) and (indets(tem[i]) minus {x,y,z})={} then temp:=lcm(temp,tem[i]):fi:od:
for i from 1 to nops(tem) do if   type(tem[i], symmfunc(y,z)) or type(tem[i], symmfunc(z,x)) then exp:=exp union {tem[i]} :fi:od:
exp:=tem minus exp:
if exp={} then tepp:=0:ex:=0:temp:=1:elif nops(exp)=1  then  ff:=unapply(exp[1],x,y,z):ex:={ex*exp[1],ex*lcm(ff(y,z,x),ff(z,x,y))}:
else 
for i from 1 to nops(exp) do   ff:=unapply(exp[i],x,y,z):ex1:=lcm(ex1,exp[i]):ex:=lcm(ex,ff(y,z,x)*ff(z,x,y)):od:
for i from 2 to nops(exp) do   ff:=unapply(exp[i],x,y,z):ex2:=lcm(ex2,ff(y,z,x)*ff(z,x,y)):od:ex2:=lcm(ex2,exp[1]):
for i from  nops(exp)-1 by -1 to 1 do   ff:=unapply(exp[i],x,y,z):ex3:=lcm(ex3,ff(y,z,x)*ff(z,x,y)):od:ex3:=lcm(ex3,exp[nops(exp)]):
ex:={ex1,ex2,ex3,ex}:
fi:
if {a,b,c}  subset indets(f)  then ex:=subs(x=a,y=b,z=c,ex):temp:=subs(x=a,y=b,z=c,temp):fi:
else tepp:=0:ex:=0:temp:=1:fi:
return [temp/lcoeff(temp),ex,tepp]:
end:



##########寻找分子########################

xzfz:=proc(var)
local f,i,j,k,tt:
tt:=0:f:=0:for i from var by -1 to 0 do for j from var by -1  to 0 do for k from 0 to var do if i+j+k=var then tt:=tt+1:f:=f+MM[tt]*x^i*y^j*z^k else next:fi:od:od:od:f:=[tt,f]:
end:


##########初步分拆###################

fsosjg:=proc(f,sz,var)
local Mm3,ff1,ff2,ff,temp,i,deg,ex,exp,te,tt:
ex:=subs(a=x,b=y,c=z,sz):tt:=0:
ff:=subs(a=x,b=y,c=z,f):
for i from 1 to 10 do if indets({op(expand(ff))}[i])  intersect  {x,y,z} <>{}  then 
deg:=degree(numer({op(expand(ff))}[i]),[x,y,z])-degree(denom({op(expand(ff))}[i]),[x,y,z])+degree(ex,[x,y,z])-2:break:fi:od:
if deg>20 then ff2:={} else
exp:=xzfz(deg):
if type(ff, symmfunc(x,y,z)) then Mm3:=exp[2]:ff1:=unapply(Mm3,x,y,z):
Mm3:=subs(solve(subs(x=1,y=1,z=1,{op(clet(ff1(x,y,z)-ff1(y,x,z)))})),Mm3):
else  Mm3:=exp[2]:fi:
ff2:=sgm(Mm3*(x-y)^2/ex):
temp:=solve(subs(x=1,y=1,z=1,{op(collect(numer(ff2-ff),[x,y,z],distributed))}),{seq(MM[i],i=1..exp[1])}):
if {temp}={} then ff2:={}:
else Mm3:=subs(temp,Mm3):
for i from 1 to exp[1] do Mm3:=subs(MM[i]=0,Mm3):od:
ff2:={sgm(numer(simplify(Mm3/ex))/factor(denom(simplify(Mm3/ex)))*(x-y)^2)}:
if  (indets(ff) minus {x,y,z})<>{} then ff2:={sgm(collect(numer(simplify(Mm3/ex)),[x,y,z],distributed,factor)/factor(denom(simplify(Mm3/ex)))*(x-y)^2)}:fi:
if   (indets(ff) minus {x,y,z})={} and degree(numer(simplify(Mm3/ex)),[x,y,z])>2 then print(var):
te:={op(expand(numer(simplify(Mm3/ex))))}:
for i from 1 to nops(te) do if evalf(subs(x=1,y=1,z=1,te[i]),5)<0 then tt:=tt+1:fi:od:
if tt>max(var,0) then ff2:={}:fi:fi:
if  {a,b,c} subset indets(f) then ff2:=subs(x=a,y=b,z=c,ff2):fi:
return ff2:
fi:fi:
end:


#####################主程序,给出多个分拆的结果############################################
#对称的(轮换对称和完全对称)分拆.命令格式fsos(g,var),其中var为人为确定的实数,输出的负系数个数小于var,若需要输出的系数均为正,则var=0#

fsos:=proc(f,var)
local ex,exp,i,j,k,sj,ff,tt,ff1,te,pq:
sj:=time():exp:={}:tt:=0:ff1:=unapply(subs(a=x,b=y,c=z,g),x,y,z):
if     subs(a=c,b=c,x=z,y=z,numer(f))<>0 then    if   {x,y,z} subset indets(f)  then   print("ERROR,this polynomial does not vanish at x=y=z"):else print("ERROR,this polynomial does not vanish at a=b=c"):fi:
      else      for i from 2 to nops([op(expand(numer(f)))]) do if degree([op(expand(numer(f)))][i]/subs(a=1,b=1,c=1,x=1,y=1,z=1,[op(expand(numer(f)))][i]))<>degree([op(expand(numer(f)))][1]/subs(a=1,b=1,c=1,x=1,y=1,z=1,[op(expand(numer(f)))][1])) then tt:=tt+1:fi:od:
            if     tt>0 then  print("ERROR, this polynomial is not homonegeous!"):
                    elif tt=0 and nops(expand({ff1(x,y,z),ff1(x,z,y) ,ff1(y,z,x),ff1(z,x,y),ff1(z,y,x),ff1(y,x,z)}))>2 then  print("ERROR,This form is not circle symmetric!"):print(false):
elif   tt=0 and  nops(expand({ff1(x,y,z),ff1(y,z,x),ff1(z,x,y)}))=1 then 
if type(subs(a=x,b=y,c=z,f), symmfunc(x,y,z)) then print("This is a symmetric polynomial!"):else print("This is a cyclic symmetric polynomial!"):fi:

ex:=qufm(f):
if ex[3]=1 then
ff:=f*(ex[1]):
print([ff>=0]):
ff:=simplify(ff):
print(1):print(1):
print("====================================================================================================================================="):
print("分母集合为"):print(ex[2]):
print("====================================================================================================================================="):
for i from 1 to  nops(ex[2]) do 
print("=============================================================================================================="):
print([[[[[i]]]]],"取分母为",[ex[2][i]]):
print("=============================================================================================================="):
print(-1):
if (indets(subs(a=x,b=y,c=z,ff)) minus {x,y,z})<>{} then pq:=20 elif type(subs(a=x,b=y,c=z,f), symmfunc(x,y,z)) then  pq:=60:else pq:=80:fi:
for j from 1 to pq do exp:=exp union fsosjg(ff,ex[2][i],var) od:

if exp={} then print(false):print(false):else 

if type(subs(a=x,b=y,c=z,f), symmfunc(x,y,z)) then print("This is a symmetric polynomial!"):else print("This is a cyclic symmetric polynomial!"):fi:
if   {x,y,z} subset indets(f) then print([[[[[Sz*(x-y)^2+Sx*(y-z)^2+Sy*(z-x)^2]]]]]):print(1):
print("If [ x>=y>=z], just need to prove [ Sx>=0, Sy>=0, Sz>=0 ] or [ Sy>=0, Sy+Sx>=0, Sy+Sz>=0 ] or [ Sx>=0 , Sz>=0,  Sx+2*Sy>=0,  Sz+2*Sy>=0 ] or [  Sz>=0,  Sx>=0,  x^2*Sy+y^2*Sx>=0  ]");print("If [Sx+Sy+Sz>=0], just need to prove  [ Sx*Sy+Sy*Sz+Sz*Sx>=0 ] "):

else print([[[[[Sc*(a-b)^2+Sa*(b-c)^2+Sb*(c-a)^2]]]]]):print(1):print("If [ a>=b>=c], just need to prove [ Sa>=0, Sb>=0, Sc>=0 ] or [  Sb>=0 , Sb+Sa>=0,  Sb+Sc>=0  ] or [  Sa>=0 ,  Sc>=0 ,  Sa+2*Sb>=0 ,  Sc+2*Sb>=0 ] or [  Sc>=0 ,  Sa>=0 ,  a^2*Sb+b^2*Sa>=0  ]"):print("If  Sa+Sb+Sc>=0, just need to prove  [  Sa*Sb+Sb*Sc+Sc*Sa>=0 ] "):fi:
for k from 1 to nops(exp) do 
print("=========="):print([[k]]):print("=========="):print(exp[k]):
od:fi:exp:={}:od:
else print(-1):print(-1):print("分母为空集,程序无法分拆此类问题,请调用zsos程序进行分拆"):fi:

print(1):print(1):
print(`time is:`,time()-sj):
fi:fi:
end:




###################################################################################################################




