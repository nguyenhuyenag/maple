print("psdgcd, a program for automatic proving inequalities and solving optimization probelms.");
print([hantwoSample,hantSample,ineqreal,proineqB,opencadSample,proineqBprojGcd,proineqBproj,psdhp,ineqpst,newineqpst,findk,findkmax,samples,cyc,cyctq,cyclic]);
print("psdgcd, 2009-2014 by Jingjun Han"):
#print("Please give me an inequality"):
#print("proineq, a program for automatic proving inequalities and solving optimization probelms."):
#print("RM can treat radical problems"):
#print("nvd can treat polynomial inequality"):

#print("Example1,RM(cyc((y/(y+2*x))^(1/2),[x,y,z])<=19/10):"):
#print("proineq can prove inequalities without any conditions. findkmax returns maximal value of the parameter such that the inequality holds, cyctq can deal with cyclic ternary quartic forms problems."):
#findk returns all possible values such that the inequality holds
#print("function rads is from software "Bottema" by Lu Yang etc."):
#print("For inequalities with extra conditions, please try the function pineq"):
print("Example,hantSample((a^2+b^2+c^2)^2-3*(a^3*b+b^3*c+c^3*a)):","gcdcad"):
print("Example,proineq((a^2+b^2+c^2)^2-3*(a^3*b+b^3*c+c^3*a)):","old program"):
print("Example,findkmax((x^2-x+1)*(y^2-y+1)*(z^2-z+1)-m*(x^2*y^2*z^2-x*z*y+1),[x,y,z],m):"):
print("Example,ineqreal((a^2+b^2+c^2)^2-3*(a^3*b+b^3*c+c^3*a),[],2):","real numbers with constraints"):
#print("Example4,ineqpst((a^2+b^2+c^2)^2-3*(a^3*b+b^3*c+c^3*a),2):","positive numbers"):
print("Example,psdhp((a^2+b^2+c^2)^2-3*(a^3*b+b^3*c+c^3*a),2):","real numbers"):
#print("Example6,newineqpst((a^2+b^2+c^2)^2-(3+1/1000000000000000000000)*(a^3*b+a*c^3+b^3*c), 2)","positive numbers"):
#print("Example3,findk((a^2+b^2+c^2)^2-k*(a^3*b+b^3*c+c^3*a),[a,b,c],k):"):
#print("Example4,cyctq((a^2+b^2+c^2)^2-(3-1/10^100000)*(a^3*b+b^3*c+c^3*a)):"):
#print("Example5,ineqpst(a^3+b^3+c^3-3*a*b*c,[a,b,c]):"):
#print("infolevel[proineq] := 2 will give you more details"):
#print("benchmark1(k,solver): f:=(\sum_{i=1}^k x_i^2)^2-4\sum_{i=1}^k x_i^2x_{i+1}^2, solver=1 (han projection with gcd): solver=2 (brown projection with gcd): solver=3 (brown projection without gcd)"):

with(linalg):
with(combinat):
##################################
Test:=proc(v,d,n)
     local tim,nu,L,i,a,ti,L1,L2,j,L3,b,c:
L:=[]:
L1:=[]:
L2:=[]:
L3:=[]:
for i to n do
L:=[op(L),randpoly([seq(a[i],i=1..v)], degree = d)]:
od:
for j to nops(L) do
tim:=time():
#nu:=nops(hantSample(L[j],2)):
#tim:=time()-tim:
L2:=[op(L2),hantSampletest(L[j],2)]:
od:
for j to nops(L) do
tim:=time():
#nu:=nops(hantSample(L[j],2)):
#tim:=time()-tim:
L3:=[op(L3),hantSampletest(L[j],3)]:
od:
for j to nops(L) do
tim:=time():
#nu:=nops(opencadSample(L[j],2)):
#tim:=time()-tim:
L1:=[op(L1),opencadSampletest(L[j])]:
od:
for j to 4 do
a[j]:=add(L1[i][j],i=1..nops(L1))/nops(L1):
od:
for j to 4 do
b[j]:=add(L2[i][j],i=1..nops(L2))/nops(L2):
od:
for j to 4 do
c[j]:=add(L3[i][j],i=1..nops(L3))/nops(L3):
od:
#return (L1,L2,L3,[seq(a[i],i=1..4)],[seq(b[i],i=1..4)],[seq(c[i],i=1..4)]):
return ([seq(a[i],i=1..4)],[seq(b[i],i=1..4)],[seq(c[i],i=1..4)]):
end:

#####################################
proineq:=proc(poly)
	local tim,nu:
	tim:=time(): 
	nu:=proineq0(poly):
	if nu=false then 
		print(`Not psd`): print("time(s)"): print(time()-tim):return false:
	end if:
	print("time(s)"):
	print(time()-tim):
	print("sample points:"):
	print(nu):
	print(`psd`):return true:
end:


#############################################
# compute all sample points during han projection
# with gcd
############################################
hantwoSample:=proc(poly)
	local tim,var,vars,l,A,i,j,k,t,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(f)=ldegree(f) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		hen:=var[vars]=1:
		f:=primpart(sqrfree1(subs(hen,f))): 
		var:=[op(indets(f))]:
                vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:

	L:=[[f,1]]:
	s:=0:
	j:=1:
	if vars>1 then  
		for j from vars to 3 by -2  do 
			g1:=res(f,var[j]):
			L:=[op(L),[g1,1]]:
			g2:=res(f,var[j-1]):
			g1:=res(g1,var[j-1]):
			g2:=res(g2,var[j]):
			f:=gcd(g1,g2):
			L:=[op(L),[f,g1]]:
		end do:
	end if:
	i:=j:

	for j from i to 2 by -1  do
		f:=res(f,var[j]):
		L:=[op(L),[f,1]]:
	end do:
        print(L):
	sa:=p2Sample(L,1):
	sa:=addPre(sa,hen):
	return sa:
end:
##################################
#inequality in real numbers with constraints
####################################
ineqreal:=proc(poly,polys,t)
local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,nu,nu1:
f:=poly:
L2:=polys:
g:=1:
tim:=time():
if nops(polys)=0 then psdhp(f,t): 
else 	#nu:=0:
	var:=[op(indets([f,op(L2)]))]:
        vars:=nops(var):
	#L:=sqrfree5s(sqrfree2(numer(f))):
        L:=[sqrfree2(numer(f))]:
	if L=false then 
		return false: 
	elif L=true then
		return true:
	else
		for j to nops(L) do
                        if nops(L)>1 then
                        print(L[j]):
                        fi:
			nu1:=ineqhp(L[j],L2,t):
			if nu1=false then
                                #print(Not psd):
				return false:
			#else nu:=nu1+nu: 
			fi:
		od:
	fi:
fi:
	#return nu:
print(time()-tim): 
return true:                                                          
end:
################################
############################################
#inequality with constraints
##########################################

ineqhp:=proc(poly,polys,t)
local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
f:=poly:
L2:=polys:
g:=1:
tim:=time():
if nops(polys)=0 then psdhp(f,t): 
else for i to nops(L2) do
     g:=g*L2[i]:
     od:
    var:=[op(indets([f,op(L2)]))]:
    # var:=[op(indets(poly))]:
     vars:=nops(var):
    # print(f*g):
     sa:=hantSample1(f*g,t):
     for i to nops(sa) do
        # print(sa[i]):
        # print(sa[i],L2,f):
         if subs(seq(var[j]=sa[i][j],j=1..vars),f)<0 then s:=1: for k to nops(L2) while s=1 do
                                                                 if subs(seq(var[j]=sa[i][j],j=1..vars),L2[k])<0 then s:=0: fi:
                                                                od:
                                                                if s=1 then #print(time()-tim): 
                                                                   return false: 
                                                                fi:
         fi:
    od:
fi:
#print(time()-tim): 
return true:                                                          
end:
############################################
#inequality with non-negative numbers
##########################################

ineqpst:=proc(poly,t)
local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,nu1,PP:
f:=poly:
g:=1:
tim:=time():
var:=[op(indets(f))]:
        vars:=nops(var):
	L:=sqrfree5s(sqrfree2(numer(f))): #print(L):
	if L=false then 
		return false: 
	elif L=true then
		return true:
	else
		for j to nops(L) do
			(nu1,PP):=ineqpp(L[j],t,1,{}):
			if nu1=false then print(nops(PP),time()-tim): return false:
			#else nu:=nu1+nu: 
			fi:
		od:
	fi:
print(nops(PP)):
print(time()-tim): 
return true:                                                          
end:                                                     
############################################
ineqpp:=proc(poly,v,w,pp)
	local var,vars,l,A,i,j,k,t,L,f,g,h,Li,nu,nu1,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,PP,tim,tim1,vars1,vars2,var1:
	nu:=true:
        l:=1:
        PP:=pp:
	f:=sqrfree2(poly):#print("Now, prove the nonnegative of",f):
       # if w=1 then print(f):fi:
	if f=1 then 
		return (nu,PP):
	fi:
        if f=-1 then 
		return (false,PP):
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	# print(poly,'poly'):
	if degree(poly)=ldegree(poly) then 
		if l=1 then
			print(`Homogenous`):
		fi:
		f:=subs(var[vars]=1,poly): 
                if is (f in PP)=true then PP:=PP union {f}: print("AP1"): return (nu,PP): 
                              else PP:={f} union PP: #print(PP):
                fi:
		var:=[op(indets(f))]:vars:=nops(var): 
        fi:
		if f=1 then
			return (nu,PP): #true:
		fi:
       # print(f):
        if vars-1>v then vars2:=v else vars2:=vars-1:fi:
        if vars>1 then #if w=1 then print(f,[var,vars,v]): fi:
                        #if w=1 then print(`Projection Phase`, "hproj"):tim1:=time():fi:
                  #(L):=hantSample2(f,v): 
                 #  if w=1 then tim:=time()-tim1: tim1:=time(): print(L,tim): print(`Projection Phase finished`, `Lifting Phase`): fi:
                  for i from vars-vars2+1 to vars do
                   #  if w=1 then print(i,vars,var): fi:
                      g:=sqrfree2(subs(var[i]=0,f)): 
                  #    if w=1 then print(g,'h'): fi:
                      if g^2<>1 then
                          if is (g in PP)=true then #PP:={g} union PP:
                             else PP:={g} union PP: #print(PP):
                              # if w=1 then print(g,'w'): fi:
                                var1:=[op(indets(g))]:
                                vars1:=nops(var1):
                                 if vars1-1>v then vars2:=v: else vars2:=vars1-1:fi:
                        #          if w=1 then print(g,vars2,PP): fi:
                               (nu,PP):=ineqpp(g,vars2,0,PP):
                        #           if w=1 then print(nu,PP,'j'): fi:
                                     if nu=false then return (false,PP):
                                     fi:
                           fi:  
                       fi:
                   od:
                         #   if w=1 then print('w'): fi:
                  nu1:=hantSample2(f,v): #if w=1 then print(nu1): fi:
                             for i to nops(nu1) do
                                if is(subs(seq(var[j]=nu1[i][j],j=1..vars),f)<0)=true then
				                      return (false,PP): 
				#else nu:=nu+nu1:
				fi: 
                             od:
                  #print(nu1,f):	
	else #print(f,'f'): 
		if uspensky2p(sqrfree2(f),op(var))<>[] then
			return (false,PP):
		fi:
	fi:
      #  if w=1 then tim:=time()-tim1:  tim1:=time():
      #     print(`Lifting Phase completed`, tim): 
      #  fi:
	#print(nu1,'nu',nu,L):
     #   print(PP):
       	return (nu,PP):
end:
###########################################
############################################
#inequality with non-negative numbers
##########################################

newineqpst:=proc(poly,t)
local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,nu1,PP:
f:=poly:
g:=1:
tim:=time():
var:=[op(indets(f))]:
        vars:=nops(var):
	L:=sqrfree5s(sqrfree2(numer(f))): #print(L):
	if L=false then 
		return false: 
	elif L=true then
		return true:
	else
		for j to nops(L) do
			nu1:=newineqpp(L[j],t):
			if nu1=false then print(time()-tim): return false:
			#else nu:=nu1+nu: 
			fi:
		od:
	fi:
print(time()-tim): 
return true:                                                          
end:     
#############################################
############################################
newineqpp:=proc(poly,v)
	local var,vars,l,A,i,j,k,t,L,f,g,h,Li,nu,nu1,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,PP,tim,tim1,vars1,vars2,var1:
	nu:=true:
        l:=1:
      	f:=sqrfree2(poly):#print("Now, prove the nonnegative of",f):
     	if f=1 then 
		return nu:
	fi:
        if f=-1 then 
		return false:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	# print(poly,'poly'):
	if degree(poly)=ldegree(poly) then 
		if l=1 then
			print(`Homogenous`):
		fi:
		f:=subs(var[vars]=1,poly): 
               	var:=[op(indets(f))]:vars:=nops(var): 
        fi:
		if f=1 then
			return nu: #true:
		fi:
       # print(f):
        if vars>1 then nu1:=newhantSample2(f,v):  print(nops(nu1),nu1):
                             for i to nops(nu1) do
                                if is(subs(seq(var[j]=nu1[i][j],j=1..vars),f)<0)=true then
				                      return false: 
				fi: 
                             od:
                  #print(nu1,f):	
	else #print(f,'f'): 
		if uspensky2p(sqrfree2(f),op(var))<>[] then
			return false:
		fi:
	fi:
      #  if w=1 then tim:=time()-tim1:  tim1:=time():
      #     print(`Lifting Phase completed`, tim): 
      #  fi:
	#print(nu1,'nu',nu,L):
     #   print(PP):
       	return (nu,PP):
end:
###########################################
#############################################
# compute all sample points during han projection
# with gcd for ineqpp
############################################
newhantSample2:=proc(poly,t)
	local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(f)=ldegree(f) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		hen:=1:
		f:=primpart(sqrfree1(subs(var[vars]=1,f))): 
		var:=[op(indets(f))]:
                vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
       #print(f,[var,vars,t]):
        L:=hprojt(f,[var,vars,t]):
        print(L):
	sa:=newp2Sample2(L,1):
	sa:=addPre(sa,hen):
	return sa:
end:
#############################################
# compute all sample points during han projection
# with gcd for ineqpp
############################################
hantSample2:=proc(poly,t)
	local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(f)=ldegree(f) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		hen:=1:
		f:=primpart(sqrfree1(subs(var[vars]=1,f))): 
		var:=[op(indets(f))]:
                vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
       #print(f,[var,vars,t]):
        L:=hprojt(f,[var,vars,t]):
        #print(L):
	sa:=p2Sample2(L,1):
	sa:=addPre(sa,hen):
	return sa:
end:
#############################################
# compute all sample points during han projection
# with gcd for ineqhp
############################################
hantSample1:=proc(poly,t)
	local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(f)=ldegree(f) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		hen:=1:
		f:=primpart(sqrfree1(subs(var[vars]=1,f))): 
		var:=[op(indets(f))]:
                vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
       #print(f,[var,vars,t]):
        L:=hprojt(f,[var,vars,t]):
        #print(L):
	sa:=p2Sample1(L,1):
	sa:=addPre(sa,hen):
	return sa:
end:
#############################################
# compute all sample points during han projection
# with gcd
############################################
hantSample:=proc(poly,t)
	local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(f)=ldegree(f) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		hen:=var[vars]=1:
		f:=primpart(sqrfree1(subs(hen,f))): 
		var:=[op(indets(f))]:
                vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
       #print(f,[var,vars,t]):
        L:=hprojt(f,[var,vars,t]):
        #print(L):
        print(time()-tim):
	sa:=p2Sample(L,1):
	sa:=addPre(sa,hen):
	return sa:
end:
######################
hprojt:=proc(poly,List)
local var,vars,l,A,i,j,k,L,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,var1,vars1,t,f:
f:=poly:
h:=1:
L:=[]:
var:=List[1]:
vars:=List[2]:
t:=List[3]:
	j:=1:
	if vars>1 then  
		for j from vars to t+1 by -t do 
                        #print(j):
                        var1:=[seq(var[j-t+1+s],s=0..t-1)]: #print(var1,t):
                        L1:=hproj([f,1],[var1,t]): #print(L1):
			L:=[op(L),op(L1)]:
                        f:=L1[t][1]:h:=L1[t][2]:#print(f):
		end do:
        i:=j: #print(i,'i',L):
         if i>1 then
          #print(factor(f),i,[seq(var[s],s=2..i)]):
         L1:=hproj([f,h],[[seq(var[s],s=2..i)],i-1]):
                L:=[op(L),op(L1)]:
           fi:
	end if:
L:=[[poly,1],op(L)]:
return L:
end:
########################################
hproj:=proc(List1,List)
local var,vars,l,A,i,j,k,L,g,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,B,f,h:
L:=[]:
f:=List1[1]:
h:=List1[2]:
var:=List[1]:
vars:=List[2]:
#t:=List[3]:
#L1:=[seq(var[vars-j+1],j=1..t)]:
L1:=var:
for j to vars do
  h1[var[j]]:=res(f,var[j]):
  h2[var[j]]:=1:
od:

for j from 2 to vars do
    A:=choose(L1,j); 
    for i to nops(A) do
      #print(A[i]):
      B:=twoLists(A[i]): #print(B):
      for k to j do
       # print([op(B[k][1])],B[k][2]):
        #print(h1[op(B[k][1])]):
        h1[op(B[k])]:=res(h1[op(B[k][1])],B[k][2]):
        #print(h1[op(B[k])],op(B[k])):
      od:
       h3:=h1[op(B[1])]:
      for k from 2 to j do
        h3:=gcd(h3,h1[op(B[k])]):
      od:
      h1[op(A[i])]:=h3:
      #h1[op(A[i])]:=gcd(seq(h1[op(B[k])],k=1..j)):
        #print(h1[op(A[i])],[op(A[i])]):
      h2[op(A[i])]:=h1[op(B[j])]:
    od:
od:
#print(h1):
#print(vars):
for j from vars to 1 by -1 do
if j<vars then
h2[seq(var[t],t=j..vars)]:=lcoeff(h2[seq(var[t],t=j+1..vars)],var[j])*h2[seq(var[t],t=j..vars)]:
else
h2[seq(var[t],t=j..vars)]:=lcoeff(h,var[j])*h2[seq(var[t],t=j..vars)]:
fi:
#print('j',j):
#print(var,j):
#print(var[j]):
#print(h1[seq(var[t],t=j..vars)],j):
 L:=[op(L),[h1[seq(var[t],t=j..vars)],h2[seq(var[t],t=j..vars)]]]:
od:
return L:
end:

#########################################
twoLists:=proc(L)
local i,j,L1,A1,A2,A,t:
L1:=[]:
#print(L):
  for j to nops(L) do
      #print(j):
      A1:=[seq(L[t],t=1..j-1)]: #print(A1):
      A2:=[seq(L[t],t=j+1..nops(L))]:#print(A2):
      A:=[[op(A1),op(A2)],L[j]]: 
      L1:=[op(L1),A]: #print(L1):
  od:
return L1:
end:

##########################################
#add pre sa=[[x=1,y=2]], pr=[z=3] 
#return [[z=3,x=1,y=2]]:
#########################################
addPre:=proc(sa,pr)
	local re, s:

	if pr=[] then 
		return sa:
	end if:

	re:=[]:
	for s in sa do 
		re:=[op(re),[pr,op(s)]]:
	end do:

	return re:
end:


#####################################
proineqB:=proc(poly)
	local tim,nu:
	tim:=time(): 
	nu:=proineq11(poly,1):
	if nu=false then print(`Not psd`): print("time(s)"):print(time()-tim):
		return false:
	fi:
	print("time(s)"):
	print(time()-tim):
	print("sample points:"):
	print(nu):
	print(`psd`):return true:
end:

##########################
#compute opencad sample points
##############################
opencadSample:=proc(poly)
	local tim,var,vars,l,A,i,j,k,t,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:

	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):#print("Now, prove the nonnegative of",f):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:vars:=nops(var):
	if degree(poly)=ldegree(poly) then 
		if v=1 then
			print(`Homogenous`): 
		fi:
		hen:=var[vars]=1:
		f:=primpart(sqrfree1(subs(hen,f))): 
		var:=[op(indets(f))]:vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
	L:=[[f,1]]:
	h:=1:
	s:=0:
	if vars>1 then  
		for j from vars to 2 by -1  do
			f:=res(f,var[j]):
			L1:=sqrfree2(f):
			L:=[op(L),[L1,1]]:
		end do:
	fi:
        #print(time()-tim):
	sa:=p2Sample(L,1):
	sa:=addPre(sa,hen):
	return sa:
end:




##########################
#Apply brown projection without gcd
##############################
proineqBproj:=proc(poly)
	local tim,var,vars,l,A,i,j,k,t,L,f,g,h,Li,nu,nu1,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	nu:=0:
	tim:=time(): 
	f:=poly:#print("Now, prove the nonnegative of",f):
	if f=1 then
		return true:
	fi:
	var:=[op(indets(poly))]:vars:=nops(var):
	if degree(poly)=1 mod 2 then
		return false:
	fi:
	if degree(poly)=ldegree(poly) then 
		if v=1 then
			print(`Homogenous`): 
		fi:
		f:=subs(var[vars]=1,poly): 
		var:=[op(indets(f))]:vars:=nops(var): 
	fi:
	if f=1 then
		return true:
	fi:
	L:=[[f,1]]:
	h:=1:
	s:=0:
	if vars>1 then  
		if vars=2 then 
			g1:=dis(f,var[vars]): 
			if g1=false then
				return false:
			fi: #print(g,"g"):
			h:=sqrfree2(numer(g1)): #print(L1,`L1[1]`,f):
			if is(h<0)=true then
				return false:
			fi:
			L:=[op(L),[h,1]]:  
			nu1:=proineq2(L,1):  
			if nu1=false then 
				return false: 
			else nu:=nu+nu1:
			fi: 
		else 
			for j from vars to 2 by -1  do
				f:=res(f,var[j]):
				L1:=sqrfree2(f):
				L:=[op(L),[L1,1]]:
			end do:
		fi:
	fi:

	nu:=proineq2(L,1):
	if nu=false then
		print(`Not psd`): print("time(s):"):print(time()-tim):return false:
	fi:
	print("time(s):"):
	print(time()-tim):
	print("sample points:"):
	print(nu):
	print(`psd`):return true:

end:
#################################

###################################
# factory resultant choose odd fator
# ##################################

###################################
proineq0:=proc(poly)
	local var,vars,i,j,L,f,nu,nu1:
	nu:=0:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	L:=sqrfree5(sqrfree2(numer(poly))):
	if L=false then 
		return false: 
	elif L=true then
		return true:
	else
		for j to nops(L) do
			nu1:=proineq11(L[j],1):
			if nu1=false then
				return false:
			else nu:=nu1+nu: 
			fi:
		od:
	fi:
	return nu:
end:


###############################
#apply brown projection with gcd
###############################
proineqBprojGcd:=proc(poly)
	local tim,var,vars,l,A,i,j,k,t,L,f,g,h,Li,nu,nu1,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	nu:=0:
	tim:=time(): 
	f:=poly:#print("Now, prove the nonnegative of",f):
	if f=1 then
		return true:
	fi:
	var:=[op(indets(poly))]:vars:=nops(var):
	if degree(poly)=1 mod 2 then
		return false:
	fi:
	if degree(poly)=ldegree(poly) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		f:=subs(var[vars]=1,poly): 
		var:=[op(indets(f))]:vars:=nops(var): 
	fi:
	if f=1 then
		return true:
	fi:
	L:=[[f,1]]:
	s:=0:
	if vars>1 then  
		if vars=2 then 
			g1:=dis(f,var[vars]): 
			if g1=false then
				return false:
			fi: #print(g,"g"):
			h:=sqrfree2(numer(g1)): #print(L1,`L1[1]`,f):
			if is(h<0)=true then
				return false:
			fi:
			L:=[op(L),[h,1]]:  
			nu1:=proineq2(L,1):  
			if nu1=false then
				return false:
			else
				nu:=nu+nu1:
			fi: 
		else 
			for j from vars to 3 by -2  do 
				g1:=res(f,var[j]):
				L:=[op(L),[g1,1]]:
				g2:= res(f,var[j-1]):
				g1:=res(g1,var[j-1]):
				g2:=res(g2,var[j]):
				f:=gcd(g1,g2):
				L:=[op(L),[f,g1]]:
			end do:
		end if:
	end if:
	i:=j:

	for j from i to 2 by -1  do
		f:=res(f,var[j]):
		L:=[op(L),[f,1]]:
	end do:

	nu:=proineq2(L,1):
	if nu=false then 
		print(`Not psd`): print("time(s):"): print(time()-tim):return false:
	fi:
	print("time(s):"):
	print(time()-tim):
	print("sample points:"):
	print(nu):
	print(`psd`):return true:

end:

###############################
#apply han projection and gcd
###############################

######################
proineq11:=proc(poly,v)
	local var,vars,l,A,i,j,k,t,L,f,g,h,Li,nu,nu1,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1:
	nu:=0:
	f:=poly:#print("Now, prove the nonnegative of",f):
	if f=1 then 
		return true:
	fi:
	var:=[op(indets(poly))]:vars:=nops(var):
	if degree(poly)=1 mod 2 then 
		return false:
	fi:
	if degree(poly)=ldegree(poly) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		f:=subs(var[vars]=1,poly): 
		var:=[op(indets(f))]:vars:=nops(var): fi:
		if f=1 then
			return true:
		fi:
		L:=[[f,1]]:
		h:=1:
		s:=0:
		if vars>1 then  
			if vars=2 then
				g1:=dis(f,var[vars]):
				if g1=false then
					return false: 
				fi: #print(g,"g"):
				L1:=sqrfree3(g1): #print(L1,`L1[1]`,f):
				if L1=false then 
					return false:
				fi: 
				if is(L1[1]<0)=true then return false: fi:
					if nops(L1)>=2 then
						for i from 2 to nops(L1) do
							#print(L1[i]):
							nu1:=proineq11(L1[i],v+1):#print(i,L[i]):
							if nu1=false then
								return false: 
							else nu:=nu+nu1:
							fi:
						od:
					fi:
					#if L1[1]=1 then return nu:fi:
					h:=1:#print(L1):
					for i from 2 to nops(L1) do
						h:=h*lcoeff(L1[i],var[vars]): #print(h,i,"h"):
					od:
					h:=sqrfree1(h*lcoeff(f,var[vars])):
					L:=[op(L),[L1[1],h]]:  
					nu1:=proineq2(L,v):  
					if nu1=false then
						return false: 
					else nu:=nu+nu1:
					fi: 
			else 
					for j from 1 to vars-1 while L<>1 do
						if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
							if v=1 then 
								print(j,L[j],vars):
							fi:
						fi:
						#print(f):
						if vars-j>2 then 
							s:=0:
							if j=1 then
								g1:=dis(f,var[vars]):  
								if g1=false then
									return false:
								fi: #print(g,"g"):
								g3:=dis(f,var[vars-1]): 
								if g3=false then
									return false:
								fi: #print(g,"g"):
								L1:=sqrfree3(g1): #print(L1,L1[1],"L1"):
								L2:=sqrfree3(g3): #print(L2,L2[1],"L2"):
								if L2=false then 
									return false:
								fi: #if v=1 then print(L,"v",0):fi:
								if L1=false then return false: fi: #if v=1 then print(L,"v",0):fi:
									if L1[1]<>1 and L2[1]<>1 then
										if nops(L1)>=2 then
											for i from 2 to nops(L1) do
												#print(L[i]):
												nu1:=proineq11(L1[i],v+1):#print(i,L[i]):
												if nu1=false then return false: else nu:=nu+nu1:fi:
												od:
											fi:                            
											h1:=1:
											for i from 2 to nops(L1) do
												h1:=h1*lcoeff(L1[i],var[vars-j+1]): #print(h,i,"h"):
											od:
											h1:=sqrfree1(h1*lcoeff(f,var[vars-j+1])):   
											h3:=1:
											for i from 2 to nops(L2) do
												h3:=h3*lcoeff(L2[i],var[vars-j]): #print(h,i,"h"):
											od:
											h3:=sqrfree1(h3*lcoeff(f,var[vars-j])): 
										        #if degree(L1[1],var[vars-j])=0 and degree(L2[1],var[vars-j+1])=0 
											#	then print("Missing variable"): s:=1:                                                
											#	while degree(L1[1],var[vars-j])=0 and degree(L2[1],var[vars-j])=0 do                                     
											#		L:=[op(L),[L1[1],h1]]:
											#		if j=1 then 
											#			h1:=lcoeff(h1,var[vars-j]):
											#			h3:=lcoeff(h3,var[vars-j+1]):
											#		else h1:=lcoeff(h1,var[vars-j]):
											#			h3:=lcoeff(h3,var[vars-j]):
											#		fi:
											#		j:=j+1 
											#	od:
											#	j1:=j:
											#	#print(j1,"s"):
											#else j1:=j-1:
											#fi:
											g2:=primpart(sqrfree1(res(L1[1],var[vars-j]))):#print(g2,"g2"):
											h2:=lcoeff(h1,var[vars-j]):   
											g4:=primpart(sqrfree1(res(L2[1],var[vars-j1]))):
											h4:=lcoeff(h3,var[vars-j1]):  #print(h4,'h4'): 
											g:=primpart(gcd(g2,g4)): 
                                                                                           #if v=1 then print(j1,j,L1[1],L2[1],g,g2,g4,"s"): fi:
											if g-g2<>0 then
												if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
													print("OK",g,g2,g4,v):
												fi:
												if s=1 then
													print ("OK1",g,g2,g4,s):
												fi:
												if nops(L2)>=2 then
													for i from 2 to nops(L2) do                 
														nu1:=proineq11(L2[i],v+1):#print(i,L[i]):
														if nu1=false then
															return false: 
														else nu:=nu+nu1:
														fi:
													od:
												fi:
												h:=sqrfree1(h2*h4): #print(h,"h"):
												L3:=sqrfree3(g):
											#	if nops(L3)>1 then g:=1: 
											#		for i from 2 to nops(L3) do 
											#			if degree(L3[i]) mod 2=1 or lcoeff(L3[i])<0 then
											#				g:=g*L3[i]:
											#			else 
											#				if proineq11(L3[i],v+1)=false then 
											#					if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then 
											#						print("not redundant"):
											#					fi:
											#					g:=g*L3[i]: 
											#				else if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
											#					print("find redundant factor",L3[i]):
											#				fi:
											#				h:=h*L3[i]: 
											#			        fi:
											#		        fi:
											#	       od:
											#        fi:
											L:=[op(L),[L1[1],L2[1],h1,h3],[g,h]]: 
											j:=j+1:
										else if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
											print("Not improved"): 
										fi:
										h:=h2:L:=[op(L),[L1[1],h1]]:  
									fi: 

								else L:=1: if L1[1]=1 then 
									if nops(L1)>=2 then
										for i from 2 to nops(L1) do
											nu1:=proineq11((sqrfree2(L1[i])),v+1): #print(i,'nu1'):
											if nu1=false then
												return false: 
											else nu:=nu+nu1:         #print(nu,'nv',j):   
											fi:
										od:
									fi:
								fi:
								if L2[1]=1 then 
									if nops(L2)>=2 then
										for i from 2 to nops(L2) do
											nu1:=proineq11((sqrfree2(L2[i])),v+1): #print(i,'nu1'):
											if nu1=false	then
												return false: 
											else nu:=nu+nu1:         #print(nu,'nv',j):       
											fi:
										od:
									fi:
								fi:
							fi:
						else          
							g1:=primpart(sqrfree1(res(L[j][1],var[vars-j+1]))):#print(g1,var[vars-j],"g1"):
							L3:=sqrfree3(g1): #print(L1,var[vars-j],"L1"):
						#	if nops(L3)>1 then g1:=1: 
						#		for i from 2 to nops(L3) do 
						#			if degree(L3[i]) mod 2=1 or lcoeff(L3[i])<0 then
						#				g1:=g1*L3[i]:
						#			else 
						#				if proineq11(L3[i],v+1)=false then
						#					if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
						#						print("not redundant"): 
                                                #                                       fi:
						#						g1:=g1*L3[i]: 
						#				else 
						#						if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then 
						#							print("find redundant factor",L3[i]):
						#						fi:
						#						h:=h*L3[i]: 
						#				fi:
						#			fi:
						#		od:
						#	fi:                                  
								h1:=lcoeff(h,var[vars-j+1]):
								g2:=primpart(sqrfree1(res(g1,var[vars-j]))):#print(g2,"g2"):
								L4:=sqrfree3(g2):
						#		if nops(L4)>1 then g2:=1: 
						#			for i from 2 to nops(L4) do 
						#				if degree(L4[i]) mod 2=1 or lcoeff(L4[i])<0 then g2:=g2*L4[i]:
						#				else if proineq11(L4[i],v+1)=false then g2:=g2*L4[i]: 
						#				      else if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then 
                                                #                                              print("find redundant factor",L4[i]): 
                                                #                                            fi:
						#					h1:=h1*L4[i]: 
						#				      fi:
						#			         fi:
						#		         od:
						#	         fi: 
							h2:=lcoeff(h1,var[vars-j]): 
							g3:=primpart(sqrfree1(res(L[j][1],var[vars-j]))):#print(g3,var[vars-j],"g3"):
							h3:=lcoeff(h,var[vars-j]):
							g4:=primpart(sqrfree1(res(g3,var[vars-j+1]))):#print(g4,var[vars-j+1]):
							h4:=lcoeff(h3,var[vars-j+1]):      
							g:=gcd(g2,g4): 
							if g-g2<>0 then
								if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
									print("OK"): 
								fi:
								h:=sqrfree1(h2*h4): #print(h,"h"):
								L:=[op(L),[g1,g3,h1,h3],[g,h]]: 
							else 
								if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
									print("Not improved"):
								fi:
								h:=h2:L:=[op(L),[g1,h1],[g,h]]:
							fi:
							j:=j+1: #print(j):
						fi:
					else  #print('j',j,L):
						#if nops(L)<>1
						if j=1 then g:=primpart(sqrfree1(dis(L[j][1],var[vars-j+1]))):
						else
							g:=primpart(sqrfree1(res(L[j][1],var[vars-j+1]))): #print(g,vars):
						fi:
						L3:=sqrfree3(g):
					#	if nops(L3)>1 then  g:=1:
					#		for i from 2 to nops(L3) do 
					#			if degree(L3[i]) mod 2=1 or lcoeff(L3[i])<0 then g:=g*L3[i]:
					#			else 
					#				if proineq11(L3[i],v+1)=false then
					#					if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then 
					#						print("not redundant"): 
					#					fi:
					#					g:=g*L3[i]: 
					#				else if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
					#					print("find redundant factor",L3[i]): 
					#				      fi:
					#				h:=h*L3[i]: 
					#			        fi:
					#		        fi:
					#	         od:
					#        fi:
					h:=sqrfree1(lcoeff(h,var[vars-j+1])):
					L:=[op(L),[g,h]]: #print(g,h,`g`):
					#else print(L,'j',j):
					#fi:
				fi:  
			od:
			#print(L,'L'): 
			if L=1 then return nu: 
			else if v=1 then print(L,v): fi:
				nu1:=proineq2(L,v): 
				if nu1=false then
					return false: 
				else nu:=nu+nu1:
				fi: 
			fi:
		fi:
	else #print(f,'f'): 
		if realroot(f)<>[] then
			return false:
		fi:
	fi:
	#print(nu1,'nu',nu,L):
	return nu:
end:
############################################################
###psdhp
###################################
psdhp:=proc(poly,v)
	local var,vars,i,j,L,f,nu,nu1,tim,PP,PP1:
        tim:=time(): PP:={}:
	nu:=0:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	L:= sqrfree5(sqrfree2(numer(poly))):
	if L=false then print(`Not psd`): print(time()-tim):
		return false: 
	elif L=true then print(`psd`): print(time()-tim):
		return true:
	else
		for j to nops(L) do
                        #print(j):
			(nu1,PP1):=psdhnproj(L[j],v,1,PP):
                        PP:=PP1 union PP:
			if nu1=false then print(j,`Not psd`): print(time()-tim):
				return false:
			#else nu:=nu1+nu: 
			fi:
		od:
	fi:
        print(nops(PP),`psd`): print(time()-tim):
        #print(PP):
	return true:
end:

###############################
###############################
#apply hnproj 
###############################

######################
psdhnproj:=proc(poly,v,w,pp)
	local var,vars,l,A,i,j,k,t,L,f,g,h,Li,nu,nu1,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,PP,tim,tim1:
	nu:=true:
        l:=1:
        PP:=pp:
	f:=poly:#print("Now, prove the nonnegative of",f):
        #print(f):
	if f=1 then 
		return (nu,PP):
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(poly)=1 mod 2 then 
		return (false,PP):
	fi:
       # print(poly,'poly'):
	if degree(poly)=ldegree(poly) then 
		if l=1 then
			print(`Homogenous`):
		fi:
		f:=subs(var[vars]=1,poly): 
                if is (f in PP)=true then PP:=PP union {f}: print("AP1"): return (nu,PP): 
                              else PP:={f} union PP: #print(PP):
                fi:
		var:=[op(indets(f))]:vars:=nops(var): 
        fi:
		if f=1 then
			return (nu,PP): #true:
		fi:
        
        if vars>1 then #if w=1 then print(f,[var,vars,v]): fi:
                        if w=1 then print(`Projection Phase`, "hnproj"):tim1:=time():fi:
                  (L,PP):=hnprojt(f,[var,vars,v,w,PP]): #if w=1 then print(L,'i'): fi:
                  #print(L,v):
                        if L=false then return (L,PP): fi:
                   if w=1 then tim:=time()-tim1: tim1:=time(): print(L,tim): print(`Projection Phase finished`, `Lifting Phase`): fi:
                  nu1:=proineq2(L,v): 
				if nu1=false then
					return (false,PP): 
				#else nu:=nu+nu1:
				fi: 
                  #print(nu1,f):	
	else #print(f,'f'): 
		if realroot(f)<>[] then
                        #print(f,PP):
			return (false,PP):
		fi:
	fi:
        if w=1 then tim:=time()-tim1:  tim1:=time():
           print(`Lifting Phase completed`, tim): 
        fi:
	#print(nu1,'nu',nu,L):
       	return (nu,PP):
end:

######################################
######################
hnprojt:=proc(poly,List)
local var,vars,l,A,i,j,k,L,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,var1,vars1,t,f,s1,w,PP:
#print(poly,List):
f:=poly:
h:=1:
L:=[]:
var:=List[1]:
vars:=List[2]:
t:=List[3]:
w:=List[4]:
PP:=List[5]:
s1:=0:
	j:=1:
	if vars>1 then  
		for j from vars to t+1 by -t do 
                       # if w=1 then 
                       #print(j):
                       #fi:
                        var1:=[seq(var[j-t+1+s],s=0..t-1)]: #if w=1 then print(var1):fi:
                           if j=vars then s1:=1: (L1,PP):=hnproj(f,[var1,t,PP]): #if w=1 then print(L1): fi:
                               if L1=false then return (false,PP): fi:
                               else
                            #print(j):
                                L1:=hproj([f,h],[var1,t]): #print(L1):
                                if L1=false then return (false,PP): fi:
                            fi:
			  L:=[op(L),op(L1)]:
                          f:=L1[t][1]:h:=L1[t][2]#print(f):
                 od:
             i:=j: #print(i,'i',poly):
             if i>1 then 
               #print(i,f):
               if s1=1 then L1:=hproj([f,h],[[seq(var[s],s=2..i)],i-1]): #print(L1,s1):
                               if L1=false then return (false,PP): fi:
                         else (L1,PP):=hnproj(f,[[seq(var[s],s=2..i)],i-1,PP]): #print(L1,s1):
                                if L1=false then return (false,PP): fi:
                fi:
                L:=[op(L),op(L1)]:
             fi:
	end if:
L:=[[poly,1],op(L)]:
#print(poly,List,s1):
return (L,PP):
end:
########################################
hnproj:=proc(f,List)
local var,vars,l,A,i,j,k,L,g,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,B,v,nu1,nu,h,vars1,var1,vars2,PP:
#print(f,List):
v:=1:
L:=[]:
var:=List[1]:
vars:=List[2]: 
PP:=List[3]:
#L1:=[seq(var[vars-j+1],j=1..t)]:
L1:=var:
                         for j to vars do
				g1:=dis(f,var[j]):
				if g1=false then
					return (false,PP): 
				fi: #print(g,"g"):
				L3:=sqrfree3(g1): #print(L3,`L3[1]`,f):
				if L3=false then 
					return (false,PP):
				fi: 
				if is(L3[1]<0)=true then return (false,PP): fi:
					if nops(L3)>=2 then 
                                                          for i from 2 to nops(L3) do
							      #print(L3[i],i,nops(L3),'i'):
                                                            if is (L3[i] in PP)=true then #print("AD2"):
                                                            else PP:=PP union {L3[i]}: #print(PP,L3[i]):
                                                                 var1:=[op(indets(L3[i]))]:        
                                                                 vars1:=nops(var1): 
                                                                   if vars>vars1-1 then vars2:=vars1-1 
                                                                                   else vars2:=vars:
                                                                   fi:                             #vars2:=min(vars1-1,vars):
                                                                  # print(L3[i],vars2,PP):
							           (nu1,PP):=psdhnproj(L3[i],vars2,0,PP):#print(nu1,PP,'j'):
							           if nu1=false then
								          return (false,PP): 
							                #else nu:=nu+nu1:
							           fi:
                                                            fi:
						           od:
					fi:
				h1[var[j]]:=L3[1]:		
                                        if j=vars then
                                          h:=1:
					  for i from 2 to nops(L3) do
						h:=h*lcoeff(L3[i],var[j]): #print(h,i,"h"):
                                                h:=sqrfree1(h*lcoeff(f,var[j])):
					  od:
                                          h2[var[vars]]:=h: #print(h2[var[vars]],j,"h2[var[vars]]",var[vars]):
                                        fi:							
                           od:
for j from 2 to vars do
    A:=choose(L1,j); 
    for i to nops(A) do
      #print(A[i]):
      B:=twoLists(A[i]): #print(B):
      for k to j do
       # print([op(B[k][1])],B[k][2]):
        #print(h1[op(B[k][1])]):
        h1[op(B[k])]:=res(h1[op(B[k][1])],B[k][2]):
        #print(h1[op(B[k])],op(B[k])):
      od:
       h3:=h1[op(B[1])]:
      for k from 2 to j do
        h3:=gcd(h3,h1[op(B[k])]):
      od:
      h1[op(A[i])]:=h3:
      #h1[op(A[i])]:=gcd(seq(h1[op(B[k])],k=1..j)):
        #print(h1[op(A[i])],[op(A[i])]):
      h2[op(A[i])]:=h1[op(B[j])]:
    od:
od:
#print(h1):
#print(vars):
for j from vars to 1 by -1 do
#print('j',j):
#print(var,j):
#print(var[j]):
#print(h1[seq(var[t],t=j..vars)],j):
if j<>vars then
 h2[seq(var[t],t=j..vars)]:=lcoeff(h2[seq(var[t],t=j+1..vars)],var[j])*h2[seq(var[t],t=j..vars)]:
fi:
 L:=[op(L),[h1[seq(var[t],t=j..vars)],h2[seq(var[t],t=j..vars)]]]:
od:
#print(f):
return (L,PP):
end:



#################################################
#compute all samples 
##########################################
p2Sample:=proc(List,v)

	local var,vars,l,A,i,j,k,s,t,L,f,L1,L2,L3,L4,L5,P,Ls,sas,sa,g,h,L6,L7,L8,L9:
	L:=List:

	f:=List[1][1]:
	var:=[op(indets(f))]: vars:=nops(var): 
	sa:=samples(List[vars][1],List[vars][2]):
	for j from 2 to vars do
		L3:=[]:
		L4:=[]:
		if nops(L[vars-j+1])=2 then 
			for k to nops(sa) do  
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]):
				L1:=samples(L5[1],L5[2]):
				for t to nops(L1) do
					L3:=[op(L3),[op(Ls),op(L1[t])]]:
				od:
			od:
			sa:=L3:
		else 
			for k to nops(sa) do  #print(k): print(L1):
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]): 
				L1:=samples(sqrfree1(L5[1]),sqrfree1(L5[3])):#print(L1,"L1",L5):
				L2:=samples(sqrfree1(L5[2]),sqrfree1(L5[4])):#print(L2,"L2",L5):
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j]):
				for t to nops(L1) do
					L6:=subs(var[j]=op(L1[t]),L5):
					L7:=samples(L6[1],L6[2]):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L1[t]),op(L7[s])]]:
					od:
				od:
				for t to nops(L2) do
					L6:=subs(var[j+1]=op(L2[t]),L5):
					L7:=samples(sqrfree1(L6[1]),sqrfree1(L6[2])):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L7[s]),op(L2[t])]]:
					od:
				od:
			od:
			sa:=L3:
			j:=j+1:
		fi:
	od:
	sas:=[]:

	for i from 1 to nops(sa) do:
		Ls:=sa[i]:
		sas:=[op(sas),[ seq(var[t]=Ls[t],t=1..vars)]]:
	od:

	return sas:
end:
#################################################
#compute all samples for ineqhp
##########################################
p2Sample1:=proc(List,v)

	local var,vars,l,A,i,j,k,s,t,L,f,L1,L2,L3,L4,L5,P,Ls,sas,sa,g,h,L6,L7,L8,L9:
	L:=List:

	f:=List[1][1]:
	var:=[op(indets(f))]: vars:=nops(var): 
	sa:=samples(List[vars][1],List[vars][2]):
	for j from 2 to vars do
		L3:=[]:
		L4:=[]:
		if nops(L[vars-j+1])=2 then 
			for k to nops(sa) do  
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]):
				L1:=samples(L5[1],L5[2]):
				for t to nops(L1) do
					L3:=[op(L3),[op(Ls),op(L1[t])]]:
				od:
			od:
			sa:=L3:
		else 
			for k to nops(sa) do  #print(k): print(L1):
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]): 
				L1:=samples(sqrfree1(L5[1]),sqrfree1(L5[3])):#print(L1,"L1",L5):
				L2:=samples(sqrfree1(L5[2]),sqrfree1(L5[4])):#print(L2,"L2",L5):
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j]):
				for t to nops(L1) do
					L6:=subs(var[j]=op(L1[t]),L5):
					L7:=samples(L6[1],L6[2]):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L1[t]),op(L7[s])]]:
					od:
				od:
				for t to nops(L2) do
					L6:=subs(var[j+1]=op(L2[t]),L5):
					L7:=samples(sqrfree1(L6[1]),sqrfree1(L6[2])):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L7[s]),op(L2[t])]]:
					od:
				od:
			od:
			sa:=L3:
			j:=j+1:
		fi:
	od:
	sas:=[]:

	for i from 1 to nops(sa) do:
		Ls:=sa[i]:
		sas:=[op(sas),[seq(var[t]=Ls[t],t=1..vars)]]:
	od:

	return sa:
end:
#####################################
#################################################
#compute all samples for newineqpp
##########################################
newp2Sample2:=proc(List,v)

	local var,vars,l,A,i,j,k,s,t,L,f,L1,L2,L3,L4,L5,P,Ls,sas,sa,g,h,L6,L7,L8,L9:
	L:=List:

	f:=List[1][1]:
	var:=[op(indets(f))]: vars:=nops(var): 
	sa:=newsamplesp(List[vars][1],List[vars][2]):
	for j from 2 to vars do
		L3:=[]:
		L4:=[]:
		if nops(L[vars-j+1])=2 then 
			for k to nops(sa) do  
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]):
				L1:=newsamplesp(L5[1],L5[2]):
				for t to nops(L1) do
					L3:=[op(L3),[op(Ls),op(L1[t])]]:
				od:
			od:
			sa:=L3:
		else 
			for k to nops(sa) do  #print(k): print(L1):
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]): 
				L1:=newsamplesp(sqrfree1(L5[1]),sqrfree1(L5[3])):#print(L1,"L1",L5):
				L2:=newsamplesp(sqrfree1(L5[2]),sqrfree1(L5[4])):#print(L2,"L2",L5):
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j]):
				for t to nops(L1) do
					L6:=subs(var[j]=op(L1[t]),L5):
					L7:=newsamplesp(L6[1],L6[2]):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L1[t]),op(L7[s])]]:
					od:
				od:
				for t to nops(L2) do
					L6:=subs(var[j+1]=op(L2[t]),L5):
					L7:=newsamplesp(sqrfree1(L6[1]),sqrfree1(L6[2])):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L7[s]),op(L2[t])]]:
					od:
				od:
			od:
			sa:=L3:
			j:=j+1:
		fi:
	od:
	sas:=[]:

	for i from 1 to nops(sa) do:
		Ls:=sa[i]:
		sas:=[op(sas),[seq(var[t]=Ls[t],t=1..vars)]]:
	od:

	return sa:
end:
#################################################
#compute all samples for ineqpp
##########################################
p2Sample2:=proc(List,v)

	local var,vars,l,A,i,j,k,s,t,L,f,L1,L2,L3,L4,L5,P,Ls,sas,sa,g,h,L6,L7,L8,L9:
	L:=List:

	f:=List[1][1]:
	var:=[op(indets(f))]: vars:=nops(var): 
	sa:=samplesp(List[vars][1],List[vars][2]):
        #print(sa):
	for j from 2 to vars do
              # print(j):
		L3:=[]:
		L4:=[]:
		if nops(L[vars-j+1])=2 then 
			for k to nops(sa) do  
                               # print(k,'k',sa): print(L1):
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]): #print(L5):
				L1:=samplesp(L5[1],L5[2]):
				for t to nops(L1) do
					L3:=[op(L3),[op(Ls),op(L1[t])]]:
				od:
			od:
			sa:=L3:
		else 
			for k to nops(sa) do 
                               # print(k,'k'): print(L1):
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]): 
				L1:=samplesp(sqrfree1(L5[1]),sqrfree1(L5[3])):#print(L1,"L1",L5):
				L2:=samplesp(sqrfree1(L5[2]),sqrfree1(L5[4])):#print(L2,"L2",L5):
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j]):
				for t to nops(L1) do
					L6:=subs(var[j]=op(L1[t]),L5):
					L7:=samplesp(L6[1],L6[2]):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L1[t]),op(L7[s])]]:
					od:
				od:
				for t to nops(L2) do
					L6:=subs(var[j+1]=op(L2[t]),L5):
					L7:=samplesp(sqrfree1(L6[1]),sqrfree1(L6[2])):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L7[s]),op(L2[t])]]:
					od:
				od:
			od:
			sa:=L3:
			j:=j+1:
		fi:
	od:
	sas:=[]:

	for i from 1 to nops(sa) do:
		Ls:=sa[i]:
		sas:=[op(sas),[seq(var[t]=Ls[t],t=1..vars)]]:
	od:

	return sa:
end:
###################
proineq2:=proc(List,v)
	local var,vars,l,A,i,j,k,s,t,L,f,L1,L2,L3,L4,L5,P,Ls,sa,g,h,L6,L7,L8,L9:
	L:=List:
	if type(infolevel[proineq], numeric) and infolevel[proineq]>=2 then
		print(L):
	fi:
	f:=List[1][1]:
	var:=[op(indets(f))]: vars:=nops(var): 
	sa:=samples(List[vars][1],List[vars][2]):
	#print(sa,"sa"):
	for j from 2 to vars-1 do
		#print(j,"proineq2"):
		L3:=[]:
		L4:=[]:
		if nops(L[vars-j+1])=2 then 
			for k to nops(sa) do  
				#if j=8 then print(k,sa[k],j): 
				Ls:=sa[k]:    
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]):
                                #if j=4 then print(L5):fi:
                                #print(L5):
				L1:=samples(L5[1],L5[2]):#print(L1):
				for t to nops(L1) do
					L3:=[op(L3),[op(Ls),op(L1[t])]]:
				od:
			od:
			sa:=L3:
		else 
			for k to nops(sa) do  #print(k): print(L1):
				#print(k,sa,j):
				Ls:=sa[k]:    
				#print(L[vars-j+1],"L[vars-j+1]",Ls,j):
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j+1]): 
				L1:=samples(sqrfree1(L5[1]),sqrfree1(L5[3])):#print(L1,"L1",L5):
				L2:=samples(sqrfree1(L5[2]),sqrfree1(L5[4])):#print(L2,"L2",L5):
				L5:=subs(seq(var[t]=Ls[t],t=1..j-1),L[vars-j]):
				for t to nops(L1) do
					#print(t,"L1",var[j],L1):
					L6:=subs(var[j]=op(L1[t]),L5):
					L7:=samples(L6[1],L6[2]):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L1[t]),op(L7[s])]]:
					od:
				od:
				for t to nops(L2) do
					#print(t,"t"):
					L6:=subs(var[j+1]=op(L2[t]),L5):
					L7:=samples(sqrfree1(L6[1]),sqrfree1(L6[2])):
					for s to nops(L7) do
						L3:=[op(L3),[op(Ls),op(L7[s]),op(L2[t])]]:
					od:
				od:
			od:
			sa:=L3:
			j:=j+1:
		fi:
	od:
	#print(sa):
	for i to nops(sa) do:
		Ls:=sa[i]:
		#print(subs(seq(var[t]=Ls[t],t=1..vars-1),f)):
		g:=sqrfree2(subs(seq(var[t]=Ls[t],t=1..vars-1),f)):#print(g,"g",var[1]):
		if realroot(g)<>[] then 
			return false:
		fi:
	od:
	#print(L):
	return nops(sa): 
end:


#############################################ȫ������
findk:=proc(poly,va,k)
	local L,f,g,i,j,t,s,L1,L2,var,vars,sa,L3,ti:
	ti:=time():
	f:=poly:#print(f):
	var:=va:
	vars:=nops(var):
	L1:=[]:
	L2:=[]:
	L:=[[1,f]]:
	for i to vars do
		L2:=[]:
		for t to nops(L) do
			L1:=fproj(L[t],var):
			L2:=[L1,op(L2)]:
		od:
		L:=L2:
		var:=[seq(var[j],j=1..vars-i)]:
		#print(L):
	od:
	g:=1:
	for i to nops(L) do
		g:=g*mul(L[i][j],j=1..nops(L[i])):
	od:
	g:=sqrfree1(g):
	L1:=sqrfree8(g):
	print(g,"g"):
	sa:=samples(g,1):
	print(sa):
	L:=[]:
	for i to nops(sa) do
		print(i,sa[i]):
		if proineq(subs(k=op(sa[i]),f))=true then L3:=[sa[i]]: 
			if i<>nops(sa) and i<>1 then
				s:=0:
				for j to nops(L1) while s=0 do
					if is(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i-1]),L1[j])<0)=true then s:=1: L3:=[op(L3),L1[j]]:
					fi:
				od:
				s:=0:
				for j to nops(L1) while s=0 do
					#print(j,"j",op(sa[i]),op(sa[i+1])):
					#if j=2 then print(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i+1]),L1[j]),is(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i+1]),L1[j])<0)):fi:
					if is(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i+1]),L1[j])<0)=true then s:=1: L3:=[op(L3),L1[j]]:
					fi:
				od:
			elif i=1 then L3:=[op(L3),-infinity]:
				s:=0: 
				for j to nops(L1) while s=0 do
					if is(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i+1]),L1[j])<0)=true then s:=1: L3:=[op(L3),L1[j]]:
					fi:
				od:
			else s:=0: 
				for j to nops(L1) while s=0 do
					if is(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i-1]),L1[j])<0)=true then s:=1: L3:=[op(L3),L1[j]]:
					fi:
				od:
				L3:=[op(L3),+infinity]:
			fi:
			L:=[op(L),L3]:
		fi:
	od:
	print(time()-ti):
	return(L,g):
end:

###################
#############################################ȫ������
findkmax:=proc(poly,va,k)
	local L,f,g,i,j,t,s,L1,L2,var,vars,sa,L3,ti:
	ti:=time():
	f:=poly:#print(f):
	var:=va:
	vars:=nops(var):
	L1:=[]:
	L2:=[]:
	L:=[[1,f]]:
	for i to vars do
		L2:=[]:
		for t to nops(L) do
			L1:=fproj(L[t],var):
			L2:=[L1,op(L2)]:
		od:

		L:=L2:
		#print(L,"L"):
		var:=[seq(var[j],j=1..vars-i)]:
		#print(L):
	od:
	g:=1:
	for i to nops(L) do
		g:=g*mul(L[i][j],j=1..nops(L[i])):
	od:
	#print(g,"g"):
	g:=sqrfree1(g):
	L1:=sqrfree8(g):
	#print(g,"g"):
	sa:=samples(g,1):
	L:=[]:
	t:=0:
	for i to nops(sa) while t=0 do
		print(i,sa[i]):
		if proineq(subs(k=op(sa[i]),f))=false then 
			t:=1:
			if i=1 or i=nops(L1) then 
				return false: 
			else L:=[[op(sa[i-1]),op(sa[i])]]: 
				s:=0:
				for j to nops(L1) while s=0 do
					if is(subs(k=op(sa[i]),L1[j])*subs(k=op(sa[i-1]),L1[j])<0)=true then s:=1: L:=[op(L),L1[j]]:
					fi:
				od:
			fi:
		fi:
	od:
	print(g):
	print(`The global supremum of`, k, `is the real root of`, L[2], `=0`, `which is between`, L[1]):
	print(time()-ti):
	return(L):
end:
#####################################
fproj1:=proc(poly,va)
	local L1,L2,i,j,var,vars,f,L,g:
	g:=1:
	var:=va:
	vars:=nops(var):
	if vars=0 then return poly: 
	fi:
	#print(List2):
	f:=res(poly,va[vars]):
	L:=sqrfree7(f):
	L1:=L[1]:
	L2:=L[2]:
	for i to nops(L2) do
		g:=sqrfree1(fproj1(L2[i],[seq(va[j],j=1..vars-1)])*g):
	od:
	for i to nops(L1) do
		g:=sqrfree1(fproj1(L1[i],[seq(va[j],j=1..vars-1)])*g):
	od:
	#print([L1,op(L2)],a):
	return(g):
end:
######################################
fproj2:=proc(poly,va)
	local L1,L2,i,j,var,vars,f,L,g:
	vars:=nops(va):
	if vars=0 then return poly: 
	fi:
	f:=sqrfree1(res(poly,va[vars])):
	g:=sqrfree1(res(f,[seq(va[j],j=1..vars-1)])):
	return(g):
end:
######################################
fproj:=proc(List,va)
	local L1,L2,i,j,var,vars,f,L,g:
	vars:=nops(va):
	L1:=1:
	L2:=[]:
	#print(List2):
	for i from 2 to nops(List) do
		f:=res(List[i],va[vars]):
		L:=sqrfree7(f):
		L1:=L[1][1]*L1:
		L2:=[op(L[2]),op(L2)]:
	od:
	g:=res(List[1],va[vars]):
	L1:=sqrfree1(g*L1):
	#print([L1,op(L2)],a):
	return([L1,op(L2)]):
end:
###################
res:=proc(poly,x)
	local var,vars,g,f:
	var:=indets(poly):   #print(poly,x):
	if member(x,var)=true
		then f:=(poly):
		g:=primpart(sqrfree1(resultant(f,diff(f,x),x))):
	else g:=poly 
	fi:
	return g
end:
###################
###################
Dres:=proc(poly,x)
	local var,vars,g,f:
	var:=indets(poly):   #print(poly,x):
	if member(x,var)=true
		then f:=(poly):
		g:=sqrfree1(primpart(gps([f,diff(f,x)],[x]))):
	else g:=poly
	fi:
	return g
end:
#####################
dis:=proc(poly,x)
	local var,vars,g,f,d:
	var:=indets(poly):
	if member(x,var)=true
		then d:=degree(poly,x): #print(d,x,poly):
		if d mod 2<>0 then return false:
		else g:=(-1)^(d/2)*discrim(poly,x):
		fi:
	else g:=poly 
	fi:
	return g
end:
##############################
disSample:=proc(poly,x)
	local var,vars,g,f,d:
	var:=indets(poly):
	if member(x,var)=true
		then d:=degree(poly,x): #print(d,x,poly):
		g:=(-1)^(d/2)*discrim(poly,x):
	else g:=poly 
	fi:
	return g
end:

######################
#################################################################
#   GPS is the gather procedure of Gather-and-Sift Algorithm.   #
#        Parameter: tsplst - Equations                          #
#                   tsvlst - Variables                          #
#        Notes: Number of tsplst should be number tsvlst plus 1 #
#        Modified by: Carl Liu - CICA                           #
#        Date: October 18, 2002                                 #
#################################################################

with(linalg):


#################################################################
#    i,j,k,lcvr        һ�����                                 #
#    st                ��ʼʱ��                                 #
#    npols             tsplst���̸���                           #
#    nvars             tsvlstδ֪�����                         #
#    tspowers          ָ���� (nvars)                           #
#    tsVr              ָ���� (nvars) (����)                  #
#    tsVrlst           tsVr��list                               #
#    tsA               nops�׷���                               #
#    tsB               nrs X nxy����                            #
#    tsC               tsB��˹��ȥ���õ��ľ���                  #
#    mu                GPS����ĵ���������                      #
#################################################################

gps := proc(tsplst,tsvlst)

	local i,j,k,lcvr,st,npols,nvars,tspowers,tsVr,tsVrlst,tsA,tsB,tsC,divby,
	subvar,subby,tsa,tsdp,tscl,tsvar,nxy,sxy,txy,nrs,trm,mu,um,t:

	st := time():
	npols := nops(tsplst):
	nvars := nops(tsvlst):
	tspowers := array(1..nvars):

	if not(npols = nvars + 1) then
		print(`Number of equations must be number of variables plus one!`):
		return:
	fi:

	tsA := array(1..npols,1..npols):
	tsVr := array(1..nvars):
	for i from 1 to nvars do
		lcvr := op(i,tsvlst):
		tsVr[i] := ts||lcvr||r
	od:
	tsVrlst := convert(tsVr, list):

	#################################################################
	# Setting up the first row of the matrix.
	#################################################################

	for i from 1 to npols do
		tsA[1,i] := op(i,tsplst):
	od:

	#################################################################
	# Setting up the remaining rows of the matrix.
	#################################################################

	divby := 1:
	for i from 2 to npols do
		subvar := op(i-1,tsvlst):
		subby := tsVr[i-1]:
		for j from 1 to npols do
			tsA[i,j] := subs(subvar=subby, tsA[i-1,j]):
		od:
	od:
	for i from npols by -1 to 2 do
		subvar := op(i-1,tsvlst):
		subby := tsVr[i-1]:
		for j from 1 to npols do
			tsA[i, j] := normal((tsA[i, j] - tsA[i-1, j])/(subvar - subby)):
		od:
	od:

	print(`Set up the First Matrix`):

	#################################################################
	#Compute the determinant of the matrix ... "dp".
	#################################################################

	tsa := normal(det(tsA)):
	tsdp := collect(tsa,tsVrlst,distributed):
	print(`Evaluated the First Determinant`):

	#################################################################
	# Setting up the actual Dixon Matrix.
	# tscl:=map(primpart,[coeffs(tsdp,tsVrlst,'trs')],tsvlst):
	#################################################################

	tscl:=[coeffs(tsdp,tsVrlst,'trs')]:
	coeffs(collect(tsdp,tsvlst,distributed),tsvlst,'txy'):
	tsvar := tsvlst:

	#################################################################
	#txy := sort([txy], tsF):
	#################################################################

	nxy := nops([txy]):
	sxy := sum(txy[q],q=1..nxy):
	txy := [op(sort(sxy,tsvlst,tdeg))]:

	nrs := nops(tscl):
	tsB := array(1..nrs,1..nxy):
	for i from 1 to nxy do
		trm := op(i,txy):
		for j from 1 to nvars do
			tspowers[j] := 0:
			while divide(trm,tsvlst[j]^(1 + tspowers[j])) do
				tspowers[j] := tspowers[j]+1:
			od:
		od:
		for j from 1 to nrs do
			tsB[j,i] := collect(tscl[j],tsvlst[1]):
			for k from 1 to nvars do
				tsB[j,i] := collect(tsB[j,i],tsvlst[k]):
				tsB[j,i] := coeff(tsB[j,i],tsvlst[k],tspowers[k]):
			od:
		od:
	od:

	print(`Set up the Dixon Matrix`):
	print(`Doing Gaussian Elimination`):
	tsC:=ffgausselim(tsB):
	um:=(multiply(tsC,txy)):
	print(`GPS is running about `,time()-st):
	#print(`tsC equals `,tsC):
	#print(`txy equals `,txy):
	mu:=factor(convert(um,list)):
	t:=nops(mu):
	#print(t,mu):
	RETURN(mu[t]):
end:

#################### �Ѷ���ʽƽ���������ƽ���������
sqrfree3:=proc(f)
	local n,L,i,k1,g,k2,k3,L1,L2:
	L:=factors(f):
	L1:=[]:
	L2:=1:
	n:=nops(L[2]):
	k3:=signum(L[1]):
	for i to n do 
		if  L[2][i][2] mod 2=0 then  
			L2:=L2*L[2][i][1]:
		else 
			if is (lcoeff(L[2][i][1])<0)=true then k3:=k3*(-1): 
				L1:=[op(L1),-L[2][i][1]]:
			else L1:=[op(L1),L[2][i][1]]:
			fi:
		fi:
	od:
	if k3=-1 then return false:
	fi:
	RETURN([L2,op(L1)]):
end:

#############################################
# �Ѷ���ʽƽ���������ƽ���������
#############################################
sqrfree3Sample:=proc(f)

	local n,L,i,g,L1,L2:
	L:=factors(f):
	L1:=[]:
	L2:=1:
	n:=nops(L[2]):
	for i to n do 
		if  L[2][i][2] mod 2=0 then  
			L2:=L2*L[2][i][1]:
		else 
			if is (lcoeff(L[2][i][1])<0)=true then 
				L1:=[op(L1),-L[2][i][1]]:
			else L1:=[op(L1),L[2][i][1]]: 
			fi:
		fi:
	od:
	RETURN([L2,op(L1)]):
end:


#################### �Ѷ���ʽƽ���������ƽ���������
sqrfree7:=proc(f)
	local n,L,i,k1,g,k2,k3,L1,L2:
	L:=factors(f):
	L1:=[]:
	L2:=1:
	n:=nops(L[2]):
	for i to n do 
		if  L[2][i][2] mod 2=0 then  
			L2:=L2*L[2][i][1]:
		else 
			L1:=[op(L1),L[2][i][1]]: 
		fi:
	od:
	RETURN([[L2],L1]):
end:

#################### ����ʽȥƽ������

sqrfree1:=proc(f)
	local L,nL:
	L:=factors(f):
	nL:=nops(L[2]):
	mul(L[2][i][1],i=1..nL):
end:
###############################����ʽ���ز���Լ�����б�

sqrfree8:=proc(f)
	local L,nL,i,L1:
	L1:=[]:
	L:=factors(f):
	nL:=nops(L[2]):
	for i to nL do
		L1:=[op(L1),L[2][i][1]]
	od:
	return L1:
end:
#################### ��������ʽ�ϲ�
sqrfree9:=proc(g,h)
	local n,L,i,k1,k2,k3,L1,L2,Li,f1,L3,f2:
	L:=factors(g):
	Li:=factors(h):
	L1:=[]:
	L2:=[]:
	L3:=[]:
	n:=nops(L[2]):
	k3:=signum(L[1]):
	for i to n do 
		if  L[2][i][2] mod 2=0 then  
			L2:=[op(L2),numer(L[2][i][1])]:
		else 
			if is (lcoeff(L[2][i][1])<0)=true then k3:=k3*(-1): 
				L1:=[op(L1),numer(-L[2][i][1])]:
			else L1:=[op(L1),numer(L[2][i][1])]:
			fi:
		fi:
	od:
	if k3=-1 then return false:
	fi:
	n:=nops(Li[2]):
	k3:=signum(Li[1]):
	for i to n do 
		if  Li[2][i][2] mod 2=0 then  
			L3:=[op(L3),numer(Li[2][i][1])]:
		else 
			if is (lcoeff(Li[2][i][1])<0)=true then k3:=k3*(-1): 
				if is(-numer(L[2][i][1]) in L1)=false then
					L1:=[op(L1),-numer(L[2][i][1])]:
				fi:
			else 
				if is(numer(L[2][i][1]) in L1)=false then L1:=[op(L1),L[2][i][1]]:
				fi: 
			fi:
		fi:
	od:
	if k3=-1 then return false:
	fi:
	f1:=1:
	f2:=1:
	for i to nops(L2) do
		if is (L2[i] in L1 )=false then f1:=f1*L2[i]:
		fi:
	od:
	for i to nops(L2) do
		if is (L3[i] in L1)=false then f2:=f2*L2[i]:
		fi:
	od:
	RETURN([[f1,f2],L1]):
end:
###################
discardpl1:=proc(f)
	local i,n,g,p:    
	if nargs=1 then g:=factor(f):else g:=f:
	fi:
	if whattype(g)=`+` then RETURN(g)
	elif whattype(g)=`^` then RETURN(op(1,g))
	elif whattype(g)=`*` then
		n:=nops(g):
		p:=1:
		for i to n do
			if type(op(i,g),integer)=false 
				then
				p:=p*(discardpl1(op(i,g),x)):
			fi:
		od:
		RETURN(p):
	else RETURN(g):
	fi:
end:
##################
delp:=proc(f)
	local Ff,i,nc,var,coesig,L,nL:
	Ff:=factor(f):
	var:=[op(indets(Ff))]:
	if type(Ff,`*`)=true then nc:=nops(Ff):
		L:=[]:
		for i to nc do 
			coesig:=map(signum,[coeffs(op(i,Ff),var)]):
			if has(-1,coesig)=true or nops(coesig)=1 then 
				L:=[op(L),op(i,Ff)]:
			fi:
		od:
		nL:=nops(L):
		product(L[j],j=1..nops(L)): 
	else 
		RETURN(Ff):    
	fi:     
end:

#################### ȥ��ƽ������
sqrfree2:=proc(f)
	local n,L,i,k,g:
	L:=factors(f):
	n:=nops(L[2]):
	g:=signum(L[1]):
	for i to n do 
		if  L[2][i][2] mod 2=0 then  
			k:=1:
		else 
			k:=L[2][i][1]:
		fi:
		g:=g*k:
	od:
	RETURN(g):
end:
#######################
sqrfree5s:=proc(f)
	local n,L,i,k,g,L1:
	L1:=[]:
	L:=factors(f):
	n:=nops(L[2]):
	for i to n do 
		if  L[2][i][2] mod 2=1 then 
			if is (lcoeff(L[2][i][1])<0)=true then 
				L1:=[op(L1),-L[2][i][1]]: 
			else L1:=[op(L1),L[2][i][1]]:
			fi: 
		fi:
	od:
	#print(k):
	#if k=-1 then return false:
	#fi:
	if L1=[] then return true:
	fi: 
	RETURN(L1):
end:
#######################
sqrfree5:=proc(f)
	local n,L,i,k,g,L1:
	L1:=[]:
	L:=factors(f):
	k:=signum(L[1]):
	n:=nops(L[2]):
	for i to n do 
		if  L[2][i][2] mod 2=1 then 
			if is (lcoeff(L[2][i][1])<0)=true then k:=k*(-1): 
				L1:=[op(L1),-L[2][i][1]]: 
			else L1:=[op(L1),L[2][i][1]]:
			fi: 
		fi:
	od:
	#print(k):
	if k=-1 then return false:
	fi:
	if L1=[] then return true:
	fi: 
	RETURN(L1):
end:
#############################�ж��Ƿ��ֻ��Գ�
cyclic:=proc(poly,var)
	local i,j,vars,f,t:
	f[1]:=poly:
	vars:=nops(var):
	for i to vars-1 do
		f[i+1]:=subs(seq(var[j]=t[(j+i)mod(vars)],j=1..vars),poly):
		f[i+1]:=subs(seq(t[j]=var[j],j=1..vars-1),t[0]=var[vars],f[i+1]):
		if f[i+1]-f[i]<>0 then return false:
		fi:
	od:
	return true:
end:

######################################### ʵ�����
#with(RegularChains):
#with(SemiAlgebraicSetTools):
#samplesPCAD:=proc(g,h)

#PartialCylindricalAlgebraicDecomposition(p, lp, R)
######################################### ѡȡ���Ե�
samples:=proc(g,h,n)
	local c,a,b,L1,L2,i,j,f,L,var,f1,m,l,t,var1,k:
	f:=g:
        var1:=op(indets(h)): 
	var:=op(indets(f)):if nops([var])=0 then # print(L1,j): 
                                               k:=1: i:=0: while k=1 do
                                                              if subs(var1=i,h)=0 then i:=i+1: 
                                                                else return([[i]]): k:=2: fi:
                                                             od:
                                               fi:#print(var):#print(f):
	
	#L:=realroot(f,var):#print(L):
        L:=realroot(f):
	L1:=sort(map2(op,1,L),`<`):
	L2:=sort(map2(op,2,L),`<`):
	#print(L,L1,L2,`l`):
	if nargs=2 then m:=rootbound1(f,var): else m:=n:
	fi:
	for i to nops(L1)-1 while L2[i]<m do
		#print(i):
		if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]<>L2[i+1] then f1:=normal(f/(var-L2[i])): #print(L2[i]):#
			if is(subs(var=L1[i],f1)*subs(var=L2[i],f1)>0)=true then 
				a:=L1[i+1]:b:=L2[i+1]:
				while a=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f1)*subs(var=c,f1)>0)=true
						then b:=c else a:=c:
					fi:
				od: 
				L1:=subsop(i+1=a,L1):L2:=subsop(i+1=b,L2):
				#print(L1,L2):
			else 
				if is(subs(var=L1[i+1],f1)*subs(var=L2[i+1],f1)>0)=true then a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=a,f1)*subs(var=c,f1)>0)=true then a:=c else b:=c:fi:
						od:
						L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
					fi:
					#print(L1,L2):
				fi:
			else 
				if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]=L2[i+1] then f1:=normal(f/(var-L2[i])): 
					a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=b,f1)*subs(var=c,f1)>=0)=true
							then b:=c else a:=c:
						fi:
					od: 
					L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
				fi:
			fi:
			if L2[i]=L1[i+1] and subs(var=L2[i],h)=0 
				then if L2[i+1]>L2[i] then a:=L2[i]:b:=L2[i+1]:
				while a=L2[i] do
					c:=(a+b)/2:
					if is(subs(var=a,f)*subs(var=c,f)>0)=true and subs(var=c,h)<>0
						then a:=c else b:=c:
					fi:
				od: 
				L2:=subsop(i=a,L2):
			else a:=L1[i]:b:=L1[i+1]:
				while b=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f)*subs(var=c,f)>0)=true and subs(var=c,h)<>0
						then b:=c else a:=c:
					fi:
				od:
			fi:
		fi: 
	od:
	#print(L1,L2,l):
	j:=nops(L1): #print(L1,j):
	if j=0 then  # print(L1,j): 
                    k:=1: i:=0: while k=1 do
                                   if subs(var1=i,h)=0 then i:=i+1: 
                                  else L:=[[i]]: k:=2: fi:
                                od:
	else #print(L1,j):
		L:=[]:
		for i from 0 to j do 
			#print(i):
			if i=0 then t:=0: l:=floor(L1[1]): 
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]:#print(l): 
				else l:=l-1:#print(l):
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true 
							then t:=1: else l:=l-1:
							#print(l):print(h(l)):print(is(h(l)<>0)):print(t):
						fi:                         
					od:
					L:=[[l]]: 
				fi:
			elif i=j then t:=0: l:=ceil(L2[j]):
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]: else l:=l+1:
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true then t:=1: else l:=l+1:
						fi: 
					od:
					L:=[op(L),[l]]:
				fi:
			else t:=0: l:=L2[i]: 
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]: 
				else l:=(l+L1[i+1])/2:
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true then t:=1: else l:=(L1[i+1]+l)/2:
						fi: 
					od:
					L:=[op(L),[l]]:                           
				fi:
			fi:
		od:
	fi:
	return L: 
end proc:
######################################################
samplesp:=proc(g,h,n)
	local c,a,b,L1,L2,i,j,f,L,var,f1,m,l,t,var1,k:
	f:=g:
        var1:=op(indets(h)): 
	var:=op(indets(f)):if nops([var])=0 then # print(L1,j): 
                                               k:=1: i:=0: while k=1 do
                                                              if subs(var1=i,h)=0 then i:=i+1: 
                                                                else return([[i]]): k:=2: fi:
                                                             od:
                                               fi:#print(var):#print(f):
	
	L:=uspensky2p(f,var):#print(L):
	L1:=sort(map2(op,1,L),`<`):
	L2:=sort(map2(op,2,L),`<`):
	#print(L,L1,L2,`l`):
	if nargs=2 then m:=rootbound1(f,var): else m:=n:
	fi:
	for i to nops(L1)-1 while L2[i]<m do
		#print(i):
		if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]<>L2[i+1] then f1:=normal(f/(var-L2[i])): #print(L2[i]):#
			if is(subs(var=L1[i],f1)*subs(var=L2[i],f1)>0)=true then 
				a:=L1[i+1]:b:=L2[i+1]:
				while a=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f1)*subs(var=c,f1)>0)=true
						then b:=c else a:=c:
					fi:
				od: 
				L1:=subsop(i+1=a,L1):L2:=subsop(i+1=b,L2):
				#print(L1,L2):
			else 
				if is(subs(var=L1[i+1],f1)*subs(var=L2[i+1],f1)>0)=true then a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=a,f1)*subs(var=c,f1)>0)=true then a:=c else b:=c:fi:
						od:
						L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
					fi:
					#print(L1,L2):
				fi:
			else 
				if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]=L2[i+1] then f1:=normal(f/(var-L2[i])): 
					a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=b,f1)*subs(var=c,f1)>=0)=true
							then b:=c else a:=c:
						fi:
					od: 
					L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
				fi:
			fi:
			if L2[i]=L1[i+1] and subs(var=L2[i],h)=0 
				then if L2[i+1]>L2[i] then a:=L2[i]:b:=L2[i+1]:
				while a=L2[i] do
					c:=(a+b)/2:
					if is(subs(var=a,f)*subs(var=c,f)>0)=true and subs(var=c,h)<>0
						then a:=c else b:=c:
					fi:
				od: 
				L2:=subsop(i=a,L2):
			else a:=L1[i]:b:=L1[i+1]:
				while b=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f)*subs(var=c,f)>0)=true and subs(var=c,h)<>0
						then b:=c else a:=c:
					fi:
				od:
			fi:
		fi: 
	od:
	#print(L1,L2,l):
	j:=nops(L1): #print(L1,j):
	if j=0 then  # print(L1,j): 
                    k:=1: i:=0: while k=1 do
                                   if subs(var1=i,h)=0 or subs(var=i,g)=0 then i:=i+1: 
                                  else L:=[[i]]: k:=2: fi:
                                od:
	else #print(L1,j):
		L:=[]:
		for i from 0 to j do 
			#print(i):
			if i=0 then 
                            #    t:=0: l:=floor(L1[1]): 
			   #	if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]:#print(l): 
			#	                                                            else l:=l-1:#print(l):
			#		                                                         while t=0 do 
			#			                                                       if is(subs(var1=l,h)<>0)=true 
			#				                                                      then t:=1: else l:=l-1:
			#				                                                       #print(l):print(h(l)):print(is(h(l)<>0)):print(t):
			#			                                                        fi:                         
			#		                                                           od:
			#		                                                   L:=[[l]]: 
			#	fi:
			elif i=j then t:=0: l:=ceil(L2[j]):
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]: else l:=l+1:
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true then t:=1: else l:=l+1:
						fi: 
					od:
					L:=[op(L),[l]]:
				fi:
			else t:=0: l:=L2[i]: 
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]: 
				else l:=(l+L1[i+1])/2:
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true then t:=1: else l:=(L1[i+1]+l)/2:
						fi: 
					od:
					L:=[op(L),[l]]:                           
				fi:
			fi:
		od:
	fi:
	return L: 
end proc:
##########################################
newsamplesp:=proc(g,h,n)
	local c,a,b,L1,L2,i,j,f,L,var,f1,m,l,t,var1,k:
	f:=g:
        var1:=op(indets(h)): 
	var:=op(indets(f)):if nops([var])=0 then # print(L1,j): 
                                               k:=1: i:=0: while k=1 do
                                                              if subs(var1=i,h)=0 then i:=i+1: 
                                                                else return([[i]]): k:=2: fi:
                                                             od:
                                               fi:#print(var):#print(f):
	
	L:=uspensky2p(f,var):#print(L):
	L1:=sort(map2(op,1,L),`<`):
	L2:=sort(map2(op,2,L),`<`):
	#print(L,L1,L2,`l`):
	if nargs=2 then m:=rootbound1(f,var): else m:=n:
	fi:
	for i to nops(L1)-1 while L2[i]<m do
		#print(i):
		if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]<>L2[i+1] then f1:=normal(f/(var-L2[i])): #print(L2[i]):#
			if is(subs(var=L1[i],f1)*subs(var=L2[i],f1)>0)=true then 
				a:=L1[i+1]:b:=L2[i+1]:
				while a=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f1)*subs(var=c,f1)>0)=true
						then b:=c else a:=c:
					fi:
				od: 
				L1:=subsop(i+1=a,L1):L2:=subsop(i+1=b,L2):
				#print(L1,L2):
			else 
				if is(subs(var=L1[i+1],f1)*subs(var=L2[i+1],f1)>0)=true then a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=a,f1)*subs(var=c,f1)>0)=true then a:=c else b:=c:fi:
						od:
						L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
					fi:
					#print(L1,L2):
				fi:
			else 
				if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]=L2[i+1] then f1:=normal(f/(var-L2[i])): 
					a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=b,f1)*subs(var=c,f1)>=0)=true
							then b:=c else a:=c:
						fi:
					od: 
					L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
				fi:
			fi:
			if L2[i]=L1[i+1] and subs(var=L2[i],h)=0 
				then if L2[i+1]>L2[i] then a:=L2[i]:b:=L2[i+1]:
				while a=L2[i] do
					c:=(a+b)/2:
					if is(subs(var=a,f)*subs(var=c,f)>0)=true and subs(var=c,h)<>0
						then a:=c else b:=c:
					fi:
				od: 
				L2:=subsop(i=a,L2):
			else a:=L1[i]:b:=L1[i+1]:
				while b=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f)*subs(var=c,f)>0)=true and subs(var=c,h)<>0
						then b:=c else a:=c:
					fi:
				od:
			fi:
		fi: 
	od:
	#print(L1,L2,l):
	j:=nops(L1): #print(L1,j):
	if j=0 then  # print(L1,j): 
                    k:=1: i:=0: while k=1 do
                                   if subs(var1=i,h)=0 or subs(var=i,g)=0 then i:=i+1: 
                                      else L:=[[i]]: k:=2: 
                                   fi:
                                od:
	else #print(L1,j):
		L:=[]:
		for i from 0 to j do 
			#print(i):
			if i=0 then 
     ##??????????????????????????????????????????
                             if is(subs(var=0,g)<>0)=true then if subs(var1=0,h)<>0 then L:=[op(L),[0]]:                                                                                         
			                                          else t:=0: l:=rootbound(numer(subs(var=1/var,f)),var): 
                                                                            # if is(subs(var1=l,h)<>0)=true then L:=[op(L),[l]]:#print(l): 
				                                             #   else l:=l/2:#print(l):
					                                        while t=0 do 
						                                  if is(subs(var1=l,h)<>0)=true 
							                            then t:=1: else l:=l/2:
							                             #print(l):print(h(l)):print(is(h(l)<>0)):print(t):
						                                  fi:                         
					                                         od:
					                                         L:=[op(L),[l]]: 
				                                             #fi:
                                                               fi:
                            fi:
			elif i=j then t:=0: l:=ceil(L2[j]):
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]: else l:=l+1:
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true then t:=1: else l:=l+1:
						fi: 
					od:
					L:=[op(L),[l]]:
				fi:
			else t:=0: l:=L2[i]: 
				if is(subs(var1=l,h)<>0)=true and is(subs(var=l,g)<>0)=true then L:=[op(L),[l]]: 
				else l:=(l+L1[i+1])/2:
					while t=0 do 
						if is(subs(var1=l,h)<>0)=true then t:=1: else l:=(L1[i+1]+l)/2:
						fi: 
					od:
					L:=[op(L),[l]]:                           
				fi:
			fi:
		od:
	fi:

	return L: 
end proc:
######################################### ѡȡ���Ե�
us2:=proc(g,n)
	local c,a,b,L1,L2,i,j,f,L,var,f1,m:
	f:=g:
	var:=op(indets(f)):if nops([var])=0 then return([[],[]]):fi:#print(var):#print(f):
	L:=uspensky2(f,var):#print(L):
	L1:=sort(map2(op,1,L),`<`):
	L2:=sort(map2(op,2,L),`<`):
	#print(L,L1,L2):
	if nargs=1 then m:=rootbound1(f,var): else m:=n:
	fi:
	for i to nops(L1)-1 while L2[i]<m do
		if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]<>L2[i+1] then f1:=normal(f/(var-L2[i])): #print(L2[i]):#
			if is(subs(var=L1[i],f1)*subs(var=L2[i],f1)>0)=true then 
				a:=L1[i+1]:b:=L2[i+1]:
				while a=L1[i+1] do
					c:=(a+b)/2:
					if is(subs(var=b,f1)*subs(var=c,f1)>0)=true
						then b:=c else a:=c:fi:
					od: L1:=subsop(i+1=a,L1):L2:=subsop(i+1=b,L2):
					#print(L1,L2):
				else if is(subs(var=L1[i+1],f1)*subs(var=L2[i+1],f1)>0)=true then a:=L1[i]:b:=L2[i]:
					while b=L2[i] do
						c:=(a+b)/2:
						if is(subs(var=a,f1)*subs(var=c,f1)>0)=true then a:=c else b:=c:
						fi:
					od:
					L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
				fi:
				#print(L1,L2):
			fi:
		else
			if L2[i]=L1[i+1] and subs(var=L2[i],f)=0 and L1[i+1]=L2[i+1] then f1:=normal(f/(var-L2[i])): 
				a:=L1[i]:b:=L2[i]:
				while b=L2[i] do
					c:=(a+b)/2:
					if is(subs(var=b,f1)*subs(var=c,f1)>=0)=true
						then b:=c else a:=c:
					fi:
				od: L1:=subsop(i=a,L1):L2:=subsop(i=b,L2):
			fi:
		fi:
	od:
	j:=nops(L1):
	for i from 0 to j do
		if i=0 then L:=[floor(L1[1])]:
		elif i=j then L:=[op(L),ceil(L2[j])]:
		else L:=[op(L),(L1[i+1]+L2[i])/2]:
		fi:
	od:
end proc:

######################### ʵ�����
uspensky2:= proc(A,x,widthgoal)
	local n, k, B, L, Aprime, Lprime1,Lprime2, widthgoal1,f0,powerremover,L1,L2:
	f0:=convert(A,'sqrfree'):
	if type(f0,`*`) then powerremover := proc (x) 
		if type(x,'integer') then 1 elif type(x,`^`) then op(1,x) else x 
		end if end proc: f0 := expand(map(powerremover,f0)) elif 
		type(f0,`^`) then f0 := op(1,f0) 
	end if:
	f0:=expand(f0):
	#readlib(realroot):
	n:= degree(f0,x):
	B:= rootbound1(f0,x):
	for k while 2 < B do
		B := iquo(B+1,2)
	end do:
	if coeff(f0,x,0) = 0 then
		L := [[0, 0]]:
		Aprime := expand(f0/x)
	else
		Aprime := f0:
		L := []
	end if:
	if nargs = 2 then
		widthgoal1 := 2^k
	else
		widthgoal1 := widthgoal
	end if:
	Lprime1 := uspensky3(Aprime,x,n,k,widthgoal1):
	Aprime := subs(x = -x,Aprime):  
	Lprime2 := map(y -> [-op(2,y), -op(1,y)],uspensky3(Aprime,x,n,k,widthgoal1)):
	return [op(L), op(Lprime1), op(Lprime2)]:
end proc:
######################### ʵ�����
uspensky2p:= proc(A,x,widthgoal)
	local n, k, B, L, Aprime, Lprime1, widthgoal1,f0,powerremover,L1,L2:
	f0:=convert(A,'sqrfree'):
	if type(f0,`*`) then powerremover := proc (x) 
		if type(x,'integer') then 1 elif type(x,`^`) then op(1,x) else x 
		end if end proc: f0 := expand(map(powerremover,f0)) elif 
		type(f0,`^`) then f0 := op(1,f0) 
	end if:
	f0:=expand(f0):
	#readlib(realroot):
	n:= degree(f0,x):
	B:= rootbound1(f0,x):
	for k while 2 < B do
		B := iquo(B+1,2)
	end do:
	if coeff(f0,x,0) = 0 then
		#L := [[0, 0]]:
                 L:=[]:
		Aprime := expand(f0/x)
	else
		Aprime := f0:
		L := []
	end if:
	if nargs = 2 then
		widthgoal1 := 2^k
	else
		widthgoal1 := widthgoal
	end if:
	Lprime1 := uspensky3(Aprime,x,n,k,widthgoal1):
	return [op(L), op(Lprime1)]:
end proc:

#########################################
############ �������Ͻ�

rootbound1 := proc(f, x)
	local r, d, c, p, i, j, s, rr:
	if not type(x,name) then
		error "2nd argument must be a name"
	end if:
	p := expand(f):
	d := degree(p,x):
	if d = 0 or p = 0 then
		return 1
	end if:
	c := coeff(p,x,d):
	p := map(abs,taylor(p-c*x^d,x,d+1)):
	c := abs(c):
	r := 1:
	i := 0:
	while signum(c*r^d-subs(x = r,p)) <=0  do
		r := 2*r:
		i := i+1
	end do:
	s := r:
	i := min(i,3):
	for j to i do
		s := 1/2*s:
		rr := r-s:
		if signum(subs(x = rr,p)-c*rr^d) <0 then
			r := rr
		end if
	end do:
	r
end proc:

###############################
uspensky3:= proc(A,x,n,k,widthgoal)
	local B, Lprime, L:
	if 0 <= k then
		B := subs(x = 2^k*x,A)
	else
		B := 2^(-k*n)*subs(x = 2^k*x,A)
	end if:
	Lprime:=zero_one1(B,x,n,widthgoal/(2^k)):
	L :=map(subs(_xxx = k,proc (x) [op(1,x)*2^_xxx, op(2,x)*2^_xxx] end proc),Lprime):
	return L:
end proc:

################################3
zero_one1:=proc(A, x, n, widthgoal)
	local Astar, var, L, Aprime, Lprime, Aprime2, Lprime2, y:
	Astar := expand(subs(y = x+1,expand(y^n*subs(x = 1/y,A)))):
	var := polyvariations1(Astar,x,n):
	if var = 0 then
		return []
	elif var = 1 then
		if 1 <= widthgoal then
			return [[0, 1]]
		else
			return midpoint1(A,x,n,widthgoal)
		end if
	end if:
	Aprime := subs(x = 1/2*x,A):
	if subs(x =1,Aprime) =0 then
		L := [[1/2, 1/2]]:
		evala(Divide(A,2*x-1,'Aprime')):
		Aprime := subs(x = 1/2*x,Aprime):
	else
		L := []
	end if:
	Aprime := expand(2^n*Aprime):
	Lprime := zero_one1(Aprime,x,n,2*widthgoal):
	L := [op(L), op(map((x, y) -> map(y,x),Lprime,z -> 1/2*z))]:
	Aprime2 := expand(subs(x = x+1,Aprime)):
	Lprime2 := zero_one1(Aprime2,x,n,2*widthgoal):
	L := [op(L), op(map((x, y) -> map(y,x),Lprime2,z -> 1/2*z+1/2))]:
end proc:
#################################
polyvariations1:=proc(poly, var, n)
	local taypoly, count, i, nterms:
	if type(poly,`+`) then
		taypoly := series(poly,var,n+1):
		count := 0:
		nterms := 1/2*nops(taypoly)-1:
		for i to nterms do
			if signum(op(2*i-1,taypoly))<>signum(op(2*i+1,taypoly)) then
				count := count+1:
				if 1 < count then
					return 2
				end if
			end if
		end do:
		return count
	else
		return 0
	end if:
end proc:
################################
midpoint1:=proc(poly, var, n, widthgoal)
	local l, r, fl, fr, mid, fm, poly1, intsize:
	l := 0:
	r := 1:
	poly1 := convert(poly,horner):
	fl := subs(var = l,poly1):
	if fl = 0 then
		return [0, 0]
	end if:
	fr := subs(var = r,poly1):
	if fr = 0 then
		return [1, 1]
	end if:
	intsize := 1:
	while widthgoal < intsize do
		intsize := 1/2*intsize:
		mid := intsize+l:
		fm := subs(var = mid,poly1):
		if fm = 0 then
			return [[mid, mid]]
		elif 0 < signum(fm)*signum(fl) then
			fl := fm:
			l := mid
		else
			fr := fm:
			r := mid
		end if
	end do:
	return [[l, r]]
end proc:
#######################
discrg:= proc(poly1 ,poly2 ,var)
	local f ,g ,tt ,d ,bz ,i ,ar ,j ,mm ,dd :
	f:=expand (poly1) :
	g:=expand (poly2*diff(f,var)):print(g):
	d := degree (f ,var) :print(d):
	if d <= degree (g ,var) then g := rem(g,f,var):
	fi :
	g := tt*var^d + g:
	bz := subs (tt = 0,bezout (f ,g ,var) ) :
	ar :=[]:
	for i to d do
		ar :=[op (ar) ,row(bz ,d+1-i)]
	od :
	mm:= matrix (ar) :
	dd := [1] :
	for j to d do
		dd := [op (dd) ,det(submatrix (mm ,1..j ,1..j) ) ]
	od :
	return dd:
end :
###################################################tv
tv:=proc(poly)
	local var,vars,lv,po,po1,t1,t2:
	po:=rhs(poly)-lhs(poly):print(po):
	po:=numer(po)*denom(po):
	if degree(po)<>ldegree(po) then error"This polynomial is not homonegeous!":
	fi:
	var:=[op(indets(po))]:vars:=nops(var):#print(var):
	if vars<>3 then error"Only treat 3 variables!":
	fi:
	if type(po,symmfunc(op(var)))=true then print("It is symmectric"):tvnd(po): 
		#elif cyclic(po,var)=true then print("It is cyclic"): po1:=subs(var[2]=t1,var[3]=t2,po):po1:=subs(t1=var[3],t2=var[2],po1):tvnd(po+po1):tvnd(po*po1):
	else lv:=cat(`not symmetric`):print(lv):tv1(po>=0,[1>=0]):
	fi:
end:
####################################################tvnd
tvnd:=proc(poly::polynom)
	local var,vars,l,A,B,C,D,E,F,G,i,j,k,p,q,r,t,f1,f2,f3,f4,f0,L,a,b,c,m,n,g,s,d,e,tim,f,g1,g2,g3,g4,g0,L1,L2,L3,sep,r1,r2,B1,B2,B3,B4,B5,C1,C2,sep1,sep2,h,H,P,i1,i2,i3,u:
	if degree(poly)<>ldegree(poly) then error"This polynomial is not homonegeous!":
	fi:
	var:=[op(indets(poly))]:vars:=nops(var):#if vars<>3 then error"Only treat 3 variables!":fi:
	if type(poly,symmfunc(op(var)))<>true then error"It is not symmetric!":
	fi:

	tim:=time():
	if is(subs(var[1]=1,var[2]=1,var[3]=1,poly)<0)=true then print(time()-tim): print(`Not PSD`):return false:
	fi:
	f1:=sqrfree2(subs(var[2]=1,var[3]=1,poly)):f2:=sqrfree2(subs(var[2]=1,var[3]=0,poly)):
	if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:fi:if subs(var[1]=0,f2)=0 then f2:=f2/var[1]:
	fi:#print(f1):print(f2):
	if degree(f1)=0 or degree(f1)=-infinity then if is(tcoeff(f1)<0)=true then print(f1): print(`Not PSD`):print(time()-tim):return false:fi:
	else 
		f1:=uspensky2(expand(f1),var[1]):print(f1):if f1<>[] then print(f1,time()-tim): print(`Not PSD`):return false:
	fi:
fi:
if degree(f2)=0 or degree(f2)=-infinity then if is(tcoeff(f2)<0)=true then print(`Not PSD`):print(time()-tim):return false:fi: 
else 
	f2:=uspensky2(expand(f2),var[1]):if f2<>[] then print(f2,time()-tim): print(`Not PSD`):return false:fi:fi:
	g:=0:
	f:=poly:
	u:=[var[1]^3-var[1]^2*p+var[1]*q-r,var[1]^2+var[2]^2+var[1]*var[2]-p*(var[1]+var[2])+q,var[1]+var[2]+var[3]-p]:
	g:=prem(f,u[3],var[3]):
	g:=prem(g,u[2],var[2]):
	g:=prem(g,u[1],var[1]):#print(poly):
	h:=g:
	#print(g):
	g:=subs(p=1,g):
	print(degree(g,r)):
	if nops([op(indets(g))])=1 then print(`PSD`): return true:
	fi:

	if degree(g,r)=2 then 
		if (op(2,us2(lcoeff(g,r),1/3))<>[] and op(1,op(2,us2(lcoeff(g,r),1/3)))<1/3) or is(subs(q=1/4,lcoeff(g,r))>=0)=true then
			l:=g:#print(l):
			r1:=solve(diff(l,r),r):#print(r1):
			l:=numer(subs(r=r1,l)):#print(l):
			r2:=numer(subs(r=r1,q^2-4*r-4*q^3+18*q*r-27*r^2)):#print(r2):
			g[1]:=r2: 
			g[2]:=q*(1-3*q):
			g[3]:=normal(r1*denom(r1)^2):#print(g[3]):
			g[0]:=sqrfree2(l):
			if degree(g[0])=0 or degree(g[0])=-infinity then if tcoeff(g[0])<0 then print(`Not PSD`):print(time()-tim):return false: else print(time()-tim):print(`PSD`):
				return true:
			fi:
		fi:
		g[5]:=g[0]:
		for i to 3 do
			if g[i]<>0 then g[5]:=g[5]*g[i]:
			fi od:
			g[5]:=delp(sqrfree1(g[5])):
			#print(g[5]):
			d:=degree(g[5]):
			# print(g[5]):
			L:=us2(g[5],1/3):
			L1:=op(1,L):L2:=op(2,L):
			lprint(L1,L2):
			for i to nops(L1)-1 while L2[i]<1/3 do
				j:=(L2[i]+L1[i+1])/2: #print(i):
				f1:=subs(q=j,g[1]):f2:=subs(q=j,g[2]):f0:=subs(q=j,g[0]):f3:=subs(q=j,g[3]):
				#print(f1,f2,f3,f4):
				if is(f1>=0)=true and is(f2>=0)=true and is(f3>=0)=true and is(f0<0)=true
					then print(`Not PSD`):print(time()-tim):return false:
				fi:
			od:
		fi:
	fi:

	if degree(g,r)>2 then 
		H[degree(g,r)]:=h:
		for i to degree(g,r) do
			H[degree(g,r)-i]:=diff(H[degree(g,r)-i+1],r):#print(H[degree(g,r)-i]):
		od:
		f1:=expand(subs(p=2+var[1],q=1+2*var[1],r=var[1],H[0])):
		j:=signum(lcoeff(f1)):
		f1:=sqrfree2(f1):
		if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:
		fi:
		if uspensky2(expand(f1),var[1])<>[] then j:=j*2:
		fi:
		for i to degree(g,r)-1 while j mod 4<>0 do
			f1:=expand(subs(p=2+var[1],q=1+2*var[1],r=var[1],H[i])):f2:=expand(subs(p=1+var[1],q=var[1],r=0,H[i])):
			if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:
			fi:
			if subs(var[1]=0,f2)=0 then f2:=f2/var[1]:
			fi:#print(f1):print(f2):
			if signum(lcoeff(f1))<>signum(lcoeff(f2)) or uspensky2((f1),var[1])<>[] or uspensky2((f2),var[1])<>[] then j:=2*j:
			else
				if j mod 2=0 then if signum(lcoeff(f1))*j<=0 then j:=signum(lcoeff(f1)): else j:=j*2:
				fi:
			else j:=signum(lcoeff(f1)):
			fi:
		fi:
		print(j):
	od:
	#print(i):
	if j=-2 or j mod 2<>0 then print(`PSD`):return true:
	fi:

	P[degree(h,p)]:=h: #print(P[degree(h,p)]):#print(degree(h,p)):
	for i from 1 to degree(h,p) do
		#print(i): 
		P[degree(h,p)-i]:=diff(P[degree(h,p)-i+1],p): #print(P[degree(h,p)-i]):
	od:
	f1:=expand(subs(p=2+var[1],q=1+2*var[1],r=var[1],P[0])):
	j:=signum(lcoeff(f1)):
	f1:=sqrfree2(f1):
	if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:
	fi:
	if uspensky2(expand(f1),var[1])<>[] then j:=j*2:
	fi:
	for i to degree(h,p)-1 while j mod 4<>0 do
		f1:=expand(subs(p=2+var[1],q=1+2*var[1],r=var[1],P[i])):f2:=expand(subs(p=1+var[1],q=var[1],r=0,P[i])):
		if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:
		fi:
		if subs(var[1]=0,f2)=0 then f2:=f2/var[1]:
		fi:#print(f1):print(f2):
		if signum(lcoeff(f1))<>signum(lcoeff(f2)) or uspensky2((f1),var[1])<>[] or uspensky2((f2),var[1])<>[] then j:=2*j:
		else
			if j mod 2=0 then 
				if signum(lcoeff(f1))*j<=0 then j:=signum(lcoeff(f1)): else j:=j*2:
				fi:
			else j:=signum(lcoeff(f1)):
			fi:
			fi:
			print(j):
		od:
		#print(i):
		if j=-2 or j mod 2<>0 then print(`PSD`):return true:
		fi:

		H[degree(g,q)]:=h:
		for i from 1 to degree(g,q) do
			H[degree(g,q)-i]:=diff(H[degree(g,q)-i+1],q): #print(H[degree(g,q)-i]):
		od:
		f1:=expand(subs(p=2+var[1],q=1+2*var[1],r=var[1],H[0])):
		j:=signum(lcoeff(f1)):
		f1:=sqrfree2(f1):
		if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:
		fi:
		if uspensky2(expand(f1),var[1])<>[] then j:=j*2:
		fi:
		for i to degree(g,q)-1 while j mod 4<>0 do
			f1:=expand(subs(p=2+var[1],q=1+2*var[1],r=var[1],H[i])):f2:=expand(subs(p=1+var[1],q=var[1],r=0,H[i])):
			if subs(var[1]=0,f1)=0 then f1:=f1/var[1]:
			fi:
			if subs(var[1]=0,f2)=0 then f2:=f2/var[1]:
			fi:#print(f1):print(f2):
			if signum(lcoeff(f1))<>signum(lcoeff(f2)) or uspensky2((f1),var[1])<>[] or uspensky2((f2),var[1])<>[] then j:=2*j:
			else 
				if j mod 2=0 then if signum(lcoeff(f1))*j<=0 then j:=signum(lcoeff(f1)): else j:=j*2:
				fi:
			else j:=signum(lcoeff(f1)):
			fi:
		fi:
		print(j):
	od:
	#print(i):
	if j=-2 or j mod 2<>0 then print(`PSD`):return true:
	fi:
	l:=g:#print(l):
	r2:=q^2-4*r-4*q^3+18*q*r-27*r^2:
	g[1]:=r2*r: 
	g[2]:=q*(1/3-q):
	g[0]:=sqrfree2(l):
	g[5]:=g[0]:
	for i to 2 do
		if g[i]<>0 then g[5]:=g[5]*g[i]:
		fi od:
		g[5]:=sqrfree1(g[5]):
		D:=resultant(g[5],diff(g[5],r),r):
		D:=delp(sqrfree1(D)):#print(D):
		d:=degree(D):print(d):
		L:=us2(D,1/3):#print(L):
		L1:=op(1,L):L2:=op(2,L):
		for i to nops(L1)-1 while L2[i]<1/3 do #print(i):
			C:=(L2[i]+L1[i+1])/2:
			C1:=subs(q=C,g[5]):
			C1:=delp(sqrfree1(C1)):#print(C1):
			d:=degree(C1):print(d):
			B:=us2(C1,1/27):
			B1:=op(1,B):B2:=op(2,B):
			for j to nops(B1)-1 while B2[j]<1/27 do
				C2:=(B2[j]+B1[j+1])/2:
				lprint([C,C2]):
				if is(subs(r=C2,q=C,g[0])<0)=true and is(subs(r=C2,q=C,g[1])>=0)=true and is(subs(r=C2,q=C,g[2])>=0)=true
					then print(`Not PSD`):print(subs(r=C2,q=C,g[0])):print(time()-tim):return false:
				fi:
			od:
		od:
	fi:
	print(time()-tim):print(`PSD`):
	return true:
end:
################################### �ֻ��Գ�
cyc:=proc(poly,L)
	local var,i,vars,g,f,j:
	if nargs=2 then var:=L else
		var:=[op(indets(poly))]:
	fi:
	vars:=nops(var):
	#f:=0:
	f[1]:=poly:
	#f:=f[1]:print(f):
	for i to vars-1 do
		f[i+1]:=subs(seq(var[j]=t[(j+i)mod(vars)],j=1..vars),poly):
		f[i+1]:=subs(seq(t[j]=var[j],j=1..vars-1),t[0]=var[vars],f[i+1]):
		#print(f[i+1]):
		#f:=f+f[i+1]:
	od:
	f:=add(f[i],i=1..vars):
	return f:
end:

#####################################
##################################################
##                                              ##
##   a loop `rads` eliminating multi-radicals   ##
##                                              ##
##################################################
rads:=proc(expr)
	local ep,np,i,nq,j,rad,nr,rp,ob,ob1,ob2,tmp1,tmp2:

	ep:=expand(expr):
	rad:=efindrads(expr):

	if rad={} then RETURN(ep)
	else
		rad:=[op(rad)]:
		rad:=ord(rad):
		nr:=nops(rad):

		for i from nr to 1 by -1 do ep:=subs(rad[i]=uu[i],ep):
		od:
		ep:=simplify(ep,radical,symbolic):
		while hastype(ep,radical) do
			tmp1:=indets(ep):tmp1:=[op(tmp1)]:
			for i to nops(tmp1) do
				ob:=tmp1[i]:
				if hastype(ob,radical) then
					for j to nr do
						if op(1,rad[j])=op(1,ob) then ep:=subs(ob=uu[j]^numer(op(2,ob)),ep)
						fi:
					od:
				fi:
			od:
		od:

		for i to nr do
			if i<>nr then
				for j from i+1 to nr do
					if hastype(rad[i],name) then
						rad[j]:=subs(op(1,rad[i])=uu[i]^denom(op(2,rad[i])),rad[j]):
						if member(uu[i],indets(rad[j])) then
							tmp1:=op(1,rad[j]):tmp2:=op(2,rad[j]):
							rad[j]:=expand(simplify(tmp1,radical,symbolic))^tmp2:
							rad[j]:=subs(csgn(uu[i])=1,rad[j]):
						fi:
					else  rad[j]:=subs(rad[i]=uu[i],rad[j]):
					fi:
				od:
			fi:
		od:
		ep:=simplify(ep,radical,symbolic):
		ep:=numer(ep):
		for i from nr to 1 by -1 do
			ob1:=op(1,rad[i]):  ob2:=op(2,rad[i]):
			ob:=ob1^numer(ob2)-uu[i]^denom(ob2):
			ob:=numer(ob):
			ep:=resultant(ep,ob,uu[i]):
		od:
	fi:
	if whattype(ep)=`^` then ep:=op(1,ep)
	fi:
	ep
end:

efindrads:=proc(expr)
	local ep,np,rad,i,j,ob,nq:

	ep:=expand(expr): np:=nops(ep): rad:={}:
	#print(ep):
	if type(ep,radical) then
		if hastype(ep,name) then
			rad:={op(1,ep)^(1/denom(op(2,ep)))} union efindrads(op(1,ep)):
		else
			rad:={ep} union efindrads(op(1,ep)):
		fi:
		RETURN(rad):
	fi:

	for i to np do
		ob:=op(i,ep):
		if type(ob,radical) then
			if hastype(ob,name) then
				rad := rad union {op(1,ob)^(1/denom(op(2,ob)))} union efindrads(op(1,ob)):
			else
				rad := rad union {ob} union efindrads(op(1,ob)):
			fi:
		else
			nq:=nops(ob):
			for j to nq do
				if type(op(j,ob),radical) then
					rad:=rad union efindrads(op(j,ob)):
				fi:
			od
		fi:
	od:
	rad
end:

ord:=proc(lst1)
	local lst,tmp,n,i,j,m,k:

	lst:=lst1:n:=nops(lst):
	for i to n-1 do
		for j from i+1 to n do
			m:=denom(op(2,lst[j])):
			if hastype(lst[j],name) then
				for k to m-1 do
					if has(lst[i],op(1,lst[j])^(k/m)) then tmp:=lst[i]: lst[i]:=lst[j]: lst[j]:=tmp
					fi:
				od:
			else
				if has(lst[i],lst[j]) then tmp:=lst[i]: lst[i]:=lst[j]: lst[j]:=tmp 
				fi:
			fi:
		od:
	od:
	lst
end:



#################################################
cyctq:=proc(f)
	local k,l,m,n,f1,f2,f3,f4,f5,f6,f7,g1,g2,var,vars,tim:
	tim:=time():
	var:=[op(indets(f))]:#print(var):
	vars:=nops(var):
	g1:=coeff(f,var[1]^2): #print(g1):
	#if degree(g1,var[2])>=2 then print(var):
	k:=coeff(g1,var[2]^2):
	#else k:=0:fi:
	#print(k):
	#if degree(g1,var[2])>=1 then
	g2:=coeff(g1,var[2]):
	l:=coeff(g2,var[3]):
	#else l:=0:fi:
	g1:=coeff(f,var[1]^3):
	m:=coeff(g1,var[2]):
	n:=coeff(g1,var[3]):
	f7:=-768+352*k^2-332*l^2+180*n^2+180*m^2+56*k^3-8*k^4+14*l^3+132*n^3+132*m^3+42*n^4+42*m^4-480*k-60*l*m*n-192*n+32*k*l*m*n-192*m+912*l+l^4-354*k*m*n+158*k*l*n+158*k*l*m+26*k^2*m*n-11*k*l*n^2+22*k^2*l*m+22*k^2*l*n-45*k*m*n^2-90*l*m^2*n-45*k*m^2*n-11*k*l*m^2+23*l^2*m*n-90*l*m*n^2+k*l^2*m+k*l^2*n+36*m*n-480*k*m+592*k*l-480*k*n-60*l*m-60*l*n+8*k^3*m+8*k^3*n-20*k^2*l+32*k^2*n+32*k^2*m-12*k^3*l+234*m*n^2+234*m^2*n-192*l*n^2-258*k*n^2-192*l*m^2-258*k*m^2+116*l^2*m+116*l^2*n+87*m^3*n+87*m*n^3-15*k*n^3+90*m^2*n^2-30*l*n^3-15*k*m^3-30*l*m^3+25*l^2*m^2+25*l^2*n^2-14*k^2*m^2-14*k^2*n^2-146*k*l^2-10*l^3*m-10*l^3*n-2*k^2*l^2+3*k*l^3:
	f6:=4*k^2+2*k*l-4*k*m-4*k*n+l^2-7*l*m-7*l*n+13*m^2-m*n+13*n^2-40*k+20*l+8*m+8*n-32:
	f5:=-4*k^3*m^2-4*k^3*n^2-4*k^2*l*m^2+4*k^2*l*m*n-4*k^2*l*n^2-k*l^2*m^2+4*k*l^2*m*n-k*l^2*n^2+8*k*l*m^3+6*k*l*m^2*n+6*k*l*m*n^2+8*k*l*n^3-2*k*m^4+10*k*m^3*n-3*k*m^2*n^2+10*k*m*n^3-2*k*n^4+l^3*m*n-9*l^2*m^2*n-9*l^2*m*n^2+l*m^4+13*l*m^3*n-3*l*m^2*n^2+13*l*m*n^3+l*n^4-7*m^5-8*m^4*n-16*m^3*n^2-16*m^2*n^3-8*m*n^4-7*n^5+16*k^4+16*k^3*l-32*k^2*l*m-32*k^2*l*n+12*k^2*m^2-48*k^2*m*n+12*k^2*n^2-4*k*l^3+4*k*l^2*m+4*k*l^2*n-12*k*l*m^2-60*k*l*m*n-12*k*l*n^2+40*k*m^3+48*k*m^2*n+48*k*m*n^2+40*k*n^3-l^4+10*l^3*m+10*l^3*n-21*l^2*m^2+12*l^2*m*n-21*l^2*n^2+10*l*m^3+48*l*m^2*n+48*l*m*n^2+10*l*n^3-17*m^4-14*m^3*n-21*m^2*n^2-14*m*n^3-17*n^4-16*k^3+32*k^2*l-48*k^2*m-48*k^2*n+80*k*l^2-48*k*l*m-48*k*l*n+96*k*m^2+48*k*m*n+96*k*n^2-24*l^3-24*l^2*m-24*l^2*n+24*l*m^2-24*l*m*n+24*l*n^2-16*m^3-48*m^2*n-48*m*n^2-16*n^3-96*k^2-64*k*l+64*k*m+64*k*n+96*l^2-32*l*m-32*l*n-16*m^2-32*m*n-16*n^2+64*k-128*l+64*m+64*n+128:
	f3:=k+1+m+n+l:
	f1:=2+k-m-n:
	f2:=l-2*k-m+4:
	f4:=3*(1+k)-m^2-n^2-m*n:
	if (f1=0 and m=n and f2=0 and m>=1 and m<=4) or (f3=0 and f4>=0) or (f1>0 and f3>0 and ((f5>0 and (f6<=0 or f7<=0)) or (f5=0 and f7<0))) then print(psd,time()-tim): return true: else print(false,time()-tim): return false:
	fi:
end:

##################################
#f:=(\sum_i^sx_i^2)^2-4\sum_i^sx_i^2x_{i+1}^2
######################################
hpoly:=proc(k)
	local var,i,f:
	var:=seq(x[i],i=1..k):
	f:=0:
	for i from 1 to k do
		f:=f+var[i]^2:
	end do:
	f:=f^2:
	for i from 1 to k-1 do
		f:=f-4*var[i]^2*var[i+1]^2:
	end do:
	f:=f-4*var[k]^2*var[1]^2:
	return f:
end:

###################################
mpoly:=proc(m)
 local f,i,j,k,a;
 f:=(sum(a[i]^2,i=1..3*m+2))^2:
 for i to 3*m+2 do
 for j from 0 to m do
 k:=(i+3*j+1) mod (3*m+2): #print(k,i,j,i+3*j+1,3*m+2):
 if k=0 then k:=3*m+2:fi:
 f:=f-2*a[i]^2*a[k]^2:
 od:
 od:
 return f:
 end:
#####################################
###################################
mppoly:=proc(m)
 local f,i,j,k;
 f:=(sum(a[i],i=1..3*m+2))^2:
 for i to 3*m+2 do
 for j from 0 to m do
 k:=(i+3*j+1) mod (3*m+2): #print(k,i,j,i+3*j+1,3*m+2):
 if k=0 then k:=3*m+2:fi:
 f:=f-2*a[i]*a[k]:
 od:
 od:
 return f:
 end:
######################################
hppoly:=proc(k)
	local var,i,f:
	var:=seq(x[i],i=1..k):
	f:=0:
	for i from 1 to k do
		f:=f+var[i]:
	end do:
	f:=f^2:
	for i from 1 to k-1 do
		f:=f-4*var[i]*var[i+1]:
	end do:
	f:=f-4*var[k]*var[1]:
	return f:
end:
##########################
chudeng:=proc(n,var)
local i,j,k,a,b,L,m,c,d,p,s,M:
M:=[]:
#print(n,var):
for j to n do
L:=choose(var,j):
p:=nops(L):
for k to p do
m:=nops(L[k]):
a[k]:=mul(L[k][i],i=1..m):
s[j]:=add(a[i],i=1..k):
od:
M:=[op(M),s[j]]
od:
return(M):
end:
###############################
opencadSampletest:=proc(poly)
	local tim,var,vars,l,A,i,j,k,t,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,ti,ti1,ti2,ti3:

	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):#print("Now, prove the nonnegative of",f):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:vars:=nops(var):
	if degree(poly)=ldegree(poly) then 
		if v=1 then
			print(`Homogenous`): 
		fi:
		hen:=var[vars]=1:
		f:=primpart(sqrfree1(subs(hen,f))): 
		var:=[op(indets(f))]:vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
	L:=[[f,1]]:
	h:=1:
	s:=0:
	if vars>1 then  
		for j from vars to 2 by -1  do
			f:=res(f,var[j]):
			L1:=sqrfree2(f):
			L:=[op(L),[L1,1]]:
		end do:
	fi:
        ti:=time():
	sa:=p2Sample(L,1):
	sa:=addPre(sa,hen):
	ti1:=time()-tim:
        ti2:=time()-ti:
        ti3:=ti-tim:
	return [nops(sa),ti1,ti3,ti2]:
end:
#################################
############################################
hantSampletest:=proc(poly,t)
	local tim,var,vars,l,A,i,j,k,L,f,g,h,Li,sa,hen,L1,g1,h1,g2,h2,g3,h3,g4,h4,L2,L3,L4,s,j1,ti,ti1,ti2,ti3:
	sa:=[]:
	hen:=[]:
	tim:=time(): 
	f:=primpart(sqrfree1(poly)):
	if f=1 then
		return sa:
	fi:
	var:=[op(indets(poly))]:
        vars:=nops(var):
	if degree(f)=ldegree(f) then 
		if v=1 then
			print(`Homogenous`):
		fi:
		hen:=var[vars]=1:
		f:=primpart(sqrfree1(subs(hen,f))): 
		var:=[op(indets(f))]:
                vars:=nops(var): 
	fi:
	if f=1 then
		return [[hen]]:
	fi:
       #print(f,[var,vars,t]):
        L:=hprojt(f,[var,vars,t]):
        #print(L):
        ti:=time():
	sa:=p2Sample(L,1):
	sa:=addPre(sa,hen):
        ti1:=time()-tim:
        ti2:=time()-ti:
        ti3:=ti-tim:
	return [nops(sa),ti1,ti3,ti2]:
end:
###########################
sympsdvp:=proc(poly,List)
 local i,vars,var,f,g,n,m,s,M,lc,v,ti,h,xx,L,f1,g1,psd,L2,j:
 ti:=time():
 f:=expand(numer(poly)):
 var:=[op(indets(f))]: #fi:
 vars:=nops(var):
 L:=chudeng(vars,var):
 L:=[op(List),op(L)]:
 #print(poly,L):
if sympsd(poly,L)=false 
  then print(`Not psd`):
  ti:=time()-ti:
 print(ti):
  return false:
fi:
 ti:=time()-ti:
 print(`psd`,ti):
  return true:
end:

############################
sympsd:=proc(poly,List)
 local i,vars,var,f,g,n,m,s,M,lc,v,ti,h,xx,L,f1,g1,psd,L2,j:
 ti:=time():
 g:=0:
 f:=expand(numer(poly)):
# if nargs=2 then var:=L else
 var:=[op(indets(f))]: #fi:
 vars:=nops(var):
 M:=chudeng(vars,var):#print(M,degree(f,var[1]),ldegree(f,var[1])):
 while degree(f,var[1])>0 do
 #print(degree(f,var[1])):
 if degree(f,var[1])=ldegree(f,var[1]) then 
 m:=f:
 n:=lcoeff(f,[seq(var[i],i=1..vars)]):
  f:=expand(f-n*(M[vars])^(degree(m,var[1]))):
 g:=g+n*sigma[vars]^(degree(m,var[1])):
 else
 m:=op(1,sort(f,[seq(var[i],i=1..vars)])):#print(m):
 n:=lcoeff(m,[seq(var[i],i=1..vars)]):#print(n):
 f:=expand(f-n*mul((M[i])^(degree(m,var[i])-degree(m,var[i+1])),i=1..vars-1)*M[vars]^degree(m,var[vars])):#print(f):
 g:=g+n*mul((sigma[i])^(degree(m,var[i])-degree(m,var[i+1])),i=1..vars-1)*(sigma[vars])^degree(m,var[vars]):#print(g):
 fi:
 od:
psd:=f+g:
L:=[]:
for j to nops(List) do
g:=0:
f:=expand(List[j]):
    while degree(f,var[1])>0 do
 #print(degree(f,var[1])):
 if degree(f,var[1])=ldegree(f,var[1]) then 
 m:=f:
 n:=lcoeff(f,[seq(var[i],i=1..vars)]):
  f:=expand(f-n*(M[vars])^(degree(m,var[1]))):
 g:=g+n*sigma[vars]^(degree(m,var[1])):
 else
 m:=op(1,sort(f,[seq(var[i],i=1..vars)])):#print(m):
 n:=lcoeff(m,[seq(var[i],i=1..vars)]):#print(n):
 f:=expand(f-n*mul((M[i])^(degree(m,var[i])-degree(m,var[i+1])),i=1..vars-1)*M[vars]^degree(m,var[vars])):#print(f):
 g:=g+n*mul((sigma[i])^(degree(m,var[i])-degree(m,var[i+1])),i=1..vars-1)*(sigma[vars])^degree(m,var[vars]):#print(g):
 fi:
 od:
L:=[op(L),f+g]:
od:
#print(`L`,L):
  #v:=[op(indets(g))]: #print(v):
  #v:=subs(seq(sigma[i]=i,i=1..vars),v):
#g;
h:=xx^vars+add((-1)^(j)*sigma[j]*xx^(vars-j),j=1..vars):
L:=[op(discrg1(h,xx)),op(L)]:
#print(psd,L):
#ineqreal(psd,L,2):
if ineqreal(psd,L,2)=false 
  then print(`Not psd`):
  ti:=time()-ti:
 print(ti):
  return false:
fi:
 ti:=time()-ti:
 print(ti):
  return true:
end:
################################
duichen:=proc(poly,L)
 local i,vars,var,f,g,n,m,s,M,lc,v,ti:
 ti:=time():
 g:=0:
 f:=expand(poly):
 if nargs=2 then var:=L else
 var:=[op(indets(f))]:fi:
 vars:=nops(var):
 M:=chudeng(vars,var):#print(M,degree(f,var[1]),ldegree(f,var[1])):
 while degree(f,var[1])>0 do
 #print(degree(f,var[1])):
 if degree(f,var[1])=ldegree(f,var[1]) then 
 m:=f:
 n:=lcoeff(f,[seq(var[i],i=1..vars)]):
  f:=expand(f-n*(M[vars])^(degree(m,var[1]))):
 g:=g+n*sigma[vars,vars]^(degree(m,var[1])):
 else
 m:=op(1,sort(f,[seq(var[i],i=1..vars)])):#print(m):
 n:=lcoeff(m,[seq(var[i],i=1..vars)]):#print(n):
 f:=expand(f-n*mul((M[i])^(degree(m,var[i])-degree(m,var[i+1])),i=1..vars-1)*M[vars]^degree(m,var[vars])):#print(f):
 g:=g+n*mul((sigma[vars,i])^(degree(m,var[i])-degree(m,var[i+1])),i=1..vars-1)*(sigma[vars,vars])^degree(m,var[vars]):#print(g):
 fi:
 od:
  v:=[op(indets(g))]: #print(v):
  v:=subs(seq(sigma[vars,i]=i,i=1..vars),v):
[g,v];
#return (nops([op(g)]),time()-ti):
end:
#######################
discrg1:= proc(poly1,var)
	local f ,g ,tt ,d ,bz ,i ,ar ,j ,mm ,dd :
	f:=expand (poly1) :
	g:=expand (1*diff(f,var)): #print(g):
	d := degree (f ,var): #print(d):
	if d <= degree (g ,var) then g := rem(g,f,var):
	fi :
	g := tt*var^d + g:
	bz := subs (tt = 0,bezout (f ,g ,var) ) :
	ar :=[]:
	for i to d do
		ar :=[op (ar) ,row(bz ,d+1-i)]
	od :
	mm:= matrix (ar) :
	dd := []:
	for j from 2 to d do
		dd := [op (dd) ,det(submatrix (mm ,1..j ,1..j) ) ]
	od :
        if d=3 then dd:=[dd[2]]: fi:
	return dd:
end :
##############################
#read`D:\\Program Files (x86)\\Maple 17\\psdgcd.txt`; hprojt(subs(A[5]=1,createBenchmark1(5)),[[seq(A[i],i=1..4)],4,2]); psdhp(createBenchmark1(5),2):
#read`D:\\Program Files (x86)\\Maple 17\\psdgcdv51.txt`; 
#read`D:\\Program Files\\Maple 17\\psdgcdv52.txt`;
# realroot-> uspensky2
#xprove(x+y+z>=a+b+1,[x^2+y^2+z^2>=a^2+b^2+1,x*y+y*z+z*x>=a*b+a+b,x*y*z>=a*b]);
#read`D:/Program Files (x86)/Maple 17/bottema2009`;
