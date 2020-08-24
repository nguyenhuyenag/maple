# Tam thuc bac 2
Quadratic := proc(f, xvar::polynom)
	local x, a, b, c, tt, den, deg, P, F;
	F := numer(f);
	den := denom(f);
	if nargs > 2 then
		return `Invalid arguments!`;
	fi;
	deg := degree(xvar);
	x := op(indets(xvar));
	if deg = 1 then
		F := subs(x = tt, F);
	else
		F := simplify(subs(x = tt^(1/deg), F), `symbolic`);
	fi;
	if degree(F, tt) <> 2 then
		print(cat(`The input is NOT a quadratic polynomial of `, xvar));
		return -1;
	fi;
	F := collect(F, tt);
	a, b := coeff(F, tt^2), coeff(F, tt);
	c := F - a*tt^2 - b*tt;
	P := a*(tt + b/(2*a))^2 + factor((4*c*a - b^2)/(4*a));
	P := subs([tt = xvar], P);
	return map(t -> t / den, P);
end:
