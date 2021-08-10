# g=2; N is the mfd of a random Heegaard splitting of complexity L;
# Q=Z/2Z is a finite group;
# p(L) is the probability that the fundamental group of N has an epimorphism onto Q;
# p(Q,g) is the limit of p(L) as L goes to infinity;
# We compute p(Z/2Z,2) = 7/15.
G := Group( (8,12)(9,13)(10,14)(11,15), (4,12)(5,13)(6,14)(7,15), (2,7)(3,6)(8,13)(9,12), (1,3)(5,7)(9,11)(13,15), (2,3)(6,7)(10,11)(14,15) );;
ans := 0;;
for g in Elements(G) do
	chk := false;;
	for i in [1,4,5] do
		if i^g = 1 or i^g = 4 or i^g = 5 then
			chk := true;
		fi;
	od;
	if chk = true then
		ans := ans + 1;
	fi;
od;
Print(ans/Size(G), "\n");