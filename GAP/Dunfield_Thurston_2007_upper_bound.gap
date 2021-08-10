for n in [5..9] do
	G:=AlternatingGroup(n);
	cc:=ConjugacyClassesMaximalSubgroups(G);
	ans:=0;;
	for H in cc do
		ans:= ans + Size(H) / ( Order(G) / Order(Representative(H)) ) / ( Order(G) / Order(Representative(H)) );
	od;
	Print(n, " : ", ans, " = ", Float(ans), "\n");
od;