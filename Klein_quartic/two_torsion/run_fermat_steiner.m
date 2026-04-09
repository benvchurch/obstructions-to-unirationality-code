// Driver: run steiner_genus2 pipeline on the Fermat quartic x^4+y^4+z^4

QQ := Rationals();
P2Q<x,y,z> := ProjectiveSpace(QQ, 2);
F_input := x^4 + y^4 + z^4;
FERMAT_MODE := true;
