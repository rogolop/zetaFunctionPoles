AttachSpec("SingularitiesDim2/IntegralClosureDim2.spec");
AttachSpec("ZetaFunction/ZetaFunction.spec");
Z := IntegerRing();
Q := RationalField();

// R<A_43,A_34,A_44,A_52,A_53,A_54> := RationalFunctionField(Q,6);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := y^6 - x^7 + A_52*x^5*y^2 + A_43*x^4*y^3 + A_34*x^3*y^4 + A_44*x^4*y^4 + A_53*x^5*y^3 + A_54*x^5*y^4;

// R<t1,t4,t6,t11> := RationalFunctionField(Q,4);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := 1/7*x^7 + 1/5*y^5 -t1*x^3*y^3 -t4*x^5*y^2 -t6*x^4*y^3 -t11*x^5*y^3;

// R<t1,t2,t6,t10> := RationalFunctionField(Q,4);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := -1/9*x^9 -1/4*y^4 +t1*x^7*y +t2*x^5*y^2 +t6*x^6*y^2 +t10*x^7*y^2;

// R<u1,u2,u3,u8,u9,u15> := RationalFunctionField(Q,6);
// assumeNonzero:={R| };
// P<x,y> := LocalPolynomialRing(R,2);
// f := x^6 +y^7 +u3*x^4*y^3 +u2*x^3*y^4 +u9*x^4*y^4 +u1*x^2*y^5 +u8*x^3*y^5 +u15*x^4*y^5;

// R<t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17> := RationalFunctionField(Q,18);
// assumeNonzero:={R| t0};
// P<x,y> := LocalPolynomialRing(R,2);
// f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0 + t3*x + t6*x^2 + t9*x^3 + t11*x^4 + t13*x^5 + t7*y + t10*x*y + t12*x^2*y + t14*x^3*y + t15*x^4*y + t16*x^5*y)^2 + (-x^7 + t1*x^5*y + t4*x^6*y + t2*x^3*y^2 + t5*x^4*y^2 + t8*x^5*y^2 + y^3)^2;

R<t0,t1,t2,t17> := RationalFunctionField(Q,4);
assumeNonzero:={R| t0};
P<x,y> := LocalPolynomialRing(R,2);
f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0)^2 + (-x^7 + t1*x^5*y + y^3)^2;
//f :=  (-x^5*y^4 + t17*x^3*y^5)*(t0)^2 + (-x^7 + t1*x^5*y + t2*x^3*y^2 + y^3)^2;

printf "Semigroup: %o\n", SemiGroup(f);
printf "f = %o\n", f;

L_all, sigma_all := ZetaFunctionStratification(f : assumeNonzero:=assumeNonzero,
                                                   verboseLevel:="default");

printf "Finished\n";
quit;

