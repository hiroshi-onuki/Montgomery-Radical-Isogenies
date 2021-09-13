load "rad_mont.m";
print("");

N := 1000;
private := [cradical_private_keygen() : i in [1..N]];

print("The original version.");
t := Cputime();
A := 0;
for i := 1 to N do
    A := csidh_action_new(private[i], A);
end for;
printf "The time of generating a public key : %o\n\n", Cputime(t);

print("Using new formulas.");
t := Cputime();
A := change_Mont_model(F!0, 1);
for i := 1 to N do
    A := csidh_action_Mont_plus(private[i], A, true);
end for;
printf "The time of generating a public key : %o\n\n", Cputime(t);

print("Using new formulas (only 4-isogenies).");
t := Cputime();
A := change_Mont_model(F!0, 1);
for i := 1 to N do
    A := csidh_action_Mont_plus(private[i], A, false);
end for;
printf "The time of generating a public key : %o\n\n", Cputime(t);
