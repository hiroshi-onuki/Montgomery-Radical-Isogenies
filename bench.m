load "rad_mont.m";
print("");

N := 10000;
private := [cradical_private_keygen() : i in [1..N]];

print("The original version.");
t := Cputime();
A := 0;
for i := 1 to N do
    A := csidh_action_new(private[i], A);
end for;
printf "The time of generating a public key : %o\n\n", Cputime(t);

print("Replacing 3-isogenies.");
t := Cputime();
A := 0;
for i := 1 to N do
    A := csidh_action_replace_3iso(private[i], A);
end for;
printf "The time of generating a public key : %o\n\n", Cputime(t);

print("Replacing 4-isogenies.");
t := Cputime();
A := 0;
for i := 1 to N do
    A := csidh_action_replace_4iso(private[i], A);
end for;
printf "The time of generating a public key : %o\n\n", Cputime(t);
