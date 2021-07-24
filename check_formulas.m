load "rad_mont.m";

function gen_point_ord(A, ell)
    /*
        Return the x-coordinate of a point of order 3 on the Montgomery curve with coefficient A.
    */
    while true do
        x := Random(F);
        XQ, ZQ := scalar_multiplication_Montgomery((p+1) div ell, x, 1, A);
        if ZQ ne 0 then
            return XQ/ZQ;
        end if;
    end while;
end function;

// Checkin the correctness of 3-isogenies.
A := F ! 0;
t := gen_point_ord(A, 3);
n := 10;
A1 := act_three_Mont_with_point(A, t, n);   // 3M + 9A + I + n(E + 5M + 12A)
A2 := act_three_original(A, t, n);          // 4E + 30M + 51A + 3I + n(E + 3M + 12A)
print("3-isogenies");
printf "Coeff. by the new method: %o\n", A1;
printf "Coeff. by the original method: %o\n", A2;
if A1 eq A2 then
    print("Check 3-isogenies -> OK.\n");
end if;

// Checking the correctness of 4-isogenies between Montgomery- curves.
A := F ! 0;
n := -10;
A1 := act_four_Mont_min(A, n);  // 4E + 5M + 14A + 2I + n(1E + 3M + 4A + 1I)
/*
    The following function comes from the original code, crad_512.m.
    The cost is 3E + 13M + 19A + 1I for Montgomery- to Tate,
                1E + 3M + 5A + 1I for one 4-isogeny,
            and 2E + 2M + 8A + 2I for Tate to Montgomey-.
*/
A2 := act_with_four_on_Montgomery_min(A, n);    // $4E + 15M + 27A + 3I + n(1E + 3M + 5A + 1I)
print("4-isogenies");
printf "Coeff. by the new method: %o\n", A1;
printf "Coeff. by the original method: %o\n", A2;
if A1 eq A2 then
    print("Check 4-isogenies -> OK.");
end if;
