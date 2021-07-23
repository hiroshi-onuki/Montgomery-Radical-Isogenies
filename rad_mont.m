load "crad_512.m";

function three_iso_Mont(t)
    /*
        The formula (10) in Theorem 7.
        The imput t is the x-coordinate of a point of order 3.
        The output is the x-coordinate of a point the codomain
        that generates the kernel of the next 3-isogeny.
        The cost is E + 5M + 12A.
    */
    t2 := t*t;                           // 1M
    t3 := t2 * t;                        // 1M
    alpha := (t3-t)^tri_exp;             // 1E + 1A
    tmp := t*alpha^2;                    // 2M
    td := tmp + tmp + tmp;               // 2A
    td +:= (t2 + t2 + t2 - 1) * alpha;   // M + 4A
    td +:= t3 + t3 + t3 - t - t;         // 5A
    return td;
end function;

function point_three_to_Mont(t)
    /*
        The formula (9).
        Return the Montgomery coefficient of the curve having a point (t, -) of order 3.
        The cost is 3M + 9A + I.
    */
    t2 := t*t;                      // 1M
    t3 := t2*t;                     // 1M
    t4 := t2*t2;                    // 1M
    tmp := t2 + t2 + t2;            // 2A
    tmp +:= tmp;                    // 1A
    num := -t4 -t4 -t4 - tmp + 1;   // 4A
    den := t3 + t3;                 // 1A
    den +:= den;                    // 1A
    A := num/den;                   // I
    return A;
end function;

function four_iso_Mont(a)
    /*
        The formula (20) in Theorem 14.
        Return the modified Montgomery coefficient of the codomain of the isogeny with kernel <(1, -)>.
        The cost is 1E + 3M + 4A + 1I.
    */
    if (p + 1) mod 16 eq 0 then
        epsilon := 1;
    else
        epsilon := -1;
    end if;
    b := a^quart_exp;               // 1E
    b *:= epsilon;                  // sign change depending on p.
    b2 := b*b;                      // 1M
    tmp := b + b;                   // 1A
    num := (b2 + tmp + tmp + 4)^2;  // 1M + 3A
    den := b * (b2 + 4);            // 1M + 1A
    ad := num/den;                  // 1I
    return ad;
end function;

function Mont_to_modMont(A)
    /*
        Return the modified Montgomery coefficient 4(A + 2).
        The cost is 3A.
    */
    a := A + 2;    // 1A
    a +:= a;       // 1A
    a +:= a;       // 1A
    return a;
end function;

function modMont_to_Mont(a)
    /*
        Return the Montgomery coefficient a/4 - 2
        The cost is 1M + 1A.
    */
    inv_four := F ! 1/4;    // This is pre-computed and stored.
    A := a * inv_four - 2;    // 1M + 1A
    return A;
end function;

function Montgomery_min_to_Montgomery_surface(A)
    /*
        Convert a Montgomery- coefficient to a Montogomery coefficient.
        The output curve is in the surface and (0, 0) generates the ideal [(1-sqrt{-p})/2, 2].
        The cost is 2E + 2M + 5A + 1I
    */
    d := (A^2 + 4)^sq_exp;  // 1E + 1M + 1A
    tmp := -A + d;          // 1A
    num := tmp + d + d;     // 2A
    den := d * tmp;         // 1M
    den +:= den;            // 1A
    den := den^sq_exp;      // 1E
    Ad := num/den;          // 1I
    return Ad;
end function;

function Montgomery_min_to_Montgomery_surface(A)
    /*
        Convert a Montgomery- coefficient to a Montogomery coefficient.
        The output curve is in the surface and (0, 0) generates the ideal [(1-sqrt{-p})/2, 2].
        The cost is 2E + 2M + 5A + 1I
    */
    d := (A^2 + 4)^sq_exp;  // 1E + 1M + 1A
    tmp := -A + d;          // 1A
    num := tmp + d + d;     // 2A
    den := d * tmp;         // 1M
    den +:= den;            // 1A
    den := den^sq_exp;      // 1E
    Ad := num/den;          // 1I
    return Ad;
end function;
function Montgomery_surface_to_Montgomery_min(A)
    /*
        Convert a Montgomery coefficient to a Montogomery- coefficient.
        The input curve is in the surface and (0, 0) generates the ideal [(1-sqrt{-p})/2, 2].
        The cost is 2E + 2M + 5A + 1I
    */
    d := (A^2 - 4)^sq_exp;  // 1E + 1M + 1A
    tmp := -A + d;          // 1A
    num := tmp + d + d;     // 2A
    den := d * tmp;         // 1M
    den +:= den;            // 1A
    den := den^sq_exp;      // 1E
    Ad := num/den;          // 1I
    return Ad;
end function;

function act_three_Mont_with_point(A, t, n)
    /*
        The action of l3^n, where l3 is an ideal of norm 3 using Montgomery curve only.
        The cost is 3M + 9A + I + n(E + 5M + 12A).
    */
    for i := 1 to n do
        t := three_iso_Mont(t);     // E + 5M + 12A
    end for;
    A := point_three_to_Mont(t);    // 3M + 9A + I
    return A;
end function;

function act_three_Mont(A, n)
    if n eq 0 then
        return A;
    end if;
    A *:= Sign(n);
    t := sample_ell_torsion_point_Montgomery(A, 3);
    A := act_three_Mont_with_point(A, t, n);
    return Sign(n)*A;
end function;

function act_three_original(A, t, n)
    /*
        The action of l3^n, where l3 is an ideal of norm 3 via Tate normal forms.
        This code is the function act_with_three_on_Montgomery in the original radical code without point generating.
        The cost is 4E + 30M + 51A + 3I + n(E + 3M + 12A).
    */
    if IsSquare(t^3 + A*t^2 + t) then
        sign := 1;
    else
        sign := -1;
    end if;
    A *:= sign;
    M, N := Montgomery_to_Tate(A, t : ell_eq_three := true);    // 1E + 8M + 10A + 1I
    M *:= -1;
    for i := 1 to n do
        M, N := three_iso(M, N);                                // E + 3M + 12A
    end for;
    M *:= -1;
    A := Weier_to_Montgomery([M,0,N,0,0]);                      // 3E + 22M + 41A + 2I
    return A*sign;
end function;

function act_four_Mont_min(A, n)
    /*
        The action of [(1-sqrt{-p})/2] on a Montgomery- curve.
        The cost is 4E + 5M + 14A + 2I + n(1E + 3M + 4A + 1I).
    */
    if n eq 0 then
        return A;
    end if;
    A *:= Sign(n);
    A := Montgomery_min_to_Montgomery_surface(A); // 2E + 2M + 5A + 1I
    a := Mont_to_modMont(A);    // 3A
    for i := 1 to Abs(n) do
        a := four_iso_Mont(a);  // 1E + 3M + 4A + 1I.
    end for;
    A := modMont_to_Mont(a);    // 1M + 1A
    A := Montgomery_surface_to_Montgomery_min(A); // 2E + 2M + 5A + 1I
    return Sign(n)*A;
end function;
