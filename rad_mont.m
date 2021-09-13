/*
  The functions below are based on
  https://eprint.iacr.org/2021/699.
*/

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

function two_iso_Mont(A)
  /*
    The formula (4).
    Return the Montgomery coefficient of E_A/<(0,0)>.
    The cost is 1E + 3A + 1I.
  */
  alpha := (A + 2)^sq_exp;          // 1E + 1A
  return (A + 6) / (alpha + alpha); // 2A + 1I
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

function Mont_to_modMont(A, sign)
    /*
        Return the modified Montgomery coefficient 4(sign*A + 2).
        The cost is 3A.
    */
    a := sign*A + 2;    // 1A
    a +:= a;       // 1A
    a +:= a;       // 1A
    return a;
end function;

function modMont_to_Mont(a, sign)
    /*
        Return the Montgomery coefficient sign*(a/4 - 2)
        The cost is 1M + 1A.
    */
    inv_four := F ! 1/4;    // This is pre-computed and stored.
    A := sign*(a * inv_four - 2);    // 1M + 1A
    return A;
end function;

function sample_three_torsion_point_Montgomery(A, sign)
  /*
    Return a point of order 3 generating the ideal [3, pi - sign].
  */
  ell := 3;
  repeat
    possible_torsion := [];
    if sign gt 0 then
      repeat xP := Random(F); until IsSquare(((xP+A)*xP+1)*xP);
    else
      repeat xP := Random(F); until not IsSquare(((xP+A)*xP+1)*xP);
    end if;

    XQ, ZQ := scalar_multiplication_Montgomery((p+1) div ell, xP, 1, A);
    if ZQ ne 0 then
      proper := true;
      for d in Divisors(ell) do
        if d ne 1 and d ne ell and proper then
          XR, ZR := scalar_multiplication_Montgomery(d, XQ, ZQ, A);
          if ZR eq 0 then proper := false; end if;
        end if;
      end for;
      if proper then possible_torsion cat:= [XQ, ZQ]; end if;
    end if;
  until possible_torsion ne [];
  return possible_torsion[1]/possible_torsion[2];
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
    t := sample_three_torsion_point_Montgomery(A, Sign(n));
    A := act_three_Mont_with_point(A, t, Abs(n));
    return A;
end function;

function change_Mont_model(A, sign)
  /*
    An isomorphism between Montgomery curves sending
    ((-A * sign*\sqrt{A^2 - 4})/2, 0) to (0, 0).
    The cost is 2E + 2M + 6A + 1I.
  */
  delta := (A^2 - 4)^sq_exp;                 // 1E + 1M + 1A
  num := -A + 3*sign*delta;                  // 3A
  den := (2*delta*(delta - sign*A))^sq_exp;  // 1E + 1M + 2A
  return num / den;                         // 1I
end function;

function act_four_Mont(A, n)
  if n ne 0 then
    if n lt 0 then
      A := change_Mont_model(A, -1);
    end if;

    a := Mont_to_modMont(A, Sign(n));  // 3A
    for i := 1 to Abs(n) div 2 do
      a := four_iso_Mont(a);  // 1E + 3M + 4A + 1I
    end for;
    A := modMont_to_Mont(a, Sign(n));  // 1M + 1A

    if Abs(n) mod 2 eq 1 then
      A := Sign(n)*two_iso_Mont(Sign(n)*A);   // 1E + 3A + 1I
    end if;
  end if;

  // surface to floor (cost: 1E + 3M + 5A)
  if n ge 0 then
    sign := 1;
  else
    sign := -1;
  end if;
  A *:= sign;
  inv_two := F! 1/2;  // pre-computed
  delta := (A^2 - 4)^sq_exp;  // 1E + 1M + 1A
  x2 := (-A + delta) * inv_two; // 1M + 1A
  A := -1*2*(1 - 2*x2^2);  // 1M + 3A
  A *:= sign; 

  return A;
end function;

/*
    Functions for CSURF
*/

function csidh_action_Mont_plus(private_key, A, using_Mont_three)

  // 4-isogenies on Montgomery
  A := act_four_Mont(A, private_key[1]);
  private_key := Remove(private_key, 1);

  if using_Mont_three then
    // 3-isogenies on Montgomery
    A := act_three_Mont(A, private_key[1]);
    private_key[1] := 0;
  else
    A := act_with_nine_on_Montgomery(A, private_key[1] div 2);
    private_key[1] := private_key[1] mod 2;
  end if;

  // other radical isogenies
  if Abs(private_key[2]) gt 1 then
    A := act_with_five_on_Montgomery(A, private_key[2]);
    private_key[2] := 0;
  end if;
  if Abs(private_key[3]) gt 1 then
    A := act_with_seven_on_Montgomery(A, private_key[3]);
    private_key[3] := 0;
  end if;
  if Abs(private_key[4]) gt 1 then
    A := act_with_eleven_on_Montgomery(A, private_key[4]);
    private_key[4] := 0;
  end if;
  if Abs(private_key[5]) gt 1 then
    A := act_with_thirteen_on_Montgomery(A, private_key[5]);
    private_key[5] := 0;
  end if;
  
  while private_key ne [0 : i in [1..#private_key]] do
    xP := Random(F);
    twist := not IsSquare(((xP+A)*xP+1)*xP); if twist then A := -A; xP := -xP; end if;
    indices_ells_correct_sign := [];
    k := 1;
    for i := 1 to #ells do
      if private_key[#ells-i+1] gt 0 and not twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
    elif private_key[#ells-i+1] lt 0 and twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
      end if;
    end for;
    XQ, ZQ := scalar_multiplication_Montgomery((p+1) div k, xP, 1, A);
    for i in indices_ells_correct_sign do
      if ZQ ne 0 then
        xQ := XQ/ZQ;
        ell := ells[i];
        XR, ZR := scalar_multiplication_Montgomery(k div ell, xQ, 1, A);
        if ZR ne 0 then
          A, XQ, ZQ := act_with_ell_on_Montgomery(A, ell, XR/ZR, xQ,degree_bound);
          if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
        end if;
      end if;
    end for;
    if twist then A := -A; end if;
  end while;

  // floor to surface
  A := (A + 6)/(2*(A + 2)^sq_exp);

  return A;
end function;

procedure csidh_key_exchange_Mont_plus()
  t := Cputime();
  A := change_Mont_model(F!0, 1);
  alice_private := cradical_private_keygen();
  bob_private := cradical_private_keygen();
  alice_public := csidh_action_Mont_plus(alice_private,A,true);
  printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_Mont_plus(bob_private,A,true);
  printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_Mont_plus(alice_private, bob_public,true);
  bob_alice := csidh_action_Mont_plus(bob_private, alice_public,true);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the new version.";
  else
    printf "new time : %o\n", Cputime(t);
    printf "The joint key is %o.\n", alice_bob;
  end if;
end procedure;

csidh_key_exchange_Mont_plus();
