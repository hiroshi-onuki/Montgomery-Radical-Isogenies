load "rad_mont.m";

function csidh_action_replace_4iso(private_key, A)

  /*
    Replacing the action of the ideal of norm 4.
  */

  A := F ! A;
  //A := act_with_four_on_Montgomery_min(A, private_key[1] div 2);
  A := act_four_Mont_min(A, private_key[1] div 2);
  A := Montgomery_min_to_Montgomery(A);
  if IsOdd(private_key[1]) then A := 2-(4*((2+A)^sq_exp-2)^4)/(2-A)^2; end if;
  private_key := Remove(private_key, 1);
  A := act_with_nine_on_Montgomery(A, private_key[1] div 2);
  private_key[1] := private_key[1] mod 2;
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
  A := Montgomery_to_Montgomery_min(A);
  return A;
end function;

function csidh_action_replace_3iso(private_key, A)

  /*
    Replacing the action of the ideal of norm 3.
  */

  A := F ! A;
  A := act_with_four_on_Montgomery_min(A, private_key[1] div 2);
  A := Montgomery_min_to_Montgomery(A);
  if IsOdd(private_key[1]) then A := 2-(4*((2+A)^sq_exp-2)^4)/(2-A)^2; end if;
  private_key := Remove(private_key, 1);
  //A := act_with_nine_on_Montgomery(A, private_key[1] div 2);
  //private_key[1] := private_key[1] mod 2;
  A := act_three_Mont(A, private_key[1]);
  private_key[1] := 0;
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
  A := Montgomery_to_Montgomery_min(A);
  return A;
end function;

procedure csidh_key_exchange_relpace_4iso()
  t := Cputime();
  alice_private := cradical_private_keygen();
  bob_private := cradical_private_keygen();
  alice_public := csidh_action_replace_4iso(alice_private,0);
  printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_replace_4iso(bob_private,0);
  printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_replace_4iso(alice_private, bob_public);
  bob_alice := csidh_action_replace_4iso(bob_private, alice_public);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the new version.";
  else
    printf "new time : %o\n", Cputime(t);
    printf "The joint key is %o.\n", alice_bob;
  end if;
end procedure;

procedure csidh_key_exchange_relpace_3iso()
  t := Cputime();
  alice_private := cradical_private_keygen();
  bob_private := cradical_private_keygen();
  alice_public := csidh_action_replace_3iso(alice_private,0);
  printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_replace_3iso(bob_private,0);
  printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_replace_3iso(alice_private, bob_public);
  bob_alice := csidh_action_replace_3iso(bob_private, alice_public);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the new version.";
  else
    printf "new time : %o\n", Cputime(t);
    printf "The joint key is %o.\n", alice_bob;
  end if;
end procedure;
