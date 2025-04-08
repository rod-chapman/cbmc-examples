with Interfaces; use Interfaces;
package Poly
  with SPARK_Mode => On
is
   subtype I32 is Integer_32;

   N : constant := 256;
   Q : constant := 8380417;
   Gamma2 : constant := (Q - 1) / 88;

   K : constant := 4;
   L : constant := 4;

   subtype IndexN is I32 range 0 .. N - 1;
   subtype IndexK is I32 range 0 .. K - 1;

   type Coeffs is array (IndexN) of I32;

   type T is record
      C : Coeffs;
   end record;

   procedure Decompose (A1 :    out T;
                        A0 :    out T;
                        A  : in     T)
     with Global => null,
          Always_Terminates,
          Pre =>  (for all I in IndexN => A.C (I) >= 0 and A.C (I) < Q),
          Post => (for all I in IndexN => A1.C (I) >= 0 and A1.C (I) < (Q - 1) / (2 * Gamma2)) and
                  (for all I in IndexN => A0.C (I) >= -Gamma2 and A0.C (I) <= Gamma2);

end Poly;
