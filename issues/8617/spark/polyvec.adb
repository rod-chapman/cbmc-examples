package body PolyVec
  with SPARK_Mode => On
is
   procedure Decompose (V1 :    out T;
                        V0 :    out T;
                        V  : in     T)
   is
   begin
      for K in IndexK loop
         Poly.Decompose (V1.Vec (K), V0.Vec (K), V.Vec (K));

         pragma Loop_Invariant (V1.Vec (0 .. K)'Initialized);
         pragma Loop_Invariant (V0.Vec (0 .. K)'Initialized);

         pragma Loop_Invariant (for all Z in IndexK range 0 .. K =>
                   (for all I in IndexN => V1.Vec (Z).C (I) >= 0 and V1.Vec (Z).C (I) < (Q - 1) / (2 * Gamma2)));

         pragma Loop_Invariant (for all Z in IndexK range 0 .. K =>
                   (for all I in IndexN => V0.Vec (Z).C (I) >= -Gamma2 and V0.Vec (Z).C (I) <= Gamma2));
      end loop;
   end Decompose;


end PolyVec;
