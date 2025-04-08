with Poly; use Poly;
with Interfaces; use Interfaces;
package PolyVec
  with SPARK_Mode => On
is
   type K_Polys is array (IndexK) of Poly.T;

   type T is record
      Vec : K_Polys;
   end record;

   procedure Decompose (V1 :    out T;
                        V0 :    out T;
                        V  : in     T)
    with Global => null,
         Relaxed_Initialization => (V0, V1),
         Pre =>  (for all K in IndexK =>
                   (for all I in IndexN => V.Vec (K).C (I) >= 0 and V.Vec (K).C (I) < Q)),
         Post => (for all K in IndexK =>
                   (for all I in IndexN => V1.Vec (K).C (I) >= 0 and V1.Vec (K).C (I) < (Q - 1) / (2 * Gamma2))) and
                 (for all K in IndexK =>
                   (for all I in IndexN => V0.Vec (K).C (I) >= -Gamma2 and V0.Vec (K).C (I) <= Gamma2));

end PolyVec;
