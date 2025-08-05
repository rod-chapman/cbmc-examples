package body AR
  with SPARK_Mode => On
is
  procedure Inc_Vector (V : in out Vector)
  is
  begin
     for I in Index loop
        V (I) := V (I) + 1;
        pragma Loop_Invariant (for all J in Index range 0 .. I => V (J) = V'Loop_Entry (J) + 1);
     end loop;
  end Inc_Vector;

  procedure Inc_Matrix (M : in out Matrix)
  is
  begin
    for I in Index loop
       Inc_Vector (M (I));
       pragma Loop_Invariant (for all J in Index range 0 .. I =>
                               (for all K in Index => M (J)(K) = M'Loop_Entry (J)(K) + 1));
    end loop;
  end Inc_Matrix;
end AR;
