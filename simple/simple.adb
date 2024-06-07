package body Simple
  with SPARK_Mode => On
is
   function Average (A, B : in Integer_32) return Integer_32
   is
   begin
      return (A + B) / 2;
   end Average;
end Simple;
