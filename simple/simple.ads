with Interfaces; use Interfaces;
package Simple
  with SPARK_Mode => On
is
   function Average (A, B : in Integer_32) return Integer_32
     with Pre  => A >= 0 and B >= 0,
          Post => Average'Result = (A + B) / 2 and
                  Average'Result >= 0;

end Simple;
