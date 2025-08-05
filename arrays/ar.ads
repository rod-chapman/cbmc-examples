with Interfaces; use Interfaces;
package AR
  with SPARK_Mode => On
is
  type Index is range 0 .. 255;
  type Vector is array (Index) of Integer_32;
  type Matrix is array (Index) of Vector;

  procedure Inc_Vector (V : in out Vector)
    with Global => null,
         Pre  => (for all I in Index => V (I) < Integer_32'Last),
         Post => (for all I in Index => V (I) = V'Old (I) + 1);

  procedure Inc_Matrix (M : in out Matrix)
    with Global => null,
         Pre  => (for all I in Index => (for all J in Index => M (I)(J) < Integer_32'Last)),
         Post => (for all I in Index => (for all J in Index => M (I)(J) = M'Old (I)(J) + 1));

end AR;
