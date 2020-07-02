#if BYTECODE || NATiVE then
include Bigarray
#else

type c_layout
type int8_unsigned_elt

module Array1 = struct
  type ('a, 'b, 'c) t
end
#end
