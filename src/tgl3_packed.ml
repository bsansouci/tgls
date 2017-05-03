module Unsigned : sig 
#1 "unsigned.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** Types and operations for unsigned integers. *)

module type S = sig
  type t

  val add : t -> t -> t
  (** Addition. *)

  val sub : t -> t -> t
  (** Subtraction. *)

  val mul : t -> t -> t
  (** Multiplication. *)

  val div : t -> t -> t
  (** Division.  Raise {!Division_by_zero} if the second argument is zero. *)

  val rem : t -> t -> t
  (** Integer remainder.  Raise {!Division_by_zero} if the second argument is
      zero. *)

  val max_int : t
  (** The greatest representable integer. *)

  val logand : t -> t -> t
  (** Bitwise logical and. *)

  val logor : t -> t -> t
  (** Bitwise logical or. *)

  val logxor : t -> t -> t
  (** Bitwise logical exclusive or. *)

  val shift_left : t -> int -> t
  (** {!shift_left} [x] [y] shifts [x] to the left by [y] bits. *)

  val shift_right : t -> int -> t
  (** {!shift_right} [x] [y] shifts [x] to the right by [y] bits. *)

  val of_int : int -> t
  (** Convert the given int value to an unsigned integer. *)

  val to_int : t -> int
  (** Convert the given unsigned integer value to an int. *)

  val of_int64 : int64 -> t
  (** Convert the given int64 value to an unsigned integer. *)

  val to_int64 : t -> int64
  (** Convert the given unsigned integer value to an int64. *)

  val of_string : string -> t
  (** Convert the given string to an unsigned integer.  Raise {!Failure}
      ["int_of_string"] if the given string is not a valid representation of
      an unsigned integer. *)

  val to_string : t -> string
  (** Return the string representation of its argument. *)

  val zero : t
  (** The integer 0. *)

  val one : t
  (** The integer 1. *)

  val lognot : t -> t
  (** Bitwise logical negation. *)

  val succ : t -> t
  (** Successor. *)

  val pred : t -> t
  (** Predecessor. *)

  val compare : t -> t -> int
  (** The comparison function for unsigned integers, with the same
      specification as {!Pervasives.compare}. *)

  module Infix : sig
    val (+) : t -> t -> t
    (** Addition.  See {!add}. *)

    val (-) : t -> t -> t
    (** Subtraction.  See {!sub}.*)

    val ( * ) : t -> t -> t
    (** Multiplication.  See {!mul}.*)

    val (/) : t -> t -> t
    (** Division.  See {!div}.*)

    val (mod) : t -> t -> t
    (** Integer remainder.  See {!rem}. *)

    val (land) : t -> t -> t
    (** Bitwise logical and.  See {!logand}. *)

    val (lor) : t -> t -> t
    (** Bitwise logical or.  See {!logor}. *)

    val (lxor) : t -> t -> t
    (** Bitwise logical exclusive or.  See {!logxor}. *)

    val (lsl) : t -> int -> t
    (** [x lsl y] shifts [x] to the left by [y] bits.  See {!shift_left}. *)

    val (lsr) : t -> int -> t
    (** [x lsr y] shifts [x] to the right by [y] bits.  See {!shift_right}. *)
  end
(** Infix names for the unsigned integer operations. *)
end
(** Unsigned integer operations. *)

module UChar : S
(** Unsigned char type and operations. *)

module UInt8 : S
(** Unsigned 8-bit integer type and operations. *)

module UInt16 : S
(** Unsigned 16-bit integer type and operations. *)

module UInt32 : sig
  include S
  val of_int32 : int32 -> t
  val to_int32 : t -> int32
end
(** Unsigned 32-bit integer type and operations. *)

module UInt64 : sig
  include S
  val of_int64 : int64 -> t
  val to_int64 : t -> int64
end
(** Unsigned 64-bit integer type and operations. *)

module Size_t : S
(** The size_t unsigned integer type and operations. *)

module UShort : S
(** The unsigned short integer type and operations. *)

module UInt : S
(** The unsigned int type and operations. *)

module ULong : S
(** The unsigned long integer type and operations. *)

module ULLong : S
(** The unsigned long long integer type and operations. *)


type uchar = UChar.t
(** The unsigned char type. *)

type uint8 = UInt8.t
(** Unsigned 8-bit integer type. *)

type uint16 = UInt16.t
(** Unsigned 16-bit integer type. *)

type uint32 = UInt32.t
(** Unsigned 32-bit integer type. *)

type uint64 = UInt64.t
(** Unsigned 64-bit integer type. *)

type size_t = Size_t.t
(** The size_t unsigned integer type. *)

type ushort = UShort.t
(** The unsigned short unsigned integer type. *)

type uint = UInt.t
(** The unsigned int type. *)

type ulong = ULong.t
(** The unsigned long integer type. *)

type ullong = ULLong.t
(** The unsigned long long integer type. *)

end = struct
#1 "unsigned.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Boxed unsigned types *)
module type Basics = sig
  type t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val max_int : t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val shift_left : t -> int -> t
  val shift_right : t -> int -> t
  val of_int : int -> t
  val to_int : t -> int
  val of_int64 : int64 -> t
  val to_int64 : t -> int64
  val of_string : string -> t
  val to_string : t -> string
end


module type Extras = sig
  type t

  val zero : t
  val one : t
  val lognot : t -> t
  val succ : t -> t
  val pred : t -> t
  val compare : t -> t -> int
end


module type Infix = sig
  type t
  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  val (/) : t -> t -> t
  val (mod) : t -> t -> t
  val (land) : t -> t -> t
  val (lor) : t -> t -> t
  val (lxor) : t -> t -> t
  val (lsl) : t -> int -> t
  val (lsr) : t -> int -> t
end


module type S = sig
  include Basics
  include Extras with type t := t

  module Infix : Infix with type t := t
end


module MakeInfix (B : Basics) =
struct
  open B
  let (+) = add
  let (-) = sub
  let ( * ) = mul
  let (/) = div
  let (mod) = rem
  let (land) = logand
  let (lor) = logor
  let (lxor) = logxor
  let (lsl) = shift_left
  let (lsr) = shift_right
end


module Extras(Basics : Basics) : Extras with type t := Basics.t =
struct
  open Basics
  let zero = of_int 0
  let one = of_int 1
  let succ n = add n one
  let pred n = sub n one
  let lognot n = logxor n max_int
  let compare (x : t) (y : t) = Pervasives.compare x y
end


module UInt8 : S =
struct
  module B =
  struct
    (* Once 4.01 support is dropped all of these should be [@@inline] *)
    type t = int
    let max_int = 255
    let add : t -> t -> t = fun x y -> (x + y) land max_int
    let sub : t -> t -> t = fun x y -> (x - y) land max_int
    let mul : t -> t -> t = fun x y -> (x * y) land max_int
    let div : t -> t -> t = (/)
    let rem : t -> t -> t = (mod)
    let logand: t -> t -> t = (land)
    let logor: t -> t -> t = (lor)
    let logxor : t -> t -> t = (lxor)
    let shift_left : t -> int -> t = fun x y -> (x lsl y) land max_int
    let shift_right : t -> int -> t = (lsr)
    let of_int (x: int): t =
      (* For backwards compatibility, this wraps *)
      x land max_int
    external to_int : t -> int = "%identity"
    let of_int64 : int64 -> t = fun x -> of_int (Int64.to_int x)
    let to_int64 : t -> int64 = fun x -> Int64.of_int (to_int x)
    external of_string : string -> t = "ctypes_uint8_of_string"
    let to_string : t -> string = string_of_int
  end
  include B
  include Extras(B)
  module Infix = MakeInfix(B)
end


module UInt16 : S =
struct
  module B =
  struct
    (* Once 4.01 support is dropped all of these should be [@@inline] *)
    type t = int
    let max_int = 65535
    let add : t -> t -> t = fun x y -> (x + y) land max_int
    let sub : t -> t -> t = fun x y -> (x - y) land max_int
    let mul : t -> t -> t = fun x y -> (x * y) land max_int
    let div : t -> t -> t = (/)
    let rem : t -> t -> t = (mod)
    let logand: t -> t -> t = (land)
    let logor: t -> t -> t = (lor)
    let logxor : t -> t -> t = (lxor)
    let shift_left : t -> int -> t = fun x y -> (x lsl y) land max_int
    let shift_right : t -> int -> t = (lsr)
    let of_int (x: int): t =
      (* For backwards compatibility, this wraps *)
      x land max_int
    external to_int : t -> int = "%identity"
    let of_int64 : int64 -> t = fun x -> Int64.to_int x |> of_int
    let to_int64 : t -> int64 = fun x -> to_int x |> Int64.of_int
    external of_string : string -> t = "ctypes_uint16_of_string"
    let to_string : t -> string = string_of_int
  end
  include B
  include Extras(B)
  module Infix = MakeInfix(B)
end


module UInt32 : sig
  include S
  external of_int32 : int32 -> t = "ctypes_uint32_of_int32"
  external to_int32 : t -> int32 = "ctypes_int32_of_uint32"
end =
struct
  module B =
  struct
    type t
    external add : t -> t -> t = "ctypes_uint32_add"
    external sub : t -> t -> t = "ctypes_uint32_sub"
    external mul : t -> t -> t = "ctypes_uint32_mul"
    external div : t -> t -> t = "ctypes_uint32_div"
    external rem : t -> t -> t = "ctypes_uint32_rem"
    external logand : t -> t -> t = "ctypes_uint32_logand"
    external logor : t -> t -> t = "ctypes_uint32_logor"
    external logxor : t -> t -> t = "ctypes_uint32_logxor"
    external shift_left : t -> int -> t = "ctypes_uint32_shift_left"
    external shift_right : t -> int -> t = "ctypes_uint32_shift_right"
    external of_int : int -> t = "ctypes_uint32_of_int"
    external to_int : t -> int = "ctypes_uint32_to_int"
    external of_int64 : int64 -> t = "ctypes_uint32_of_int64"
    external to_int64 : t -> int64 = "ctypes_uint32_to_int64"
    external of_string : string -> t = "ctypes_uint32_of_string"
    external to_string : t -> string = "ctypes_uint32_to_string"
    external _max_int : unit -> t = "ctypes_uint32_max"
    let max_int = _max_int ()
  end
  include B
  include Extras(B)
  module Infix = MakeInfix(B)
  external of_int32 : int32 -> t = "ctypes_uint32_of_int32"
  external to_int32 : t -> int32 = "ctypes_int32_of_uint32"
end


module UInt64 : sig
  include S
  external of_int64 : int64 -> t = "ctypes_uint64_of_int64"
  external to_int64 : t -> int64 = "ctypes_uint64_to_int64"
end =
struct
  module B =
  struct
    type t
    external add : t -> t -> t = "ctypes_uint64_add"
    external sub : t -> t -> t = "ctypes_uint64_sub"
    external mul : t -> t -> t = "ctypes_uint64_mul"
    external div : t -> t -> t = "ctypes_uint64_div"
    external rem : t -> t -> t = "ctypes_uint64_rem"
    external logand : t -> t -> t = "ctypes_uint64_logand"
    external logor : t -> t -> t = "ctypes_uint64_logor"
    external logxor : t -> t -> t = "ctypes_uint64_logxor"
    external shift_left : t -> int -> t = "ctypes_uint64_shift_left"
    external shift_right : t -> int -> t = "ctypes_uint64_shift_right"
    external of_int : int -> t = "ctypes_uint64_of_int"
    external to_int : t -> int = "ctypes_uint64_to_int"
    external of_int64 : int64 -> t = "ctypes_uint64_of_int64"
    external to_int64 : t -> int64 = "ctypes_uint64_to_int64"
    external of_string : string -> t = "ctypes_uint64_of_string"
    external to_string : t -> string = "ctypes_uint64_to_string"
    external _max_int : unit -> t = "ctypes_uint64_max"
    let max_int = _max_int ()
  end
  include B
  include Extras(B)
  module Infix = MakeInfix(B)
end


let pick : size:int -> (module S) =
  fun ~size -> match size with
    | 1 -> (module UInt8)
    | 2 -> (module UInt16)
    | 4 -> (module UInt32)
    | 8 -> (module UInt64)
    | _ -> assert false

external size_t_size : unit -> int = "ctypes_size_t_size"
external ushort_size : unit -> int = "ctypes_ushort_size"
external uint_size : unit -> int = "ctypes_uint_size"
external ulong_size : unit -> int = "ctypes_ulong_size"
external ulonglong_size : unit -> int = "ctypes_ulonglong_size"

module Size_t : S = (val pick ~size:(size_t_size ()))
module UChar : S = UInt8
module UShort : S = (val pick ~size:(ushort_size ()))
module UInt : S = (val pick ~size:(uint_size ()))
module ULong : S = (val pick ~size:(ulong_size ()))
module ULLong : S = (val pick ~size:(ulonglong_size ()))

type uchar = UChar.t
type uint8 = UInt8.t
type uint16 = UInt16.t
type uint32 = UInt32.t
type uint64 = UInt64.t
type size_t = Size_t.t
type ushort = UShort.t
type uint = UInt.t
type ulong = ULong.t
type ullong = ULLong.t

end
module Signed : sig 
#1 "signed.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** Types and operations for signed integers. *)

module type S = sig
  include Unsigned.S

  val neg : t -> t
  (** Unary negation. *)

  val abs : t -> t
  (** Return the absolute value of its argument. *)

  val minus_one : t
  (** The value -1 *)

  val min_int : t
  (** The smallest representable integer. *)

  val shift_right_logical : t -> int -> t
  (** {!shift_right_logical} [x] [y] shifts [x] to the right by [y] bits.  See
      {!Int32.shift_right_logical}. *)

  val of_nativeint : nativeint -> t
  (** Convert the given nativeint value to a signed integer. *)

  val to_nativeint : t -> nativeint
  (** Convert the given signed integer to a nativeint value. *)

  val of_int64 : int64 -> t
  (** Convert the given int64 value to a signed integer. *)

  val to_int64 : t -> int64
  (** Convert the given signed integer to an int64 value. *)
end
(** Signed integer operations *)

module Int : S with type t = int
(** Signed integer type and operations. *)

module Int32 : S with type t = int32
(** Signed 32-bit integer type and operations. *)

module Int64 : S with type t = int64
(** Signed 64-bit integer type and operations. *)

module SInt : S
(** C's signed integer type and operations. *)

module Long : S
(** The signed long integer type and operations. *)

module LLong : S
(** The signed long long integer type and operations. *)

type sint = SInt.t
(** C's signed integer type. *)

type long = Long.t
(** The signed long integer type. *)

type llong = LLong.t
(** The signed long long integer type. *)

end = struct
#1 "signed.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

module type S = sig
  include Unsigned.S

  val neg : t -> t
  val abs : t -> t
  val minus_one : t
  val min_int : t
  val shift_right_logical : t -> int -> t
  val of_nativeint : nativeint -> t
  val to_nativeint : t -> nativeint
  val of_int64 : int64 -> t
  val to_int64 : t -> int64
end

module type Basics = sig
  type t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val shift_left : t -> int -> t
  val shift_right : t -> int -> t
  val shift_right_logical : t -> int -> t
end

module MakeInfix(S : Basics) =
struct
  open S
  let (+) = add
  let (-) = sub
  let ( * ) = mul
  let (/) = div
  let (mod) = rem
  let (land) = logand
  let (lor) = logor
  let (lxor) = logxor
  let (lsl) = shift_left
  let (lsr) = shift_right_logical
  let (asr) = shift_right
end

module Int =
struct
  module Basics =
  struct
    type t = int
    let add = ( + )
    let sub = ( - )
    let mul = ( * )
    let div = ( / )
    let rem = ( mod )
    let max_int = Pervasives.max_int
    let min_int = Pervasives.min_int
    let logand = ( land )
    let logor = ( lor )
    let logxor = ( lxor )
    let shift_left = ( lsl )
    let shift_right = ( asr )
    let shift_right_logical = ( lsr )
    let of_int x = x
    let to_int x = x
    let of_string = int_of_string
    let to_string = string_of_int
    let zero = 0
    let one = 1
    let minus_one = -1
    let lognot = lnot
    let succ = Pervasives.succ
    let pred = Pervasives.pred
    let compare = Pervasives.compare
  end
  include Basics
  module Infix = MakeInfix(Basics)
  let to_int64 = Int64.of_int
  let of_int64 = Int64.to_int
  let to_nativeint = Nativeint.of_int
  let of_nativeint = Nativeint.to_int
  let abs = Pervasives.abs
  let neg x = -x
end

module Int32 = 
struct
  include Int32
  module Infix = MakeInfix(Int32)
  let of_nativeint = Nativeint.to_int32
  let to_nativeint = Nativeint.of_int32
  let of_int64 = Int64.to_int32
  let to_int64 = Int64.of_int32
end

module Int64 = 
struct
  include Int64
  module Infix = MakeInfix(Int64)
  let of_int64 x = x
  let to_int64 x = x
end

(* C guarantees that sizeof(t) == sizeof(unsigned t) *)
external int_size : unit -> int = "ctypes_uint_size"
external long_size : unit -> int = "ctypes_ulong_size"
external llong_size : unit -> int = "ctypes_ulonglong_size"

let pick : size:int -> (module S) =
  fun ~size -> match size with
    | 4 -> (module Int32)
    | 8 -> (module Int64)
    | _ -> assert false

module SInt = (val pick ~size:(int_size ()))
module Long = (val pick ~size:(long_size ()))
module LLong = (val pick ~size:(llong_size ()))

type sint = SInt.t
type long = Long.t
type llong = LLong.t

end
module Ctypes_primitive_types : sig 
#1 "ctypes_primitive_types.mli"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Representation of primitive C types.

   Internal representation, not for public use. *)

open Unsigned
open Signed

type _ prim =
 | Char : char prim
 | Schar : int prim
 | Uchar : uchar prim
 | Bool : bool prim
 | Short : int prim
 | Int : int prim
 | Long : long prim
 | Llong : llong prim
 | Ushort : ushort prim
 | Sint : sint prim
 | Uint : uint prim
 | Ulong : ulong prim
 | Ullong : ullong prim
 | Size_t : size_t prim
 | Int8_t : int prim
 | Int16_t : int prim
 | Int32_t : int32 prim
 | Int64_t : int64 prim
 | Uint8_t : uint8 prim
 | Uint16_t : uint16 prim
 | Uint32_t : uint32 prim
 | Uint64_t : uint64 prim
 | Camlint : int prim
 | Nativeint : nativeint prim
 | Float : float prim
 | Double : float prim
 | Complex32 : Complex.t prim
 | Complex64 : Complex.t prim

type _ ml_prim = 
  | ML_char :  char ml_prim
  | ML_complex :  Complex.t ml_prim
  | ML_float :  float ml_prim
  | ML_int :  int ml_prim
  | ML_int32 :  int32 ml_prim
  | ML_int64 :  int64 ml_prim
  | ML_llong :  llong ml_prim
  | ML_long :  long ml_prim
  | ML_sint : sint ml_prim
  | ML_nativeint :  nativeint ml_prim
  | ML_size_t :  size_t ml_prim
  | ML_uchar :  uchar ml_prim
  | ML_bool :  bool ml_prim
  | ML_uint :  uint ml_prim
  | ML_uint16 :  uint16 ml_prim
  | ML_uint32 :  uint32 ml_prim
  | ML_uint64 :  uint64 ml_prim
  | ML_uint8 :  uint8 ml_prim
  | ML_ullong :  ullong ml_prim
  | ML_ulong :  ulong ml_prim
  | ML_ushort :  ushort ml_prim

val ml_prim : 'a prim -> 'a ml_prim

end = struct
#1 "ctypes_primitive_types.ml"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Unsigned
open Signed

type _ prim =
 | Char : char prim
 | Schar : int prim
 | Uchar : uchar prim
 | Bool : bool prim
 | Short : int prim
 | Int : int prim
 | Long : long prim
 | Llong : llong prim
 | Ushort : ushort prim
 | Sint : sint prim
 | Uint : uint prim
 | Ulong : ulong prim
 | Ullong : ullong prim
 | Size_t : size_t prim
 | Int8_t : int prim
 | Int16_t : int prim
 | Int32_t : int32 prim
 | Int64_t : int64 prim
 | Uint8_t : uint8 prim
 | Uint16_t : uint16 prim
 | Uint32_t : uint32 prim
 | Uint64_t : uint64 prim
 | Camlint : int prim
 | Nativeint : nativeint prim
 | Float : float prim
 | Double : float prim
 | Complex32 : Complex.t prim
 | Complex64 : Complex.t prim

type _ ml_prim = 
  | ML_char :  char ml_prim
  | ML_complex :  Complex.t ml_prim
  | ML_float :  float ml_prim
  | ML_int :  int ml_prim
  | ML_int32 :  int32 ml_prim
  | ML_int64 :  int64 ml_prim
  | ML_llong :  llong ml_prim
  | ML_long :  long ml_prim
  | ML_sint : sint ml_prim
  | ML_nativeint :  nativeint ml_prim
  | ML_size_t :  size_t ml_prim
  | ML_uchar :  uchar ml_prim
  | ML_bool :  bool ml_prim
  | ML_uint :  uint ml_prim
  | ML_uint16 :  uint16 ml_prim
  | ML_uint32 :  uint32 ml_prim
  | ML_uint64 :  uint64 ml_prim
  | ML_uint8 :  uint8 ml_prim
  | ML_ullong :  ullong ml_prim
  | ML_ulong :  ulong ml_prim
  | ML_ushort :  ushort ml_prim

let ml_prim : type a. a prim -> a ml_prim = function
  | Char -> ML_char
  | Schar -> ML_int
  | Uchar -> ML_uchar
  | Bool -> ML_bool
  | Short -> ML_int
  | Int -> ML_int
  | Long -> ML_long
  | Llong -> ML_llong
  | Ushort -> ML_ushort
  | Sint -> ML_sint
  | Uint -> ML_uint
  | Ulong -> ML_ulong
  | Ullong -> ML_ullong
  | Size_t -> ML_size_t
  | Int8_t -> ML_int
  | Int16_t -> ML_int
  | Int32_t -> ML_int32
  | Int64_t -> ML_int64
  | Uint8_t -> ML_uint8
  | Uint16_t -> ML_uint16
  | Uint32_t -> ML_uint32
  | Uint64_t -> ML_uint64
  | Camlint -> ML_int
  | Nativeint -> ML_nativeint
  | Float -> ML_float
  | Double -> ML_float
  | Complex32 -> ML_complex
  | Complex64 -> ML_complex

end
module Ctypes_ptr
= struct
#1 "ctypes_ptr.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Boxed pointers to C memory locations . *)

module Raw :
sig
  include Signed.S
  val null : t
end =
struct
  include Nativeint

  module Infix =
  struct
    let (+) = add
    let (-) = sub
    let ( * ) = mul
    let (/) = div
    let (mod) = rem
    let (land) = logand
    let (lor) = logor
    let (lxor) = logxor
    let (lsl) = shift_left
    let (lsr) = shift_right_logical
  end

  let of_nativeint x = x
  let to_nativeint x = x
  let of_int64 = Int64.to_nativeint
  let to_int64  = Int64.of_nativeint

  let null = zero
end

type voidp = Raw.t

module Fat :
sig
  (** A fat pointer, which holds a reference to the reference type, the C memory
      location, and an OCaml object. *)
  type _ t

  (** [make ?managed ~reftyp raw] builds a fat pointer from the reference
      type [reftyp], the C memory location [raw], and (optionally) an OCaml
      value, [managed].  The [managed] argument may be used to manage the
      lifetime of the C object; a typical use it to attach a finaliser to
      [managed] which releases the memory associated with the C object whose
      address is stored in [raw_ptr]. *)
  val make : ?managed:_ -> reftyp:'typ -> voidp -> 'typ t

  val is_null : _ t -> bool

  val reftype : 'typ t -> 'typ

  val managed : _ t -> Obj.t option

  val coerce : _ t -> 'typ -> 'typ t

  (** Return the raw pointer address.  The function is unsafe in the sense
      that it dissociates the address from the value which manages the memory,
      which may trigger associated finalisers, invalidating the address. *)
  val unsafe_raw_addr : _ t -> voidp

  val add_bytes : 'typ t -> int -> 'typ t

  val compare : 'typ t -> 'typ t -> int

  val diff_bytes : 'typ t -> 'typ t -> int
end =
struct
  type 'typ t =
    { reftyp  : 'typ;
      raw     : voidp;
      managed : Obj.t option; }

  let make ?managed ~reftyp raw = match managed with
    | None   -> { reftyp; raw; managed = None }
    | Some v -> { reftyp; raw; managed = Some (Obj.repr v) }

  let is_null { raw } = Raw.(compare zero) raw = 0

  let reftype { reftyp } = reftyp

  let managed { managed } = managed

  let coerce p reftyp = { p with reftyp }

  let unsafe_raw_addr { raw } = raw

  let add_bytes p bytes = { p with raw = Raw.(add p.raw (of_int bytes)) }

  let compare l r = Raw.compare l.raw r.raw

  let diff_bytes l r = Raw.(to_int (sub r.raw l.raw))
end

end
module Ctypes_bigarray_stubs
= struct
#1 "ctypes_bigarray_stubs.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

type _ kind =
    Kind_float32 : float kind
  | Kind_float64 : float kind
  | Kind_int8_signed : int kind
  | Kind_int8_unsigned : int kind
  | Kind_int16_signed : int kind
  | Kind_int16_unsigned : int kind
  | Kind_int32 : int32 kind
  | Kind_int64 : int64 kind
  | Kind_int : int kind
  | Kind_nativeint : nativeint kind
  | Kind_complex32 : Complex.t kind
  | Kind_complex64 : Complex.t kind
  | Kind_char : char kind

external kind : ('a, 'b) Bigarray.kind -> 'a kind
  (* Bigarray.kind is simply an int whose values are consecutively numbered
     starting from zero, so we can directly transform its values to a variant
     with appropriately-ordered constructors.

     In OCaml <= 4.01.0, Bigarray.char and Bigarray.int8_unsigned are
     indistinguishable, so the 'kind' function will never return Kind_char.
     OCaml 4.02.0 gives the types distinct representations. *)
  = "%identity"

external address : 'b -> Ctypes_ptr.voidp
  = "ctypes_bigarray_address"

external view : 'a kind -> dims:int array -> _ Ctypes_ptr.Fat.t ->
  ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t
  = "ctypes_bigarray_view"

external view1 : 'a kind -> dims:int array -> _ Ctypes_ptr.Fat.t ->
  ('a, 'b, Bigarray.c_layout) Bigarray.Array1.t
  = "ctypes_bigarray_view"

external view2 : 'a kind -> dims:int array -> _ Ctypes_ptr.Fat.t ->
  ('a, 'b, Bigarray.c_layout) Bigarray.Array2.t
  = "ctypes_bigarray_view"

external view3 : 'a kind -> dims:int array -> _ Ctypes_ptr.Fat.t ->
  ('a, 'b, Bigarray.c_layout) Bigarray.Array3.t
  = "ctypes_bigarray_view"

end
module Ctypes_memory_stubs
= struct
#1 "ctypes_memory_stubs.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Stubs for reading and writing memory. *)

open Ctypes_ptr

(* A reference, managed by the garbage collector, to a region of memory in the
   C heap. *)
type managed_buffer

(* Allocate a region of stable, zeroed memory managed by a custom block. *)
external allocate : int -> int -> managed_buffer
  = "ctypes_allocate"

(* Obtain the address of the managed block. *)
external block_address : managed_buffer -> voidp
  = "ctypes_block_address"

(* Read a C value from a block of memory *)
external read : 'a Ctypes_primitive_types.prim -> _ Fat.t -> 'a
  = "ctypes_read"

(* Write a C value to a block of memory *)
external write : 'a Ctypes_primitive_types.prim -> 'a -> _ Fat.t -> unit
  = "ctypes_write"

module Pointer =
struct
  external read : _ Fat.t -> voidp
    = "ctypes_read_pointer"

  external write : _ Fat.t -> _ Fat.t -> unit
  = "ctypes_write_pointer"
end

(* Copy [size] bytes from [src] to [dst]. *)
external memcpy : dst:_ Fat.t -> src:_ Fat.t -> size:int -> unit
  = "ctypes_memcpy"

(* Read a fixed length OCaml string from memory *)
external string_of_array : _ Fat.t -> len:int -> string
  = "ctypes_string_of_array"

(* Do nothing, concealing from the optimizer that nothing is being done. *)
external use_value : 'a -> unit
  = "ctypes_use"

end
module Ctypes_path : sig 
#1 "ctypes_path.mli"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Value paths (long identifiers) *)

type path

val path_of_string : string -> path
val format_path : Format.formatter -> path -> unit

end = struct
#1 "ctypes_path.ml"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Paths (long identifiers) *)

type path = string list

let is_uident s =
  Str.(string_match (regexp "[A-Z][a-zA-Z0-9_]*") s 0);;

let is_ident s =
  Str.(string_match (regexp "[A-Za-z_][a-zA-Z0-9_]*") s 0);;

let rec is_valid_path = function
  | [] -> false
  | [l] -> is_ident l
  | u :: p -> is_uident u && is_valid_path p

let path_of_string s = 
  let p = Str.(split (regexp_string ".") s) in
  if is_valid_path p then p
  else invalid_arg "Ctypes_ident.path_of_string"

let format_path fmt p =
  Format.pp_print_string fmt (String.concat "." p)

end
module Ctypes_primitives
= struct
#1 "ctypes_primitives.ml"
(*
 * Copyright (c) 2016 whitequark
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_primitive_types
let sizeof : type a. a prim -> int = function
 | Char -> 1
 | Schar -> 1
 | Uchar -> 1
 | Bool -> 1
 | Short -> 2
 | Int -> 4
 | Long -> 8
 | Llong -> 8
 | Ushort -> 2
 | Sint -> 4
 | Uint -> 4
 | Ulong -> 8
 | Ullong -> 8
 | Size_t -> 8
 | Int8_t -> 1
 | Int16_t -> 2
 | Int32_t -> 4
 | Int64_t -> 8
 | Uint8_t -> 1
 | Uint16_t -> 2
 | Uint32_t -> 4
 | Uint64_t -> 8
 | Float -> 4
 | Double -> 8
 | Complex32 -> 8
 | Complex64 -> 16
 | Nativeint -> 8
 | Camlint -> 8
let alignment : type a. a prim -> int = function
 | Char -> 1
 | Schar -> 1
 | Uchar -> 1
 | Bool -> 1
 | Short -> 2
 | Int -> 4
 | Long -> 8
 | Llong -> 8
 | Ushort -> 2
 | Sint -> 4
 | Uint -> 4
 | Ulong -> 8
 | Ullong -> 8
 | Size_t -> 8
 | Int8_t -> 1
 | Int16_t -> 2
 | Int32_t -> 4
 | Int64_t -> 8
 | Uint8_t -> 1
 | Uint16_t -> 2
 | Uint32_t -> 4
 | Uint64_t -> 8
 | Float -> 4
 | Double -> 8
 | Complex32 -> 4
 | Complex64 -> 8
 | Nativeint -> 8
 | Camlint -> 8
let name : type a. a prim -> string = function
 | Char -> "char"
 | Schar -> "signed char"
 | Uchar -> "unsigned char"
 | Bool -> "_Bool"
 | Short -> "short"
 | Int -> "int"
 | Long -> "long"
 | Llong -> "long long"
 | Ushort -> "unsigned short"
 | Sint -> "int"
 | Uint -> "unsigned int"
 | Ulong -> "unsigned long"
 | Ullong -> "unsigned long long"
 | Size_t -> "size_t"
 | Int8_t -> "int8_t"
 | Int16_t -> "int16_t"
 | Int32_t -> "int32_t"
 | Int64_t -> "int64_t"
 | Uint8_t -> "uint8_t"
 | Uint16_t -> "uint16_t"
 | Uint32_t -> "uint32_t"
 | Uint64_t -> "uint64_t"
 | Float -> "float"
 | Double -> "double"
 | Complex32 -> "float _Complex"
 | Complex64 -> "double _Complex"
 | Nativeint -> "intnat"
 | Camlint -> "camlint"
let format_string : type a. a prim -> string option = function
 | Char -> Some "%d"
 | Schar -> Some "%d"
 | Uchar -> Some "%d"
 | Bool -> Some "%d"
 | Short -> Some "%hd"
 | Int -> Some "%d"
 | Long -> Some "%ld"
 | Llong -> Some "%lld"
 | Ushort -> Some "%hu"
 | Sint -> Some "%d"
 | Uint -> Some "%u"
 | Ulong -> Some "%lu"
 | Ullong -> Some "%llu"
 | Size_t -> Some "%zu"
 | Int8_t -> Some "%hhd"
 | Int16_t -> Some "%hd"
 | Int32_t -> Some "%d"
 | Int64_t -> Some "%lld"
 | Uint8_t -> Some "%hhu"
 | Uint16_t -> Some "%hu"
 | Uint32_t -> Some "%u"
 | Uint64_t -> Some "%llu"
 | Float -> Some "%.12g"
 | Double -> Some "%.12g"
 | Complex32 -> None
 | Complex64 -> None
 | Nativeint -> Some "%ld"
 | Camlint -> Some "%ld"
let pointer_size = 8
let pointer_alignment = 8

end
module Ctypes_bigarray : sig 
#1 "ctypes_bigarray.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** {2 Types *)

type ('a, 'b) t
(** The type of bigarray values of particular sizes.  A value of type
    [(a, b) t] can be used to read and write values of type [b].  *)

(** {3 Type constructors *)

val bigarray : int array -> ('a, 'b) Bigarray.kind ->
  ('a, ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t) t
(** Create a {!t} value for the {!Bigarray.Genarray.t} type. *)

val bigarray1 : int -> ('a, 'b) Bigarray.kind ->
  ('a, ('a, 'b, Bigarray.c_layout) Bigarray.Array1.t) t
(** Create a {!t} value for the {!Bigarray.Array1.t} type. *)

val bigarray2 : int -> int -> ('a, 'b) Bigarray.kind ->
  ('a, ('a, 'b, Bigarray.c_layout) Bigarray.Array2.t) t
(** Create a {!t} value for the {!Bigarray.Array2.t} type. *)

val bigarray3 : int -> int -> int -> ('a, 'b) Bigarray.kind ->
  ('a, ('a, 'b, Bigarray.c_layout) Bigarray.Array3.t) t
(** Create a {!t} value for the {!Bigarray.Array3.t} type. *)

val prim_of_kind : ('a, _) Bigarray.kind -> 'a Ctypes_primitive_types.prim
(** Create a {!Ctypes_ptr.Types.ctype} for a {!Bigarray.kind}. *)

(** {3 Type eliminators *)

val sizeof : (_, _) t -> int
(** Compute the size of a bigarray type. *)

val alignment : (_, _) t -> int
(** Compute the alignment of a bigarray type. *)

val element_type : ('a, _) t -> 'a Ctypes_primitive_types.prim
(** Compute the element type of a bigarray type. *)

val dimensions : (_, _) t -> int array
(** Compute the dimensions of a bigarray type. *)

val type_expression : ('a, 'b) t -> ([> `Appl of Ctypes_path.path * 'c list
                                     |  `Ident of Ctypes_path.path ] as 'c)
(** Compute a type expression that denotes a bigarray type. *)

(** {2 Values *)

val unsafe_address : 'a -> Ctypes_ptr.voidp
(** Return the address of a bigarray value.  This function is unsafe because
    it dissociates the raw address of the C array from the OCaml object that
    manages the lifetime of the array.  If the caller does not hold a
    reference to the OCaml object then the array might be freed, invalidating
    the address. *)

val view : (_, 'a) t -> _ Ctypes_ptr.Fat.t -> 'a
(** [view b ptr] creates a bigarray view onto existing memory.

    If [ptr] references an OCaml object then [view] will ensure that
    that object is not collected before the bigarray returned by
    [view]. *)

end = struct
#1 "ctypes_bigarray.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_bigarray_stubs

let prim_of_kind : type a. a kind -> a Ctypes_primitive_types.prim
  = let open Ctypes_primitive_types in function
    Kind_float32 -> Float
  | Kind_float64 -> Double
  | Kind_int8_signed -> Int8_t
  | Kind_int8_unsigned -> Int8_t
  | Kind_int16_signed -> Int16_t
  | Kind_int16_unsigned -> Int16_t
  | Kind_int32 -> Int32_t
  | Kind_int64 -> Int64_t
  | Kind_int -> Camlint
  | Kind_nativeint -> Nativeint
  | Kind_complex32 -> Complex32
  | Kind_complex64 -> Complex64
  | Kind_char -> Char

let bigarray_kind_sizeof k = Ctypes_primitives.sizeof (prim_of_kind k)

let bigarray_kind_alignment k = Ctypes_primitives.alignment (prim_of_kind k)

type (_, _) dims = 
| DimsGen : int array -> ('a, ('a, _, Bigarray.c_layout) Bigarray.Genarray.t) dims
| Dims1 : int -> ('a, ('a, _, Bigarray.c_layout) Bigarray.Array1.t) dims
| Dims2 : int * int -> ('a, ('a, _, Bigarray.c_layout) Bigarray.Array2.t) dims
| Dims3 : int * int * int -> ('a, ('a, _, Bigarray.c_layout) Bigarray.Array3.t) dims

type ('a, 'b) t = ('a, 'b) dims * 'a kind

let elements : type a b. (b, a) dims -> int = function
  | DimsGen ds -> Array.fold_left ( * ) 1 ds
  | Dims1 d -> d
  | Dims2 (d1, d2) -> d1 * d2
  | Dims3 (d1, d2, d3) -> d1 * d2 * d3

let element_type (_, k) = prim_of_kind k

let dimensions : type a b. (b, a) t -> int array = function
| DimsGen dims, _ -> dims
| Dims1 x, _ -> [| x |]
| Dims2 (x, y), _ -> [| x; y |]
| Dims3 (x, y, z), _ -> [| x; y; z |]

let sizeof (d, k) = elements d * bigarray_kind_sizeof k

let alignment (d, k) = bigarray_kind_alignment k

let bigarray ds k = (DimsGen ds, kind k)
let bigarray1 d k = (Dims1 d, kind k)
let bigarray2 d1 d2 k = (Dims2 (d1, d2), kind k)
let bigarray3 d1 d2 d3 k = (Dims3 (d1, d2, d3), kind k)

let path_of_string = Ctypes_path.path_of_string
let type_name : type a b. (b, a) dims -> Ctypes_path.path = function
  | DimsGen _ -> path_of_string "Bigarray.Genarray.t"
  | Dims1 _ -> path_of_string "Bigarray.Array1.t"
  | Dims2 _ -> path_of_string "Bigarray.Array2.t"
  | Dims3 _ -> path_of_string "Bigarray.Array3.t"

let kind_type_names : type a. a kind -> _ = function
  | Kind_float32 ->
    (`Ident (path_of_string "float"),
     `Ident (path_of_string "Bigarray.float32_elt"))
  | Kind_float64 ->
    (`Ident (path_of_string "float"),
     `Ident (path_of_string "Bigarray.float64_elt"))
  | Kind_int8_signed ->
    (`Ident (path_of_string "int"),
     `Ident (path_of_string "Bigarray.int8_signed_elt"))
  | Kind_int8_unsigned ->
    (`Ident (path_of_string "int"),
     `Ident (path_of_string "Bigarray.int8_unsigned_elt"))
  | Kind_int16_signed ->
    (`Ident (path_of_string "int"),
     `Ident (path_of_string "Bigarray.int16_signed_elt"))
  | Kind_int16_unsigned ->
    (`Ident (path_of_string "int"),
     `Ident (path_of_string "Bigarray.int16_unsigned_elt"))
  | Kind_int32 ->
    (`Ident (path_of_string "int32"),
     `Ident (path_of_string "Bigarray.int32_elt"))
  | Kind_int64 ->
    (`Ident (path_of_string "int64"),
     `Ident (path_of_string "Bigarray.int64_elt"))
  | Kind_int ->
    (`Ident (path_of_string "int"),
     `Ident (path_of_string "Bigarray.int_elt"))
  | Kind_nativeint ->
    (`Ident (path_of_string "nativeint"),
     `Ident (path_of_string "Bigarray.nativeint_elt"))
  | Kind_complex32 ->
    (`Ident (path_of_string "Complex.t"),
     `Ident (path_of_string "Bigarray.complex32_elt"))
  | Kind_complex64 ->
    (`Ident (path_of_string "Complex.t"),
     `Ident (path_of_string "Bigarray.complex64_elt"))
  | Kind_char ->
    (`Ident (path_of_string "char"),
     `Ident (path_of_string "Bigarray.int8_unsigned_elt"))

let type_expression : type a b. (a, b) t -> _ =
  fun (t, ck) ->
  begin
    let a, b = kind_type_names ck in
    let layout = `Ident (path_of_string "Bigarray.c_layout") in
    (`Appl (type_name t, [a; b; layout])
        : [> `Ident of Ctypes_path.path
          | `Appl of Ctypes_path.path * 'a list ] as 'a)
  end

let prim_of_kind k = prim_of_kind (kind k)

let unsafe_address b = Ctypes_bigarray_stubs.address b

let view : type a b. (a, b) t -> _ Ctypes_ptr.Fat.t -> b =
  let open Ctypes_bigarray_stubs in
  fun (dims, kind) ptr -> let ba : b = match dims with
  | DimsGen ds -> view kind ~dims:ds ptr
  | Dims1 d -> view1 kind ~dims:[| d |] ptr
  | Dims2 (d1, d2) -> view2 kind ~dims:[| d1; d2 |] ptr
  | Dims3 (d1, d2, d3) -> view3 kind ~dims:[| d1; d2; d3 |] ptr in
  match Ctypes_ptr.Fat.managed ptr with
  | None -> ba
  | Some src -> Gc.finalise (fun _ -> Ctypes_memory_stubs.use_value src) ba; ba

end
module Ctypes_static : sig 
#1 "ctypes_static.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* C type construction.  Internal representation, not for public use. *)

type abstract_type = {
  aname : string;
  asize : int;
  aalignment : int;
}

type _ ocaml_type =
  String     : string ocaml_type
| Bytes      : Bytes.t ocaml_type
| FloatArray : float array ocaml_type

type incomplete_size = { mutable isize: int }

type structured_spec = { size: int; align: int; }

type 'a structspec =
    Incomplete of incomplete_size
  | Complete of structured_spec

type _ typ =
    Void            :                       unit typ
  | Primitive       : 'a Ctypes_primitive_types.prim -> 'a typ
  | Pointer         : 'a typ             -> 'a ptr typ
  | Funptr          : 'a fn              -> 'a static_funptr typ
  | Struct          : 'a structure_type  -> 'a structure typ
  | Union           : 'a union_type      -> 'a union typ
  | Abstract        : abstract_type      -> 'a abstract typ
  | View            : ('a, 'b) view      -> 'a typ
  | Array           : 'a typ * int       -> 'a carray typ
  | Bigarray        : (_, 'a) Ctypes_bigarray.t
                                         -> 'a typ
  | OCaml           : 'a ocaml_type      -> 'a ocaml typ
and 'a carray = { astart : 'a ptr; alength : int }
and ('a, 'kind) structured = { structured : ('a, 'kind) structured ptr }
and 'a union = ('a, [`Union]) structured
and 'a structure = ('a, [`Struct]) structured
and 'a abstract = ('a, [`Abstract]) structured
and (_, _) pointer =
  CPointer : 'a typ Ctypes_ptr.Fat.t -> ('a, [`C]) pointer
| OCamlRef : int * 'a * 'a ocaml_type -> ('a, [`OCaml]) pointer
and 'a ptr = ('a, [`C]) pointer
and 'a ocaml = ('a, [`OCaml]) pointer
and 'a static_funptr = Static_funptr of 'a fn Ctypes_ptr.Fat.t
and ('a, 'b) view = {
  read : 'b -> 'a;
  write : 'a -> 'b;
  format_typ: ((Format.formatter -> unit) -> Format.formatter -> unit) option;
  format: (Format.formatter -> 'a -> unit) option;
  ty: 'b typ;
}
and ('a, 's) field = {
  ftype: 'a typ;
  foffset: int;
  fname: string;
}
and 'a structure_type = {
  tag: string;
  mutable spec: 'a structspec;
  mutable fields : 'a structure boxed_field list;
}
and 'a union_type = {
  utag: string;
  mutable uspec: structured_spec option;
  mutable ufields : 'a union boxed_field list;
}
and 's boxed_field = BoxedField : ('a, 's) field -> 's boxed_field
and _ fn =
  | Returns  : 'a typ   -> 'a fn
  | Function : 'a typ * 'b fn  -> ('a -> 'b) fn

type _ bigarray_class =
  Genarray :
  < element: 'a;
    dims: int array;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t;
    carray: 'a carray > bigarray_class
| Array1 :
  < element: 'a;
    dims: int;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array1.t;
    carray: 'a carray > bigarray_class
| Array2 :
  < element: 'a;
    dims: int * int;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array2.t;
    carray: 'a carray carray > bigarray_class
| Array3 :
  < element: 'a;
    dims: int * int * int;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array3.t;
    carray: 'a carray carray carray > bigarray_class

type boxed_typ = BoxedType : 'a typ -> boxed_typ

val sizeof : 'a typ -> int
val alignment : 'a typ -> int
val passable : 'a typ -> bool
val ocaml_value : 'a typ -> bool
val has_ocaml_argument : 'a fn -> bool

val void : unit typ
val char : char typ
val schar : int typ
val float : float typ
val double : float typ
val complex32 : Complex.t typ
val complex64 : Complex.t typ
val short : int typ
val int : int typ
val sint : Signed.sint typ
val long : Signed.long typ
val llong : Signed.llong typ
val nativeint : nativeint typ
val int8_t : int typ
val int16_t : int typ
val int32_t : Signed.Int32.t typ
val int64_t : Signed.Int64.t typ
val camlint : int typ
val uchar : Unsigned.uchar typ
val bool : bool typ
val uint8_t : Unsigned.UInt8.t typ
val uint16_t : Unsigned.UInt16.t typ
val uint32_t : Unsigned.UInt32.t typ
val uint64_t : Unsigned.UInt64.t typ
val size_t : Unsigned.size_t typ
val ushort : Unsigned.ushort typ
val uint : Unsigned.uint typ
val ulong : Unsigned.ulong typ
val ullong : Unsigned.ullong typ
val array : int -> 'a typ -> 'a carray typ
val ocaml_string : string ocaml typ
val ocaml_bytes : Bytes.t ocaml typ
val ocaml_float_array : float array ocaml typ
val ptr : 'a typ -> 'a ptr typ
val ( @-> ) : 'a typ -> 'b fn -> ('a -> 'b) fn
val abstract : name:string -> size:int -> alignment:int -> 'a abstract typ
val view : ?format_typ:((Format.formatter -> unit) ->
                        Format.formatter -> unit) ->
           ?format: (Format.formatter -> 'b -> unit) ->
           read:('a -> 'b) -> write:('b -> 'a) -> 'a typ -> 'b typ
val typedef: 'a typ -> string -> 'a typ
val bigarray : < ba_repr : 'c;
                 bigarray : 'd;
                 carray : 'e;
                 dims : 'b;
                 element : 'a > bigarray_class ->
               'b -> ('a, 'c) Bigarray.kind -> 'd typ
val returning : 'a typ -> 'a fn
val static_funptr : 'a fn -> 'a static_funptr typ
val structure : string -> 'a structure typ
val union : string -> 'a union typ
val offsetof : ('a, 'b) field -> int
val field_type : ('a, 'b) field -> 'a typ
val field_name : ('a, 'b) field -> string

exception IncompleteType
exception ModifyingSealedType of string
exception Unsupported of string

val unsupported : ('a, unit, string, _) format4 -> 'a

(* This corresponds to the enum in ctypes_primitives.h *)
type arithmetic =
    Int8
  | Int16
  | Int32
  | Int64
  | Uint8
  | Uint16
  | Uint32
  | Uint64
  | Float
  | Double

end = struct
#1 "ctypes_static.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* C type construction *)

exception IncompleteType
exception ModifyingSealedType of string
exception Unsupported of string

let unsupported fmt = Printf.ksprintf (fun s -> raise (Unsupported s)) fmt

type incomplete_size = { mutable isize: int }

type structured_spec = { size: int; align: int; }

type 'a structspec =
    Incomplete of incomplete_size
  | Complete of structured_spec

type abstract_type = {
  aname : string;
  asize : int;
  aalignment : int;
}

type _ ocaml_type =
  String     : string ocaml_type
| Bytes      : Bytes.t ocaml_type
| FloatArray : float array ocaml_type

type _ typ =
    Void            :                       unit typ
  | Primitive       : 'a Ctypes_primitive_types.prim -> 'a typ
  | Pointer         : 'a typ             -> 'a ptr typ
  | Funptr          : 'a fn              -> 'a static_funptr typ
  | Struct          : 'a structure_type  -> 'a structure typ
  | Union           : 'a union_type      -> 'a union typ
  | Abstract        : abstract_type      -> 'a abstract typ
  | View            : ('a, 'b) view      -> 'a typ
  | Array           : 'a typ * int       -> 'a carray typ
  | Bigarray        : (_, 'a) Ctypes_bigarray.t
                                         -> 'a typ
  | OCaml           : 'a ocaml_type      -> 'a ocaml typ
and 'a carray = { astart : 'a ptr; alength : int }
and ('a, 'kind) structured = { structured : ('a, 'kind) structured ptr }
and 'a union = ('a, [`Union]) structured
and 'a structure = ('a, [`Struct]) structured
and 'a abstract = ('a, [`Abstract]) structured
and (_, _) pointer =
  CPointer : 'a typ Ctypes_ptr.Fat.t -> ('a, [`C]) pointer
| OCamlRef : int * 'a * 'a ocaml_type -> ('a, [`OCaml]) pointer
and 'a ptr = ('a, [`C]) pointer
and 'a ocaml = ('a, [`OCaml]) pointer
and 'a static_funptr = Static_funptr of 'a fn Ctypes_ptr.Fat.t
and ('a, 'b) view = {
  read : 'b -> 'a;
  write : 'a -> 'b;
  format_typ: ((Format.formatter -> unit) -> Format.formatter -> unit) option;
  format: (Format.formatter -> 'a -> unit) option;
  ty: 'b typ;
}
and ('a, 's) field = {
  ftype: 'a typ;
  foffset: int;
  fname: string;
}
and 'a structure_type = {
  tag: string;
  mutable spec: 'a structspec;
  (* fields are in reverse order iff the struct type is incomplete *)
  mutable fields : 'a structure boxed_field list;
}
and 'a union_type = {
  utag: string;
  mutable uspec: structured_spec option;
  (* fields are in reverse order iff the union type is incomplete *)
  mutable ufields : 'a union boxed_field list;
}
and 's boxed_field = BoxedField : ('a, 's) field -> 's boxed_field
and _ fn =
  | Returns  : 'a typ   -> 'a fn
  | Function : 'a typ * 'b fn  -> ('a -> 'b) fn

type _ bigarray_class =
  Genarray :
  < element: 'a;
    dims: int array;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t;
    carray: 'a carray > bigarray_class
| Array1 :
  < element: 'a;
    dims: int;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array1.t;
    carray: 'a carray > bigarray_class
| Array2 :
  < element: 'a;
    dims: int * int;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array2.t;
    carray: 'a carray carray > bigarray_class
| Array3 :
  < element: 'a;
    dims: int * int * int;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array3.t;
    carray: 'a carray carray carray > bigarray_class

type boxed_typ = BoxedType : 'a typ -> boxed_typ

let rec sizeof : type a. a typ -> int = function
    Void                           -> raise IncompleteType
  | Primitive p                    -> Ctypes_primitives.sizeof p
  | Struct { spec = Incomplete _ } -> raise IncompleteType
  | Struct { spec = Complete
      { size } }                   -> size
  | Union { uspec = None }         -> raise IncompleteType
  | Union { uspec = Some { size } }
                                   -> size
  | Array (t, i)                   -> i * sizeof t
  | Bigarray ba                    -> Ctypes_bigarray.sizeof ba
  | Abstract { asize }             -> asize
  | Pointer _                      -> Ctypes_primitives.pointer_size
  | Funptr _                       -> Ctypes_primitives.pointer_size
  | OCaml _                        -> raise IncompleteType
  | View { ty }                    -> sizeof ty

let rec alignment : type a. a typ -> int = function
    Void                             -> raise IncompleteType
  | Primitive p                      -> Ctypes_primitives.alignment p
  | Struct { spec = Incomplete _ }   -> raise IncompleteType
  | Struct { spec = Complete
      { align } }                    -> align
  | Union { uspec = None }           -> raise IncompleteType
  | Union { uspec = Some { align } } -> align
  | Array (t, _)                     -> alignment t
  | Bigarray ba                      -> Ctypes_bigarray.alignment ba
  | Abstract { aalignment }          -> aalignment
  | Pointer _                        -> Ctypes_primitives.pointer_alignment
  | Funptr _                         -> Ctypes_primitives.pointer_alignment
  | OCaml _                          -> raise IncompleteType
  | View { ty }                      -> alignment ty

let rec passable : type a. a typ -> bool = function
    Void                           -> true
  | Primitive _                    -> true
  | Struct { spec = Incomplete _ } -> raise IncompleteType
  | Struct { spec = Complete _ }   -> true
  | Union  { uspec = None }        -> raise IncompleteType
  | Union  { uspec = Some _ }      -> true
  | Array _                        -> false
  | Bigarray _                     -> false
  | Pointer _                      -> true
  | Funptr _                       -> true
  | Abstract _                     -> false
  | OCaml _                        -> true
  | View { ty }                    -> passable ty

(* Whether a value resides in OCaml-managed memory.
   Values that reside in OCaml memory cannot be accessed
   when the runtime lock is not held. *)
let rec ocaml_value : type a. a typ -> bool = function
    Void        -> false
  | Primitive _ -> false
  | Struct _    -> false
  | Union _     -> false
  | Array _     -> false
  | Bigarray _  -> false
  | Pointer _   -> false
  | Funptr _    -> false
  | Abstract _  -> false
  | OCaml _     -> true
  | View { ty } -> ocaml_value ty

let rec has_ocaml_argument : type a. a fn -> bool = function
    Returns _ -> false
  | Function (t, _) when ocaml_value t -> true
  | Function (_, t) -> has_ocaml_argument t

let void = Void
let char = Primitive Ctypes_primitive_types.Char
let schar = Primitive Ctypes_primitive_types.Schar
let float = Primitive Ctypes_primitive_types.Float
let double = Primitive Ctypes_primitive_types.Double
let complex32 = Primitive Ctypes_primitive_types.Complex32
let complex64 = Primitive Ctypes_primitive_types.Complex64
let short = Primitive Ctypes_primitive_types.Short
let int = Primitive Ctypes_primitive_types.Int
let sint = Primitive Ctypes_primitive_types.Sint
let long = Primitive Ctypes_primitive_types.Long
let llong = Primitive Ctypes_primitive_types.Llong
let nativeint = Primitive Ctypes_primitive_types.Nativeint
let int8_t = Primitive Ctypes_primitive_types.Int8_t
let int16_t = Primitive Ctypes_primitive_types.Int16_t
let int32_t = Primitive Ctypes_primitive_types.Int32_t
let int64_t = Primitive Ctypes_primitive_types.Int64_t
let camlint = Primitive Ctypes_primitive_types.Camlint
let uchar = Primitive Ctypes_primitive_types.Uchar
let bool = Primitive Ctypes_primitive_types.Bool
let uint8_t = Primitive Ctypes_primitive_types.Uint8_t
let uint16_t = Primitive Ctypes_primitive_types.Uint16_t
let uint32_t = Primitive Ctypes_primitive_types.Uint32_t
let uint64_t = Primitive Ctypes_primitive_types.Uint64_t
let size_t = Primitive Ctypes_primitive_types.Size_t
let ushort = Primitive Ctypes_primitive_types.Ushort
let uint = Primitive Ctypes_primitive_types.Uint
let ulong = Primitive Ctypes_primitive_types.Ulong
let ullong = Primitive Ctypes_primitive_types.Ullong
let array i t = Array (t, i)
let ocaml_string = OCaml String
let ocaml_bytes = OCaml Bytes
let ocaml_float_array = OCaml FloatArray
let ptr t = Pointer t
let ( @->) f t =
  if not (passable f) then
    raise (Unsupported "Unsupported argument type")
  else
    Function (f, t)
let abstract ~name ~size ~alignment =
  Abstract { aname = name; asize = size; aalignment = alignment }
let view ?format_typ ?format ~read ~write ty =
  View { read; write; format_typ; format; ty }
let id v = v
let typedef old name =
  view ~format_typ:(fun k fmt -> Format.fprintf fmt "%s%t" name k)
    ~read:id ~write:id old
let bigarray : type a b c d e.
  < element: a;
    dims: b;
    ba_repr: c;
    bigarray: d;
    carray: e > bigarray_class ->
   b -> (a, c) Bigarray.kind -> d typ =
  fun spec dims kind -> match spec with
  | Genarray -> Bigarray (Ctypes_bigarray.bigarray dims kind)
  | Array1 -> Bigarray (Ctypes_bigarray.bigarray1 dims kind)
  | Array2 -> let d1, d2 = dims in
              Bigarray (Ctypes_bigarray.bigarray2 d1 d2 kind)
  | Array3 -> let d1, d2, d3 = dims in
              Bigarray (Ctypes_bigarray.bigarray3 d1 d2 d3 kind)
let returning v =
  if not (passable v) then
    raise (Unsupported "Unsupported return type")
  else
    Returns v
let static_funptr fn = Funptr fn

let structure tag =
  Struct { spec = Incomplete { isize = 0 }; tag; fields = [] }

let union utag = Union { utag; uspec = None; ufields = [] }

let offsetof { foffset } = foffset
let field_type { ftype } = ftype
let field_name { fname } = fname

(* This corresponds to the enum in ctypes_primitives.h *)
type arithmetic =
    Int8
  | Int16
  | Int32
  | Int64
  | Uint8
  | Uint16
  | Uint32
  | Uint64
  | Float
  | Double

end
module Ctypes_type_printing : sig 
#1 "ctypes_type_printing.mli"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static

(* The format context affects the formatting of pointer, struct and union
   types.  There are three printing contexts: *)
type format_context = [
(* In the top-level context struct and union types are printed in full, with
   member lists.  Pointer types are unparenthesized; for example,
   pointer-to-void is printed as "void *", not as "void ( * )". *)
| `toplevel
(* In the array context, struct and union types are printed in abbreviated
   form, which consists of just a keyword and the tag name.  Pointer types are
   parenthesized; for example, pointer-to-array-of-int is printed as
   "int ( * )[]", not as "int *[]". *)
| `array
(* In the non-array context, struct and union types are printed in abbreviated
   form and pointer types are unparenthesized. *)
| `nonarray]

val format_name : ?name:string -> Format.formatter -> unit

val format_typ' : 'a Ctypes_static.typ -> (format_context -> Format.formatter -> unit) ->
  format_context -> Format.formatter -> unit

val format_typ : ?name:string -> Format.formatter -> 'a typ -> unit

val format_fn' : 'a fn -> (Format.formatter -> unit) -> Format.formatter -> unit

val format_fn : ?name:string -> Format.formatter -> 'a fn -> unit

val string_of_typ : ?name:string -> 'a typ -> string

val string_of_fn : ?name:string -> 'a fn -> string

end = struct
#1 "ctypes_type_printing.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static

(* See type_printing.mli for the documentation of [format context]. *)
type format_context = [ `toplevel | `array | `nonarray ]

let rec format_typ' : type a. a typ ->
  (format_context -> Format.formatter -> unit) ->
  (format_context -> Format.formatter -> unit) =
  let fprintf = Format.fprintf in
  fun t k context fmt -> match t with
    | Void ->
      fprintf fmt "void%t" (k `nonarray)
    | Primitive p ->
      let name = Ctypes_primitives.name p in
      fprintf fmt "%s%t" name (k `nonarray)
    | View { format_typ = Some format } ->
      format (k `nonarray) fmt
    | View { ty } ->
      format_typ' ty k context fmt
    | Abstract { aname } ->
      fprintf fmt "%s%t" aname (k `nonarray)
    | Struct { tag ; spec; fields } ->
      begin match spec, context with
        | Complete _, `toplevel ->
          begin
            fprintf fmt "struct %s {@;<1 2>@[" tag;
            format_fields fields fmt;
            fprintf fmt "@]@;}%t" (k `nonarray)
          end
        | _ -> fprintf fmt "struct %s%t" tag (k `nonarray)
      end
    | Union { utag; uspec; ufields } ->
      begin match uspec, context with
        | Some _, `toplevel ->
          begin
            fprintf fmt "union %s {@;<1 2>@[" utag;
            format_fields ufields fmt;
            fprintf fmt "@]@;}%t" (k `nonarray)
          end
        | _ -> fprintf fmt "union %s%t" utag (k `nonarray)
      end
    | Pointer ty ->
      format_typ' ty
        (fun context fmt ->
          match context with
            | `array -> fprintf fmt "(*%t)" (k `nonarray)
            | _      -> fprintf fmt "*%t" (k `nonarray))
        `nonarray fmt
    | Funptr fn ->
      format_fn' fn
        (fun fmt -> Format.fprintf fmt "(*%t)" (k `nonarray)) fmt
    | Array (ty, n) ->
      format_typ' ty (fun _ fmt -> fprintf fmt "%t[%d]" (k `array) n) `nonarray
        fmt
    | Bigarray ba ->
      let elem = Ctypes_bigarray.element_type ba
      and dims = Ctypes_bigarray.dimensions ba in
      let name = Ctypes_primitives.name elem in
      fprintf fmt "%s%t%t" name (k `array)
        (fun fmt -> (Array.iter (Format.fprintf fmt "[%d]") dims))
    | OCaml String -> format_typ' (ptr char) k context fmt
    | OCaml Bytes -> format_typ' (ptr char) k context fmt
    | OCaml FloatArray -> format_typ' (ptr double) k context fmt

and format_fields : type a. a boxed_field list -> Format.formatter -> unit =
  fun fields fmt ->
  let open Format in
      List.iteri
        (fun i (BoxedField {ftype=t; fname}) ->
          fprintf fmt "@[";
          format_typ' t (fun _ fmt -> fprintf fmt " %s" fname) `nonarray fmt;
          fprintf fmt "@];@;")
        fields
and format_parameter_list parameters k fmt =
  Format.fprintf fmt "%t(@[@[" k;
  if parameters = [] then Format.fprintf fmt "void" else
    List.iteri
      (fun i (BoxedType t) ->
        if i <> 0 then Format.fprintf fmt "@], @[";
        format_typ' t (fun _ _ -> ()) `nonarray fmt)
      parameters;
  Format.fprintf fmt "@]@])"
and format_fn' : 'a. 'a fn ->
  (Format.formatter -> unit) ->
  (Format.formatter -> unit) =
  let rec gather : type a. a fn -> boxed_typ list * boxed_typ =
    function
      | Returns ty -> [], BoxedType ty
      | Function (Void, fn) -> gather fn
      | Function (p, fn) -> let ps, r = gather fn in BoxedType p :: ps, r in
  fun fn k fmt ->
    let ps, BoxedType r = gather fn in
    format_typ' r (fun context fmt -> format_parameter_list ps k fmt)
      `nonarray fmt

let format_name ?name fmt =
  match name with
    | Some name -> Format.fprintf fmt " %s" name
    | None      -> ()

let format_typ : ?name:string -> Format.formatter -> 'a typ -> unit
  = fun ?name fmt typ ->
    Format.fprintf fmt "@[";
    format_typ' typ (fun context -> format_name ?name) `toplevel fmt;
    Format.fprintf fmt "@]"

let format_fn : ?name:string -> Format.formatter -> 'a fn -> unit
  = fun ?name fmt fn ->
    Format.fprintf fmt "@[";
    format_fn' fn (format_name ?name) fmt;
    Format.fprintf fmt "@]"

let string_of_typ ?name ty = Format.asprintf "%a" (format_typ ?name) ty
let string_of_fn ?name fn = Format.asprintf "%a" (format_fn ?name) fn

end
module Ctypes_coerce
= struct
#1 "ctypes_coerce.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Coercions *)

open Ctypes_static

type uncoercible_info =
    Types : _ typ * _ typ -> uncoercible_info
  | Functions : _ fn * _ fn -> uncoercible_info

exception Uncoercible of uncoercible_info

let show_uncoercible = function
    Uncoercible (Types (l, r)) ->
    let pr ty = Ctypes_type_printing.string_of_typ ty in
    Some (Format.sprintf
            "Coercion failure: %s is not coercible to %s" (pr l) (pr r))
  | Uncoercible (Functions (l, r)) ->
    let pr ty = Ctypes_type_printing.string_of_fn ty in
    Some (Format.sprintf
            "Coercion failure: %s is not coercible to %s" (pr l) (pr r))
  | _ -> None

let () = Printexc.register_printer show_uncoercible

let uncoercible : 'a 'b 'c. 'a typ -> 'b typ -> 'c =
  fun l r -> raise (Uncoercible (Types (l, r)))

let uncoercible_functions : 'a 'b 'c. 'a fn -> 'b fn -> 'c =
  fun l r -> raise (Uncoercible (Functions (l, r)))

let id x = x

type (_, _) coercion =
  | Id : ('a, 'a) coercion
  | Coercion : ('a -> 'b) -> ('a, 'b) coercion

let ml_prim_coercion :
  type a b. a Ctypes_primitive_types.ml_prim -> b Ctypes_primitive_types.ml_prim ->
  (a, b) coercion option =
  let open Ctypes_primitive_types in
  fun l r -> match l, r with
  | ML_char, ML_char -> Some Id
  | ML_complex, ML_complex -> Some Id
  | ML_float, ML_float -> Some Id
  | ML_int, ML_int -> Some Id
  | ML_int32, ML_int32 -> Some Id
  | ML_int64, ML_int64 -> Some Id
  | ML_llong, ML_llong -> Some Id
  | ML_long, ML_long -> Some Id
  | ML_nativeint, ML_nativeint -> Some Id
  | ML_size_t, ML_size_t -> Some Id
  | ML_uchar, ML_uchar -> Some Id
  | ML_bool, ML_bool -> Some Id
  | ML_uint, ML_uint -> Some Id
  | ML_uint16, ML_uint16 -> Some Id
  | ML_uint32, ML_uint32 -> Some Id
  | ML_uint64, ML_uint64 -> Some Id
  | ML_uint8, ML_uint8 -> Some Id
  | ML_ullong, ML_ullong -> Some Id
  | ML_ulong, ML_ulong -> Some Id
  | ML_ushort, ML_ushort -> Some Id
  | l, r -> None

let rec coercion : type a b. a typ -> b typ -> (a, b) coercion =
  fun atyp btyp -> match atyp, btyp with
  | _, Void -> Coercion ignore
  | Primitive l, Primitive r ->
    (match Ctypes_primitive_types.(ml_prim_coercion (ml_prim l) (ml_prim r)) with
       Some c -> c
     | None -> uncoercible atyp btyp)
  | View av, b ->
    begin match coercion av.ty b with
    | Id -> Coercion av.write
    | Coercion coerce -> Coercion (fun v -> coerce (av.write v))
    end
  | a, View bv ->
    begin match coercion a bv.ty with
    | Id -> Coercion bv.read
    | Coercion coerce -> Coercion (fun v -> bv.read (coerce v))
    end
  | Pointer a, Pointer b ->
    begin
      try
        begin match coercion a b with
        | Id -> Id
        | Coercion _ ->
          Coercion (fun (CPointer p) -> CPointer (Ctypes_ptr.Fat.coerce p b))
        end
      with Uncoercible _ ->
        Coercion (fun (CPointer p) -> CPointer (Ctypes_ptr.Fat.coerce p b))
    end
  | Pointer a, Funptr b ->
    Coercion (fun (CPointer p) -> Static_funptr (Ctypes_ptr.Fat.coerce p b))
  | Funptr a, Pointer b ->
    Coercion (fun (Static_funptr p) -> CPointer (Ctypes_ptr.Fat.coerce p b))
  | Funptr a, Funptr b ->
    begin
      try
        begin match fn_coercion a b with
        | Id -> Id
        | Coercion _ ->
          Coercion (fun (Static_funptr p) -> Static_funptr (Ctypes_ptr.Fat.coerce p b))
        end
      with Uncoercible _ ->
        Coercion (fun (Static_funptr p) -> Static_funptr (Ctypes_ptr.Fat.coerce p b))
    end
  | l, r -> uncoercible l r

and fn_coercion : type a b. a fn -> b fn -> (a, b) coercion =
  fun afn bfn -> match afn, bfn with
  | Function (af, at), Function (bf, bt) ->
    begin match coercion bf af, fn_coercion at bt with
    | Id, Id -> Id
    | Id, Coercion h ->
      Coercion (fun g x -> h (g x))
    | Coercion f, Id ->
      Coercion (fun g x -> g (f x))
    | Coercion f, Coercion h ->
      Coercion (fun g x -> h (g (f x)))
    end
  | Returns at, Returns bt -> coercion at bt
  | l, r -> uncoercible_functions l r

let coerce : type a b. a typ -> b typ -> a -> b =
  fun atyp btyp -> match coercion atyp btyp with
  | Id -> id
  | Coercion c -> c

let coerce_fn : type a b. a fn -> b fn -> a -> b =
  fun afn bfn -> match fn_coercion afn bfn with
  | Id -> id
  | Coercion c -> c

end
module Ctypes_roots_stubs
= struct
#1 "ctypes_roots_stubs.ml"
(*
 * Copyright (c) 2015 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

external root : 'a -> Ctypes_ptr.voidp =
  "ctypes_caml_roots_create"

external set : Ctypes_ptr.voidp -> 'a -> unit =
  "ctypes_caml_roots_set"

external get : Ctypes_ptr.voidp -> 'a =
  "ctypes_caml_roots_get"

external release : Ctypes_ptr.voidp -> unit =
  "ctypes_caml_roots_release"

end
module Ctypes_memory
= struct
#1 "ctypes_memory.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static

module Stubs = Ctypes_memory_stubs
module Raw = Ctypes_ptr.Raw
module Fat = Ctypes_ptr.Fat

let castp reftype (CPointer p) = CPointer (Fat.coerce p reftype)

(* Describes how to read a value, e.g. from a return buffer *)
let rec build : type a b. a typ -> b typ Fat.t -> a
 = function
    | Void ->
      fun _ -> ()
    | Primitive p -> Stubs.read p
    | Struct { spec = Incomplete _ } ->
      raise IncompleteType
    | Struct { spec = Complete { size } } as reftyp ->
      (fun buf ->
        let managed = Stubs.allocate 1 size in
        let dst = Fat.make ~managed ~reftyp (Stubs.block_address managed) in
        let () = Stubs.memcpy ~size ~dst ~src:buf in
        { structured = CPointer dst})
    | Pointer reftyp ->
      (fun buf -> CPointer (Fat.make ~reftyp (Stubs.Pointer.read buf)))
    | Funptr fn ->
      (fun buf -> Static_funptr (Fat.make ~reftyp:fn (Stubs.Pointer.read buf)))
    | View { read; ty } ->
      let buildty = build ty in
      (fun buf -> read (buildty buf))
    | OCaml _ -> (fun buf -> assert false)
    (* The following cases should never happen; non-struct aggregate
       types are excluded during type construction. *)
    | Union _ -> assert false
    | Array _ -> assert false
    | Bigarray _ -> assert false
    | Abstract _ -> assert false

let rec write : type a b. a typ -> a -> b Fat.t -> unit
  = let write_aggregate size { structured = CPointer src } dst =
      Stubs.memcpy ~size ~dst ~src
    in
    function
    | Void -> (fun _ _ -> ())
    | Primitive p -> Stubs.write p
    | Pointer _ ->
      (fun (CPointer p) dst -> Stubs.Pointer.write p dst)
    | Funptr _ ->
      (fun (Static_funptr p) dst -> Stubs.Pointer.write p dst)
    | Struct { spec = Incomplete _ } -> raise IncompleteType
    | Struct { spec = Complete _ } as s -> write_aggregate (sizeof s)
    | Union { uspec = None } -> raise IncompleteType
    | Union { uspec = Some { size } } -> write_aggregate size
    | Abstract { asize } -> write_aggregate asize
    | Array _ as a ->
      let size = sizeof a in
      (fun { astart = CPointer src } dst ->
        Stubs.memcpy ~size ~dst ~src)
    | Bigarray b as t ->
      let size = sizeof t in
      (fun ba dst ->
        let src = Fat.make ~managed:ba ~reftyp:Void
          (Ctypes_bigarray.unsafe_address ba)
        in
        Stubs.memcpy ~size ~dst ~src)
    | View { write = w; ty } ->
      let writety = write ty in
      (fun v -> writety (w v))
    | OCaml _ -> raise IncompleteType

let null : unit ptr = CPointer (Fat.make ~reftyp:Void Raw.null)

let rec (!@) : type a. a ptr -> a
  = fun (CPointer cptr as ptr) ->
    match Fat.reftype cptr with
      | Void -> raise IncompleteType
      | Union { uspec = None } -> raise IncompleteType
      | Struct { spec = Incomplete _ } -> raise IncompleteType
      | View { read; ty } -> read (!@ (CPointer (Fat.coerce cptr ty)))
      (* If it's a reference type then we take a reference *)
      | Union _ -> { structured = ptr }
      | Struct _ -> { structured = ptr }
      | Array (elemtype, alength) ->
        { astart = CPointer (Fat.coerce cptr elemtype); alength }
      | Bigarray b -> Ctypes_bigarray.view b cptr
      | Abstract _ -> { structured = ptr }
      | OCaml _ -> raise IncompleteType
      (* If it's a value type then we cons a new value. *)
      | _ -> build (Fat.reftype cptr) cptr

let ptr_diff : type a b. (a, b) pointer -> (a, b) pointer -> int
  = fun l r ->
    match l, r with
    | CPointer lp, CPointer rp ->
      (* We assume the pointers are properly aligned, or at least that
         the difference is a multiple of sizeof reftype. *)
      Fat.diff_bytes lp rp / sizeof (Fat.reftype lp)
    | OCamlRef (lo, l, _), OCamlRef (ro, r, _) ->
      if l != r then invalid_arg "Ctypes.ptr_diff";
      ro - lo

let (+@) : type a b. (a, b) pointer -> int -> (a, b) pointer
  = fun p x ->
    match p with
    | CPointer p ->
      CPointer (Fat.add_bytes p (x * sizeof (Fat.reftype p)))
    | OCamlRef (offset, obj, ty) ->
      OCamlRef (offset + x, obj, ty)

let (-@) p x = p +@ (-x)

let (<-@) : type a. a ptr -> a -> unit
  = fun (CPointer p) ->
    fun v -> write (Fat.reftype p) v p

let from_voidp = castp
let to_voidp p = castp Void p

let allocate_n
  : type a. ?finalise:(a ptr -> unit) -> a typ -> count:int -> a ptr
  = fun ?finalise reftyp ~count ->
    let package p =
      CPointer (Fat.make ~managed:p ~reftyp (Stubs.block_address p))
    in
    let finalise = match finalise with
      | Some f -> Gc.finalise (fun p -> f (package p))
      | None -> ignore
    in
    let p = Stubs.allocate count (sizeof reftyp) in begin
      finalise p;
      package p
    end

let allocate : type a. ?finalise:(a ptr -> unit) -> a typ -> a -> a ptr
  = fun ?finalise reftype v ->
    let p = allocate_n ?finalise ~count:1 reftype in begin
      p <-@ v;
      p
    end

let ptr_compare (CPointer l) (CPointer r) = Fat.(compare l r)

let reference_type (CPointer p) = Fat.reftype p

let ptr_of_raw_address addr =
  CPointer (Fat.make ~reftyp:Void (Raw.of_nativeint addr))

let funptr_of_raw_address addr =
  Static_funptr (Fat.make ~reftyp:(void @-> returning void) (Raw.of_nativeint addr))

let raw_address_of_ptr (CPointer p) =
  (* This is unsafe by definition: if the object to which [p] refers
     is collected at this point then the returned address is invalid.
     If there is an OCaml object associated with [p] then it is vital
     that the caller retains a reference to it. *)
  Raw.to_nativeint (Fat.unsafe_raw_addr p)

module CArray =
struct
  type 'a t = 'a carray

  let check_bound { alength } i =
    if i >= alength then
      invalid_arg "index out of bounds"

  let unsafe_get { astart } n = !@(astart +@ n)
  let unsafe_set { astart } n v = (astart +@ n) <-@ v

  let get arr n =
    check_bound arr n;
    unsafe_get arr n

  let set arr n v =
    check_bound arr n;
    unsafe_set arr n v

  let start { astart } = astart
  let length { alength } = alength
  let from_ptr astart alength = { astart; alength }

  let fill ({ alength } as arr) v =
    for i = 0 to alength - 1 do unsafe_set arr i v done

  let make : type a. ?finalise:(a t -> unit) -> a typ -> ?initial:a -> int -> a t
    = fun ?finalise reftype ?initial count ->
      let finalise = match finalise with
        | Some f -> Some (fun astart -> f { astart; alength = count } )
        | None -> None
      in
      let arr = { astart = allocate_n ?finalise ~count reftype;
                  alength = count } in
      match initial with
        | None -> arr
        | Some v -> fill arr v; arr

  let element_type { astart } = reference_type astart

  let of_list typ list =
    let arr = make typ (List.length list) in
    List.iteri (set arr) list;
    arr

  let to_list a =
    let l = ref [] in
    for i = length a - 1 downto 0 do
      l := get a i :: !l
    done;
    !l
end

let make ?finalise s =
  let finalise = match finalise with
    | Some f -> Some (fun structured -> f { structured })
    | None -> None in
  { structured = allocate_n ?finalise s ~count:1 }
let (|->) (CPointer p) { ftype; foffset } =
  CPointer (Fat.(add_bytes (Fat.coerce p ftype) foffset))

let (@.) { structured = p } f = p |-> f
let setf s field v = (s @. field) <-@ v
let getf s field = !@(s @. field)

let addr { structured } = structured

open Bigarray

let _bigarray_start kind ba =
  let raw_address = Ctypes_bigarray.unsafe_address ba in
  let reftyp = Primitive (Ctypes_bigarray.prim_of_kind kind) in
  CPointer (Fat.make ~managed:ba ~reftyp raw_address)

let bigarray_kind : type a b c d f.
  < element: a;
    ba_repr: f;
    bigarray: b;
    carray: c;
    dims: d > bigarray_class -> b -> (a, f) Bigarray.kind =
  function
  | Genarray -> Genarray.kind
  | Array1 -> Array1.kind
  | Array2 -> Array2.kind
  | Array3 -> Array3.kind

let bigarray_start spec ba = _bigarray_start (bigarray_kind spec ba) ba

let array_of_bigarray : type a b c d e.
  < element: a;
    ba_repr: e;
    bigarray: b;
    carray: c;
    dims: d > bigarray_class -> b -> c
  = fun spec ba ->
    let CPointer p as element_ptr =
      bigarray_start spec ba in
    match spec with
  | Genarray ->
    let ds = Genarray.dims ba in
    CArray.from_ptr element_ptr (Array.fold_left ( * ) 1 ds)
  | Array1 ->
    let d = Array1.dim ba in
    CArray.from_ptr element_ptr d
  | Array2 ->
    let d1 = Array2.dim1 ba and d2 = Array2.dim2 ba in
    CArray.from_ptr (castp (array d2 (Fat.reftype p)) element_ptr) d1
  | Array3 ->
    let d1 = Array3.dim1 ba and d2 = Array3.dim2 ba and d3 = Array3.dim3 ba in
    CArray.from_ptr (castp (array d2 (array d3 (Fat.reftype p))) element_ptr) d1

let bigarray_elements : type a b c d f.
   < element: a;
     ba_repr: f;
     bigarray: b;
     carray: c;
     dims: d > bigarray_class -> d -> int
  = fun spec dims -> match spec, dims with
   | Genarray, ds -> Array.fold_left ( * ) 1 ds
   | Array1, d -> d
   | Array2, (d1, d2) -> d1 * d2
   | Array3, (d1, d2, d3) -> d1 * d2 * d3

let bigarray_of_ptr spec dims kind ptr =
  !@ (castp (bigarray spec dims kind) ptr)

let array_dims : type a b c d f.
   < element: a;
     ba_repr: f;
     bigarray: b;
     carray: c carray;
     dims: d > bigarray_class -> c carray -> d =
   let unsupported () = raise (Unsupported "taking dimensions of non-array type") in
   fun spec a -> match spec with
   | Genarray -> [| a.alength |]
   | Array1 -> a.alength
   | Array2 ->
     begin match a.astart with
     | CPointer p ->
       begin match Fat.reftype p with
       | Array (_, n) -> (a.alength, n)
       | _ -> unsupported ()
       end
    end
   | Array3 ->
     begin match a.astart with
     | CPointer p ->
       begin match Fat.reftype p with
       |  Array (Array (_, m), n) -> (a.alength, n, m)
       | _ -> unsupported ()
       end
     end

let bigarray_of_array spec kind a =
  let dims = array_dims spec a in
  !@ (castp (bigarray spec dims kind) (CArray.start a))

let genarray = Genarray
let array1 = Array1
let array2 = Array2
let array3 = Array3
let typ_of_bigarray_kind k = Primitive (Ctypes_bigarray.prim_of_kind k)

let string_from_ptr (CPointer p) ~length:len =
  if len < 0 then invalid_arg "Ctypes.string_from_ptr"
  else Stubs.string_of_array p ~len

let ocaml_string_start str =
  OCamlRef (0, str, String)

let ocaml_bytes_start str =
  OCamlRef (0, str, Bytes)

let ocaml_float_array_start arr =
  OCamlRef (0, arr, FloatArray)

module Root =
struct
  module Stubs = Ctypes_roots_stubs

  (* Roots are not managed values so it's safe to call unsafe_raw_addr. *)
  let raw_addr : unit ptr -> Raw.t =
    fun (CPointer p) -> Fat.unsafe_raw_addr p

  let create : 'a. 'a -> unit ptr =
    fun v -> CPointer (Fat.make ~reftyp:void (Stubs.root v))

  let get : 'a. unit ptr -> 'a =
    fun p -> Stubs.get (raw_addr p)

  let set : 'a. unit ptr -> 'a -> unit =
    fun p v -> Stubs.set (raw_addr p) v
  
  let release : 'a. unit ptr -> unit =
    fun p -> Stubs.release (raw_addr p)
end

let is_null (CPointer p) = Fat.is_null p

end
module Ctypes_std_view_stubs
= struct
#1 "ctypes_std_view_stubs.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Stubs for standard views. *)

(* Convert a C string to an OCaml string *)
external string_of_cstring : char Ctypes_static.typ Ctypes_ptr.Fat.t -> string
  = "ctypes_string_of_cstring"

(* Convert an OCaml string to a C string *)
external cstring_of_string : string -> Ctypes_memory_stubs.managed_buffer
  = "ctypes_cstring_of_string"

(* Size information for uintptr_t *)
external uintptr_t_size : unit -> int = "ctypes_uintptr_t_size"

(* Size information for uintptr_t *)
external intptr_t_size : unit -> int = "ctypes_intptr_t_size"

(* Size information for ptrdiff_t *)
external ptrdiff_t_size : unit -> int = "ctypes_ptrdiff_t_size"

end
module Ctypes_std_views
= struct
#1 "ctypes_std_views.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

let string_of_char_ptr (Ctypes_static.CPointer p) =
  Ctypes_std_view_stubs.string_of_cstring p

let char_ptr_of_string s =
  let managed = Ctypes_std_view_stubs.cstring_of_string s in
  Ctypes_static.CPointer (Ctypes_ptr.Fat.make ~managed ~reftyp:Ctypes_static.char
                     (Ctypes_memory_stubs.block_address managed))

let string = Ctypes_static.(view (ptr char))
  ~read:string_of_char_ptr ~write:char_ptr_of_string

let read_nullable t reftyp =
  let coerce = Ctypes_coerce.coerce Ctypes_static.(ptr reftyp) t in
  fun p -> if Ctypes_memory.is_null p then None else Some (coerce p)

let write_nullable t reftyp =
  let coerce = Ctypes_coerce.coerce t Ctypes_static.(ptr reftyp) in
  Ctypes_memory.(function None -> from_voidp reftyp null | Some f -> coerce f)

let nullable_view ?format_typ ?format t reftyp =
  let read = read_nullable t reftyp
  and write = write_nullable t reftyp
  in Ctypes_static.(view ~read ~write ?format_typ ?format (ptr reftyp))

let read_nullable_funptr t reftyp =
  let coerce = Ctypes_coerce.coerce (Ctypes_static.static_funptr reftyp) t in
  fun (Ctypes_static.Static_funptr p as ptr) ->
    if Ctypes_ptr.Fat.is_null p
    then None
    else Some (coerce ptr)

let write_nullable_funptr t reftyp =
  let coerce = Ctypes_coerce.coerce t Ctypes_static.(static_funptr reftyp) in
  function None -> Ctypes_static.Static_funptr
                     (Ctypes_ptr.Fat.make ~reftyp Ctypes_ptr.Raw.null)
         | Some f -> coerce f

let nullable_funptr_view ?format_typ ?format t reftyp =
  let read = read_nullable_funptr t reftyp
  and write = write_nullable_funptr t reftyp
  in Ctypes_static.(view ~read ~write ?format_typ ?format (static_funptr reftyp))

let ptr_opt t = nullable_view (Ctypes_static.ptr t) t

let string_opt = nullable_view string Ctypes_static.char

module type Signed_type =
sig
  include Signed.S
  val t : t Ctypes_static.typ
end

module type Unsigned_type =
sig
  include Unsigned.S
  val t : t Ctypes_static.typ
end

let signed_typedef name ~size : (module Signed_type) =
  match size with
    1 -> (module struct include Signed.Int
           let t = Ctypes_static.(typedef int8_t name) end)
  | 2 -> (module struct include Signed.Int
           let t = Ctypes_static.(typedef int16_t name) end)
  | 4 -> (module struct include Signed.Int32
           let t = Ctypes_static.(typedef int32_t name) end)
  | 8 -> (module struct include Signed.Int64
           let t = Ctypes_static.(typedef int64_t name) end)
  | n -> Printf.kprintf failwith "size %d not supported for %s\n" n name

let unsigned_typedef name ~size : (module Unsigned_type) =
  match size with
  | 1 -> (module struct include Unsigned.UInt8
           let t = Ctypes_static.(typedef uint8_t name) end)
  | 2 -> (module struct include Unsigned.UInt16
           let t = Ctypes_static.(typedef uint16_t name) end)
  | 4 -> (module struct include Unsigned.UInt32
           let t = Ctypes_static.(typedef uint32_t name) end)
  | 8 -> (module struct include Unsigned.UInt64
           let t = Ctypes_static.(typedef uint64_t name) end)
  | n -> Printf.kprintf failwith "size %d not supported for %s\n" n name

module Intptr = (val signed_typedef "intptr_t"
                    ~size:(Ctypes_std_view_stubs.intptr_t_size ()))
module Uintptr = (val unsigned_typedef "uintptr_t"
                    ~size:(Ctypes_std_view_stubs.uintptr_t_size ()))
let intptr_t = Intptr.t
let uintptr_t = Uintptr.t

module Ptrdiff = (val signed_typedef "ptrdiff_t"
                     ~size:(Ctypes_std_view_stubs.ptrdiff_t_size ()))
let ptrdiff_t = Ptrdiff.t

end
module Ctypes_structs : sig 
#1 "ctypes_structs.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static

module type S =
sig
  type (_, _) field
  val field : 't typ -> string -> 'a typ ->
    ('a, (('s, [<`Struct | `Union]) structured as 't)) field
  val seal : (_, [< `Struct | `Union]) Ctypes_static.structured Ctypes_static.typ -> unit
end

end = struct
#1 "ctypes_structs.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static

module type S =
sig
  type (_, _) field
  val field : 't typ -> string -> 'a typ ->
    ('a, (('s, [<`Struct | `Union]) structured as 't)) field
  val seal : (_, [< `Struct | `Union]) Ctypes_static.structured Ctypes_static.typ -> unit
end

end
module Ctypes_structs_computed : sig 
#1 "ctypes_structs_computed.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** Structs and unions whose layouts are computed from the sizes and alignment
    requirements of the constituent field types. *)

include Ctypes_structs.S
  with type ('a, 's) field := ('a, 's) Ctypes_static.field

end = struct
#1 "ctypes_structs_computed.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static

let max_field_alignment fields =
  List.fold_left
    (fun align (BoxedField {ftype}) -> max align (alignment ftype))
    0
    fields

let max_field_size fields =
  List.fold_left
    (fun size (BoxedField {ftype}) -> max size (sizeof ftype))
    0
    fields

let aligned_offset offset alignment =
  match offset mod alignment with
    0 -> offset
  | overhang -> offset - overhang + alignment

let rec field : type t a. t typ -> string -> a typ -> (a, t) field =
  fun structured label ftype ->
  match structured with
  | Struct ({ spec = Incomplete spec } as s) ->
    let foffset = aligned_offset spec.isize (alignment ftype) in
    let field = { ftype; foffset; fname = label } in
    begin
      spec.isize <- foffset + sizeof ftype;
      s.fields <- BoxedField field :: s.fields;
      field
    end
  | Union ({ uspec = None } as u) ->
    let field = { ftype; foffset = 0; fname = label } in
    u.ufields <- BoxedField field :: u.ufields;
    field
  | Struct { tag; spec = Complete _ } -> raise (ModifyingSealedType tag)
  | Union { utag } -> raise (ModifyingSealedType utag)
  | View { ty } ->
     let { ftype; foffset; fname } = field ty label ftype in
     { ftype; foffset; fname }
  | _ -> raise (Unsupported "Adding a field to non-structured type")

let rec seal : type a. a typ -> unit = function
  | Struct { fields = [] } -> raise (Unsupported "struct with no fields")
  | Struct { spec = Complete _; tag } -> raise (ModifyingSealedType tag)
  | Struct ({ spec = Incomplete { isize } } as s) ->
    s.fields <- List.rev s.fields;
    let align = max_field_alignment s.fields in
    let size = aligned_offset isize align in
    s.spec <- Complete { (* sraw_io;  *)size; align }
  | Union { utag; uspec = Some _ } ->
    raise (ModifyingSealedType utag)
  | Union { ufields = [] } ->
    raise (Unsupported "union with no fields")
  | Union u -> begin
    u.ufields <- List.rev u.ufields;
    let size = max_field_size u.ufields
    and align = max_field_alignment u.ufields in
    u.uspec <- Some { align; size = aligned_offset size align }
  end
  | View { ty } -> seal ty
  | _ -> raise (Unsupported "Sealing a non-structured type")

end
(** Interface as module  *)
module Ctypes_types
= struct
#1 "ctypes_types.mli"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Signed
open Unsigned


(** Abstract interface to C object type descriptions *)
module type TYPE =
sig
  (** {2:types Values representing C types} *)

  type 'a typ
  (** The type of values representing C types.  There are two types associated
      with each [typ] value: the C type used to store and pass values, and the
      corresponding OCaml type.  The type parameter indicates the OCaml type, so a
      value of type [t typ] is used to read and write OCaml values of type [t].
      There are various uses of [typ] values, including

      - constructing function types for binding native functions using
      {!Foreign.foreign}

      - constructing pointers for reading and writing locations in C-managed
      storage using {!ptr}

      - describing the fields of structured types built with {!structure} and
      {!union}.
  *)

  (** {3 The void type} *)

  val void  : unit typ
  (** Value representing the C void type.  Void values appear in OCaml as the
      unit type, so using void in an argument or result type specification
      produces a function which accepts or returns unit.

      Dereferencing a pointer to void is an error, as in C, and will raise
      {!IncompleteType}.
  *)

  (** {3 Scalar types}

      The scalar types consist of the {!arithmetic_types} and the {!pointer_types}.
  *)

  (** {4:arithmetic_types Arithmetic types}

      The arithmetic types consist of the signed and unsigned integer types
      (including character types) and the floating types.  There are values
      representing both exact-width integer types (of 8, 16, 32 and 64 bits) and
      types whose size depend on the platform (signed and unsigned short, int, long,
      long long).

  *)

  val char : char typ
  (** Value representing the C type [char]. *)

  (** {5 Signed integer types} *)

  val schar : int typ
  (** Value representing the C type [signed char]. *)

  val short : int typ
  (** Value representing the C type ([signed]) [short]. *)

  val int   : int typ
  (** Value representing the C type ([signed]) [int]. *)

  val long  : long typ
  (** Value representing the C type ([signed]) [long]. *)

  val llong  : llong typ
  (** Value representing the C type ([signed]) [long long]. *)

  val nativeint : nativeint typ
  (** Value representing the C type ([signed]) [int]. *)

  val int8_t : int typ
  (** Value representing an 8-bit signed integer C type. *)

  val int16_t : int typ
  (** Value representing a 16-bit signed integer C type. *)

  val int32_t : int32 typ
  (** Value representing a 32-bit signed integer C type. *)

  val int64_t : int64 typ
  (** Value representing a 64-bit signed integer C type. *)

  module Intptr : Signed.S
  val intptr_t : Intptr.t typ
  (** Value representing the C type [intptr_t]. *)

  module Ptrdiff : Signed.S
  val ptrdiff_t : Ptrdiff.t typ
  (** Value representing the C type [ptrdiff_t]. *)

  val camlint : int typ
  (** Value representing an integer type with the same storage requirements as
      an OCaml [int]. *)

  (** {5 Unsigned integer types} *)

  val uchar : uchar typ
  (** Value representing the C type [unsigned char]. *)

  val bool : bool typ
  (** Value representing the C type [bool]. *)

  val uint8_t : uint8 typ
  (** Value representing an 8-bit unsigned integer C type. *)

  val uint16_t : uint16 typ
  (** Value representing a 16-bit unsigned integer C type. *)

  val uint32_t : uint32 typ
  (** Value representing a 32-bit unsigned integer C type. *)

  val uint64_t : uint64 typ
  (** Value representing a 64-bit unsigned integer C type. *)

  val size_t : size_t typ
  (** Value representing the C type [size_t], an alias for one of the unsigned
      integer types.  The actual size and alignment requirements for [size_t]
      vary between platforms. *)

  val ushort : ushort typ
  (** Value representing the C type [unsigned short]. *)

  val sint : sint typ
  (** Value representing the C type [int]. *)

  val uint : uint typ
  (** Value representing the C type [unsigned int]. *)

  val ulong : ulong typ
  (** Value representing the C type [unsigned long]. *)

  val ullong : ullong typ
  (** Value representing the C type [unsigned long long]. *)

  module Uintptr : Unsigned.S
  val uintptr_t : Uintptr.t typ
  (** Value representing the C type [uintptr_t]. *)

  (** {5 Floating types} *)

  val float : float typ
  (** Value representing the C single-precision [float] type. *)

  val double : float typ
  (** Value representing the C type [double]. *)

  (** {5 Complex types} *)

  val complex32 : Complex.t typ
  (** Value representing the C99 single-precision [float complex] type. *)

  val complex64 : Complex.t typ
  (** Value representing the C99 double-precision [double complex] type. *)

  (** {4:pointer_types Pointer types} *)

  (** {5 C-compatible pointers} *)

  val ptr : 'a typ -> 'a Ctypes_static.ptr typ
  (** Construct a pointer type from an existing type (called the {i reference
      type}).  *)

  val ptr_opt : 'a typ -> 'a Ctypes_static.ptr option typ
  (** Construct a pointer type from an existing type (called the {i reference
      type}).  This behaves like {!ptr}, except that null pointers appear in OCaml
      as [None]. *)

  val string : string typ
  (** A high-level representation of the string type.

      On the C side this behaves like [char *]; on the OCaml side values read
      and written using {!string} are simply native OCaml strings.

      To avoid problems with the garbage collector, values passed using
      {!string} are copied into immovable C-managed storage before being passed
      to C.
  *)

  val string_opt : string option typ
  (** A high-level representation of the string type.  This behaves like {!string},
      except that null pointers appear in OCaml as [None].
  *)

  (** {5 OCaml pointers} *)

  val ocaml_string : string Ctypes_static.ocaml typ
  (** Value representing the directly mapped storage of an OCaml string. *)

  val ocaml_bytes : Bytes.t Ctypes_static.ocaml typ
  (** Value representing the directly mapped storage of an OCaml byte array. *)

  (** {3 Array types} *)

  (** {4 C array types} *)

  val array : int -> 'a typ -> 'a Ctypes_static.carray typ
  (** Construct a sized array type from a length and an existing type (called
      the {i element type}). *)

  (** {4 Bigarray types} *)

  val bigarray :
    < element: 'a;
      ba_repr: 'b;
      dims: 'dims;
      bigarray: 'bigarray;
      carray: _ > Ctypes_static.bigarray_class ->
     'dims -> ('a, 'b) Bigarray.kind -> 'bigarray typ
  (** Construct a sized bigarray type representation from a bigarray class, the
      dimensions, and the {!Bigarray.kind}. *)

  val typ_of_bigarray_kind : ('a, 'b) Bigarray.kind -> 'a typ
  (** [typ_of_bigarray_kind k] is the type corresponding to the Bigarray kind
      [k]. *)

  (** {3 Struct and union types} *)

  type ('a, 't) field

  val structure : string -> 's Ctypes_static.structure typ
  (** Construct a new structure type.  The type value returned is incomplete and
      can be updated using {!field} until it is passed to {!seal}, at which point
      the set of fields is fixed.

      The type (['_s structure typ]) of the expression returned by the call
      [structure tag] includes a weak type variable, which can be explicitly
      instantiated to ensure that the OCaml values representing different C
      structure types have incompatible types.  Typical usage is as follows:

      [type tagname]

      [let tagname : tagname structure typ = structure "tagname"]
  *)

  val union : string -> 's Ctypes_static.union typ
  (** Construct a new union type.  This behaves analogously to {!structure};
      fields are added with {!field}. *)

  val field : 't typ -> string -> 'a typ ->
    ('a, (('s, [<`Struct | `Union]) Ctypes_static.structured as 't)) field
  (** [field ty label ty'] adds a field of type [ty'] with label [label] to the
      structure or union type [ty] and returns a field value that can be used to
      read and write the field in structure or union instances (e.g. using
      {!getf} and {!setf}).

      Attempting to add a field to a union type that has been sealed with [seal]
      is an error, and will raise {!ModifyingSealedType}. *)

  val seal : (_, [< `Struct | `Union]) Ctypes_static.structured typ -> unit
  (** [seal t] completes the struct or union type [t] so that no further fields
      can be added.  Struct and union types must be sealed before they can be used
      in a way that involves their size or alignment; see the documentation for
      {!IncompleteType} for further details.  *)

  (** {3 View types} *)

  val view : ?format_typ:((Format.formatter -> unit) -> Format.formatter -> unit) ->
             ?format:(Format.formatter -> 'b -> unit) ->
             read:('a -> 'b) -> write:('b -> 'a) -> 'a typ -> 'b typ
  (** [view ~read:r ~write:w t] creates a C type representation [t'] which
      behaves like [t] except that values read using [t'] are subsequently
      transformed using the function [r] and values written using [t'] are first
      transformed using the function [w].

      For example, given suitable definitions of [string_of_char_ptr] and
      [char_ptr_of_string], the type representation

      [view ~read:string_of_char_ptr ~write:char_ptr_of_string (ptr char)]

      can be used to pass OCaml strings directly to and from bound C functions,
      or to read and write string members in structs and arrays.  (In fact, the
      {!string} type representation is defined in exactly this way.)

      The optional argument [format_typ] is used by the {!Ctypes.format_typ} and
      {!string_of_typ} functions to print the type at the top level and
      elsewhere.  If [format_typ] is not supplied the printer for [t] is used
      instead.

      The optional argument [format] is used by the {!Ctypes.format}
      and {!string_of} functions to print the values. If [format_val]
      is not supplied the printer for [t] is used instead.

  *)

  val typedef : 'a typ -> string -> 'a typ
  (** [typedef t name] creates a C type representation [t'] which
      is equivalent to [t] except its name is printed as [name].

      This is useful when generating C stubs involving "anonymous" types, for
      example: [typedef struct { int f } typedef_name;]
  *)

  (** {3 Abstract types} *)

  val abstract : name:string -> size:int -> alignment:int -> 'a Ctypes_static.abstract typ
  (** Create an abstract type specification from the size and alignment
      requirements for the type. *)

  (** {3 Injection of concrete types} *)

  val lift_typ : 'a Ctypes_static.typ -> 'a typ
  (** [lift_typ t] turns a concrete type representation into an abstract type
      representation.

      For example, retrieving struct layout from C involves working with an
      abstract representation of types which do not support operations such as
      [sizeof].  The [lift_typ] function makes it possible to use concrete
      type representations wherever such abstract type representations are
      needed. *)

  (** {3 Function types} *)
  (** Abstract interface to C function type descriptions *)

  type 'a fn = 'a Ctypes_static.fn
  (** The type of values representing C function types.  A value of type [t fn]
      can be used to bind to C functions and to describe type of OCaml functions
      passed to C. *)

  val ( @-> ) : 'a typ -> 'b fn -> ('a -> 'b) fn
  (** Construct a function type from a type and an existing function type.  This
      corresponds to prepending a parameter to a C function parameter list.  For
      example,

      [int @-> ptr void @-> returning float]

      describes a function type that accepts two arguments -- an integer and a
      pointer to void -- and returns a float.
  *)

  val returning : 'a typ -> 'a fn
  (** Give the return type of a C function.  Note that [returning] is intended
      to be used together with {!(@->)}; see the documentation for {!(@->)} for an
      example. *)

  (** {3 Function pointer types} *)
  type 'a static_funptr = 'a Ctypes_static.static_funptr
  (** The type of values representing C function pointer types. *)

  val static_funptr : 'a fn -> 'a Ctypes_static.static_funptr typ
  (** Construct a function pointer type from an existing function type
      (called the {i reference type}).  *)
end

end
module Ctypes_value_printing_stubs
= struct
#1 "ctypes_value_printing_stubs.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Stubs for formatting C values. *)

(* Return a string representation of a C value *)
external string_of_prim : 'a Ctypes_primitive_types.prim -> 'a -> string
  = "ctypes_string_of_prim"

external string_of_pointer : _ Ctypes_ptr.Fat.t -> string
  = "ctypes_string_of_pointer"

end
module Ctypes_value_printing
= struct
#1 "ctypes_value_printing.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

open Ctypes_static
open Ctypes_memory

let rec format : type a. a typ -> Format.formatter -> a -> unit
  = fun typ fmt v -> match typ with
    Void -> Format.pp_print_string fmt ""
  | Primitive p ->
    Format.pp_print_string fmt (Ctypes_value_printing_stubs.string_of_prim p v)
  | Pointer _ -> format_ptr fmt v
  | Funptr _ -> format_funptr fmt v
  | Struct _ -> format_structured fmt v
  | Union _ -> format_structured fmt v
  | Array (a, n) -> format_array fmt v
  | Bigarray ba -> Format.fprintf fmt "<bigarray %a>"
    (fun fmt -> Ctypes_type_printing.format_typ fmt) typ
  | Abstract _ -> format_structured fmt v
  | OCaml _ -> format_ocaml fmt v
  | View {write; ty; format=f} ->
    begin match f with
      | None -> format ty fmt (write v)
      | Some f -> f fmt v
    end
and format_structured : type a b. Format.formatter -> (a, b) structured -> unit
  = fun fmt ({structured = CPointer p} as s) ->
    let open Format in
    match Ctypes_ptr.Fat.reftype p with
    | Struct {fields} ->
      fprintf fmt "{@;<1 2>@[";
      format_fields "," fields fmt s;
      fprintf fmt "@]@;<1 0>}"
    | Union {ufields} ->
      fprintf fmt "{@;<1 2>@[";
      format_fields " |" ufields fmt s;
      fprintf fmt "@]@;<1 0>}"
    | Abstract abs ->
      pp_print_string fmt "<abstract>"
    | _ -> raise (Unsupported "unknown structured type")
and format_array : type a. Format.formatter -> a carray -> unit
  = fun fmt ({astart = CPointer p; alength} as arr) ->
    let open Format in
    fprintf fmt "{@;<1 2>@[";
    for i = 0 to alength - 1 do
      format (Ctypes_ptr.Fat.reftype p) fmt (CArray.get arr i);
      if i <> alength - 1 then
        fprintf fmt ",@;"
    done;
    fprintf fmt "@]@;<1 0>}"
and format_ocaml : type a. Format.formatter -> a ocaml -> unit =
  let offset fmt = function
    | 0 -> ()
    | n -> Format.fprintf fmt "@ @[[offset:%d]@]" n
  and float_array fmt arr =
    Format.fprintf fmt "[|@;<1 2>@[";
    let len = Array.length arr in
    for i = 0 to len - 1 do
      Format.pp_print_float fmt arr.(i);
      if i <> len - 1 then
        Format.fprintf fmt ",@;"
    done;
    Format.fprintf fmt "@]@;<1 0>|]"
  in
  fun fmt (OCamlRef (off, obj, ty)) -> match ty with
  | String -> Format.fprintf fmt "%S%a" obj offset off
  | Bytes -> Format.fprintf fmt "%S%a" (Bytes.to_string obj) offset off
  | FloatArray -> Format.fprintf fmt "%a%a" float_array obj offset off
and format_fields : type a b. string -> (a, b) structured boxed_field list ->
                              Format.formatter -> (a, b) structured -> unit
  = fun sep fields fmt s ->
    let last_field = List.length fields - 1 in
    let open Format in
    List.iteri
      (fun i (BoxedField ({ftype; foffset; fname} as f)) ->
        fprintf fmt "@[%s@] = @[%a@]%s@;" fname (format ftype) (getf s f)
          (if i <> last_field then sep else ""))
      fields
and format_ptr : type a. Format.formatter -> a ptr -> unit
  = fun fmt (CPointer p) ->
    Format.fprintf fmt "%s" (Ctypes_value_printing_stubs.string_of_pointer p)
and format_funptr  : type a. Format.formatter -> a static_funptr -> unit
  = fun fmt (Static_funptr p) ->
    Format.fprintf fmt "%s" (Ctypes_value_printing_stubs.string_of_pointer p)

let string_of typ v = Format.asprintf "%a" (format typ) v

end
module Ctypes : sig 
#1 "ctypes.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** The core ctypes module.

    The main points of interest are the set of functions for describing C
    types (see {!types}) and the set of functions for accessing C values (see
    {!values}).  The {!Foreign.foreign} function uses C type descriptions
    to bind external C values.
*)

(** {4:pointer_types Pointer types} *)

type ('a, 'b) pointer = ('a, 'b) Ctypes_static.pointer
(** The type of pointer values. A value of type [('a, [`C]) pointer] contains
    a C-compatible pointer, and a value of type [('a, [`OCaml]) pointer]
    contains a pointer to a value that can be moved by OCaml runtime. *)

(** {4 C-compatible pointers} *)

type 'a ptr = ('a, [`C]) pointer
(** The type of C-compatible pointer values.  A value of type [t ptr] can be
    used to read and write values of type [t] at particular addresses. *)

type 'a ocaml = 'a Ctypes_static.ocaml
(** The type of pointer values pointing directly into OCaml values.
    {b Pointers of this type should never be captured by external code}.
    In particular, functions accepting ['a ocaml] pointers must not invoke
    any OCaml code. *)

(** {4 C array types} *)

type 'a carray = 'a Ctypes_static.carray
(** The type of C array values.  A value of type [t carray] can be used to read
    and write array objects in C-managed storage. *)

(** {4 Bigarray types} *)

type 'a bigarray_class = 'a Ctypes_static.bigarray_class
(** The type of Bigarray classes.  There are four instances, one for each of
    the Bigarray submodules. *)

val genarray :
  < element: 'a;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Genarray.t;
    carray: 'a carray;
    dims: int array > bigarray_class
(** The class of {!Bigarray.Genarray.t} values *)

val array1 :
  < element: 'a;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array1.t;
    carray: 'a carray;
    dims: int > bigarray_class
(** The class of {!Bigarray.Array1.t} values *)

val array2 :
  < element: 'a;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array2.t;
    carray: 'a carray carray;
    dims: int * int > bigarray_class
(** The class of {!Bigarray.Array2.t} values *)

val array3 :
  < element: 'a;
    ba_repr: 'b;
    bigarray: ('a, 'b, Bigarray.c_layout) Bigarray.Array3.t;
    carray: 'a carray carray carray;
    dims: int * int * int > bigarray_class
(** The class of {!Bigarray.Array3.t} values *)

(** {3 Struct and union types} *)

type ('a, 'kind) structured = ('a, 'kind) Ctypes_static.structured
(** The base type of values representing C struct and union types.  The
    ['kind] parameter is a polymorphic variant type indicating whether the type
    represents a struct ([`Struct]) or a union ([`Union]). *)

type 'a structure = ('a, [`Struct]) structured
(** The type of values representing C struct types. *)

type 'a union = ('a, [`Union]) structured
(** The type of values representing C union types. *)

type ('a, 't) field = ('a, 't) Ctypes_static.field
(** The type of values representing C struct or union members (called "fields"
    here).  A value of type [(a, s) field] represents a field of type [a] in a
    struct or union of type [s]. *)

type 'a abstract = 'a Ctypes_static.abstract
(** The type of abstract values.  The purpose of the [abstract] type is to
    represent values whose type varies from platform to platform.

    For example, the type [pthread_t] is a pointer on some platforms, an
    integer on other platforms, and a struct on a third set of platforms.  One
    way to deal with this kind of situation is to have
    possibly-platform-specific code which interrogates the C type in some way
    to help determine an appropriate representation.  Another way is to use
    [abstract], leaving the representation opaque.

    (Note, however, that although [pthread_t] is a convenient example, since
    the type used to implement it varies significantly across platforms, it's
    not actually a good match for [abstract], since values of type [pthread_t]
    are passed and returned by value.) *)

include Ctypes_types.TYPE
 with type 'a typ = 'a Ctypes_static.typ
  and type ('a, 's) field := ('a, 's) field

(** {3 Operations on types} *)

val sizeof : 'a typ -> int
(** [sizeof t] computes the size in bytes of the type [t].  The exception
    {!IncompleteType} is raised if [t] is incomplete. *)

val alignment : 'a typ -> int
(** [alignment t] computes the alignment requirements of the type [t].  The
    exception {!IncompleteType} is raised if [t] is incomplete. *)

val format_typ : ?name:string -> Format.formatter -> 'a typ -> unit
(** Pretty-print a C representation of the type to the specified formatter. *)

val format_fn : ?name:string -> Format.formatter -> 'a fn -> unit
(** Pretty-print a C representation of the function type to the specified
    formatter. *)

val string_of_typ : ?name:string -> 'a typ -> string
(** Return a C representation of the type. *)

val string_of_fn : ?name:string -> 'a fn -> string
(** Return a C representation of the function type. *)

(** {2:values Values representing C values} *)

val format : 'a typ -> Format.formatter -> 'a -> unit
(** Pretty-print a representation of the C value to the specified formatter. *)

val string_of : 'a typ -> 'a -> string
(** Return a string representation of the C value. *)

(** {3 Pointer values} *)

val null : unit ptr
(** A null pointer. *)

val (!@) : 'a ptr -> 'a
(** [!@ p] dereferences the pointer [p].  If the reference type is a scalar
    type then dereferencing constructs a new value.  If the reference type is
    an aggregate type then dereferencing returns a value that references the
    memory pointed to by [p]. *)

val (<-@) : 'a ptr -> 'a -> unit
(** [p <-@ v] writes the value [v] to the address [p]. *)

val (+@) : ('a, 'b) pointer -> int -> ('a, 'b) pointer
(** If [p] is a pointer to an array element then [p +@ n] computes the
    address of the [n]th next element. *)

val (-@) : ('a, 'b) pointer -> int -> ('a, 'b) pointer
(** If [p] is a pointer to an array element then [p -@ n] computes the address
    of the nth previous element. *)

val ptr_diff : ('a, 'b) pointer -> ('a, 'b) pointer -> int
(** [ptr_diff p q] computes [q - p].  As in C, both [p] and [q] must point
    into the same array, and the result value is the difference of the
    subscripts of the two array elements. *)

val from_voidp : 'a typ -> unit ptr -> 'a ptr
(** Conversion from [void *]. *)

val to_voidp : _ ptr -> unit ptr
(** Conversion to [void *]. *)

val allocate : ?finalise:('a ptr -> unit) -> 'a typ -> 'a -> 'a ptr
(** [allocate t v] allocates a fresh value of type [t], initialises it
    with [v] and returns its address.  The argument [?finalise], if
    present, will be called just before the memory is freed.  The value
    will be automatically freed after no references to the pointer
    remain within the calling OCaml program. *)

val allocate_n : ?finalise:('a ptr -> unit) -> 'a typ -> count:int -> 'a ptr
(** [allocate_n t ~count:n] allocates a fresh array with element type
    [t] and length [n], and returns its address.  The argument
    [?finalise], if present, will be called just before the memory is
    freed.  The array will be automatically freed after no references
    to the pointer remain within the calling OCaml program.  The
    memory is allocated with libc's [calloc] and is guaranteed to be
    zero-filled.  *)

val ptr_compare : 'a ptr -> 'a ptr -> int
(** If [p] and [q] are pointers to elements [i] and [j] of the same array then
    [ptr_compare p q] compares the indexes of the elements.  The result is
    negative if [i] is less than [j], positive if [i] is greater than [j], and
    zero if [i] and [j] are equal. *)

val reference_type : 'a ptr -> 'a typ
(** Retrieve the reference type of a pointer. *)

val ptr_of_raw_address : nativeint -> unit ptr
(** Convert the numeric representation of an address to a pointer *)

val funptr_of_raw_address : nativeint -> (unit -> unit) Ctypes_static.static_funptr
(** Convert the numeric representation of an address to a function pointer *)

val raw_address_of_ptr : unit ptr -> nativeint
(** [raw_address_of_ptr p] returns the numeric representation of p.

    Note that the return value remains valid only as long as the pointed-to
    object is alive.  If [p] is a managed object (e.g. a value returned by
    {!make}) then unless the caller retains a reference to [p], the object may
    be collected, invalidating the returned address. *)

val string_from_ptr : char ptr -> length:int -> string
(** [string_from_ptr p ~length] creates a string initialized with the [length]
    characters at address [p].

    Raise [Invalid_argument "Ctypes.string_from_ptr"] if [length] is
    negative. *)

val ocaml_string_start : string -> string ocaml
(** [ocaml_string_start s] allows to pass a pointer to the contents of an OCaml
    string directly to a C function. *)

val ocaml_bytes_start : Bytes.t -> Bytes.t ocaml
(** [ocaml_bytes_start s] allows to pass a pointer to the contents of an OCaml
    byte array directly to a C function. *)

(** {3 Array values} *)

(** {4 C array values} *)

module CArray :
sig
  type 'a t = 'a carray

  val get : 'a t -> int -> 'a
  (** [get a n] returns the [n]th element of the zero-indexed array [a].  The
      semantics for non-scalar types are non-copying, as for {!(!@)}.

      If you rebind the [CArray] module to [Array] then you can also use the
      syntax [a.(n)] instead of [Array.get a n].

      Raise [Invalid_argument "index out of bounds"] if [n] is outside of the
      range [0] to [(CArray.length a - 1)]. *)

  val set : 'a t -> int -> 'a -> unit
  (** [set a n v] overwrites the [n]th element of the zero-indexed array [a]
      with [v].

      If you rebind the [CArray] module to [Array] then you can also use the
      [a.(n) <- v] syntax instead of [Array.set a n v].

      Raise [Invalid_argument "index out of bounds"] if [n] is outside of the
      range [0] to [(CArray.length a - 1)]. *)

  val unsafe_get : 'a t -> int -> 'a
  (** [unsafe_get a n] behaves like [get a n] except that the check that [n]
      between [0] and [(CArray.length a - 1)] is not performed. *)

  val unsafe_set : 'a t -> int -> 'a -> unit
  (** [unsafe_set a n v] behaves like [set a n v] except that the check that
      [n] between [0] and [(CArray.length a - 1)] is not performed. *)

  val of_list : 'a typ -> 'a list -> 'a t
  (** [of_list t l] builds an array of type [t] of the same length as [l], and
      writes the elements of [l] to the corresponding elements of the array. *)

  val to_list : 'a t -> 'a list
  (** [to_list a] builds a list of the same length as [a] such that each
      element of the list is the result of reading the corresponding element of
      [a]. *)

  val length : 'a t -> int
  (** Return the number of elements of the given array. *)

  val start : 'a t -> 'a ptr
  (** Return the address of the first element of the given array. *)

  val from_ptr : 'a ptr -> int -> 'a t
  (** [from_ptr p n] creates an [n]-length array reference to the memory at
      address [p]. *)

  val make : ?finalise:('a t -> unit) -> 'a typ -> ?initial:'a -> int -> 'a t
  (** [make t n] creates an [n]-length array of type [t].  If the optional
      argument [?initial] is supplied, it indicates a value that should be
      used to initialise every element of the array.  The argument [?finalise],
      if present, will be called just before the memory is freed. *)

  val element_type : 'a t -> 'a typ
(** Retrieve the element type of an array. *)
end
(** Operations on C arrays. *)

(** {4 Bigarray values} *)

val bigarray_start : < element: 'a;
                       ba_repr: _;
                       bigarray: 'b;
                       carray: _;
                       dims: _ > bigarray_class -> 'b -> 'a ptr
(** Return the address of the first element of the given Bigarray value. *)

val bigarray_of_ptr : < element: 'a;
                        ba_repr: 'f;
                        bigarray: 'b;
                        carray: _;
                        dims: 'i > bigarray_class ->
    'i -> ('a, 'f) Bigarray.kind -> 'a ptr -> 'b
(** [bigarray_of_ptr c dims k p] converts the C pointer [p] to a bigarray
    value.  No copy is made; the bigarray references the memory pointed to by
    [p]. *)

val array_of_bigarray : < element: _;
                          ba_repr: _;
                          bigarray: 'b;
                          carray: 'c;
                          dims: _ > bigarray_class -> 'b -> 'c
(** [array_of_bigarray c b] converts the bigarray value [b] to a value of type
    {!CArray.t}.  No copy is made; the result occupies the same memory as
    [b]. *)

(** Convert a Bigarray value to a C array. *)

val bigarray_of_array : < element: 'a;
                          ba_repr: 'f;
                          bigarray: 'b;
                          carray: 'c carray;
                          dims: 'i > bigarray_class ->
    ('a, 'f) Bigarray.kind -> 'c carray -> 'b
(** [bigarray_of_array c k a] converts the {!CArray.t} value [a] to a bigarray
    value.  No copy is made; the result occupies the same memory as [a]. *)

(** {3 Struct and union values} *)

val make : ?finalise:('s -> unit) -> ((_, _) structured as 's) typ -> 's
(** Allocate a fresh, uninitialised structure or union value.  The argument
    [?finalise], if present, will be called just before the underlying memory is
    freed. *)

val setf : ((_, _) structured as 's) -> ('a, 's) field -> 'a -> unit
(** [setf s f v] overwrites the value of the field [f] in the structure or
    union [s] with [v]. *)

val getf : ((_, _) structured as 's) -> ('a, 's) field -> 'a
(** [getf s f] retrieves the value of the field [f] in the structure or union
    [s].  The semantics for non-scalar types are non-copying, as for
    {!(!@)}.*)

val (@.) : ((_, _) structured as 's) -> ('a, 's) field -> 'a ptr
(** [s @. f] computes the address of the field [f] in the structure or union
    value [s]. *)

val (|->) : ((_, _) structured as 's) ptr -> ('a, 's) field -> 'a ptr
(** [p |-> f] computes the address of the field [f] in the structure or union
    value pointed to by [p]. *)

val offsetof : (_, _ structure) field -> int
(** [offsetof f] returns the offset, in bytes, of the field [f] from the
    beginning of the associated struct type. *)

val field_type : ('a, _) field -> 'a typ
(** [field_type f] returns the type of the field [f]. *)

val field_name : (_, _) field -> string
(** [field_name f] returns the name of the field [f]. *)

val addr : ((_, _) structured as 's) -> 's ptr
(** [addr s] returns the address of the structure or union [s]. *)

(** {3 Coercions} *)

val coerce : 'a typ -> 'b typ -> 'a -> 'b
(** [coerce t1 t2] returns a coercion function between the types represented
    by [t1] and [t2].  If [t1] cannot be coerced to [t2], [coerce] raises
    {!Uncoercible}.

    The following coercions are currently supported:

     - All function and object pointer types are intercoercible.
     - Any type may be coerced to {!void}
     - There is a coercion between a {!view} and another type [t] (in either
       direction) if there is a coercion between the representation type
       underlying the view and [t].
     - Coercion is transitive: if [t1] is coercible to [t2] and [t2] is
       coercible to [t3], then [t1] is directly coercible to [t3].

    The set of supported coercions is subject to change.  Future versions of
    ctypes may both add new types of coercion and restrict the existing
    coercions. *)

val coerce_fn : 'a fn -> 'b fn -> 'a -> 'b
(** [coerce_fn f1 f2] returns a coercion function between the function
    types represented by [f1] and [f2].  If [f1] cannot be coerced to
    [f2], [coerce_fn] raises {!Uncoercible}.

    A function type [f1] may be coerced to another function type [f2]
    if all of the following hold:

      - the C types described by [f1] and [f2] have the same arity

      - each argument of [f2] may be coerced to the corresponding
        argument of [f1]

      - the return type of [f1] may be coerced to the return type of [f2]

    The set of supported coercions is subject to change.  Future versions of
    ctypes may both add new types of coercion and restrict the existing
    coercions. *)

(** {2:roots Registration of OCaml values as roots} *)
module Root :
sig
  val create : 'a -> unit ptr
  (** [create v] allocates storage for the address of the OCaml value [v],
      registers the storage as a root, and returns its address. *)

  val get : unit ptr -> 'a
  (** [get p] retrieves the OCaml value whose address is stored at [p]. *)

  val set : unit ptr -> 'a -> unit
  (** [set p v] updates the OCaml value stored as a root at [p]. *)

  val release : unit ptr -> unit
  (** [release p] unregsiters the root [p]. *)
end

(** {2 Exceptions} *)

exception Unsupported of string
(** An attempt was made to use a feature not currently supported by ctypes.
    In practice this refers to attempts to use an union, array or abstract
    type as an argument or return type of a function. *)

exception ModifyingSealedType of string
(** An attempt was made to modify a sealed struct or union type
    description.  *)

exception IncompleteType
(** An attempt was made to compute the size or alignment of an incomplete
    type.

    The incomplete types are struct and union types that have not been sealed,
    and the void type.

    It is not permitted to compute the size or alignment requirements of an
    incomplete type, to use it as a struct or union member, to read or write a
    value of the type through a pointer or to use it as the referenced type in
    pointer arithmetic.  Additionally, incomplete struct and union types
    cannot be used as argument or return types.
*)

type uncoercible_info
exception Uncoercible of uncoercible_info
(** An attempt was made to coerce between uncoercible types.  *)

end = struct
#1 "ctypes.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

include Ctypes_static

include Ctypes_structs_computed

include Ctypes_type_printing

include Ctypes_memory

include Ctypes_std_views

include Ctypes_value_printing

include Ctypes_coerce

let lift_typ x = x

end
module Ctypes_closure_properties : sig 
#1 "ctypes_closure_properties.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

module type MUTEX =
sig
  type t
  val create : unit -> t
  val lock : t -> unit
  val try_lock : t -> bool
  val unlock : t -> unit
end

module Make (Mutex : MUTEX) :
sig
  val record : Obj.t -> Obj.t -> int
  (** [record c v] links the lifetimes of [c] and [v], ensuring that [v] is not
      collected while [c] is still live.  The return value is a key
      that can be used to retrieve [v] while [v] is still live. *)

  val retrieve : int -> Obj.t
  (** [retrieve v] retrieves a value using a key returned by [record], or raises
      [Not_found] if [v] is no longer live. *)
end

end = struct
#1 "ctypes_closure_properties.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

module type MUTEX =
sig
  type t
  val create : unit -> t
  val lock : t -> unit
  val try_lock : t -> bool
  val unlock : t -> unit
end

module HashPhysical = Hashtbl.Make
  (struct
    type t = Obj.t
    let hash = Hashtbl.hash
    let equal = (==)
   end)

module Make (Mutex : MUTEX) = struct

  (* Map integer identifiers to functions. *)
  let function_by_id : (int, Obj.t) Hashtbl.t = Hashtbl.create 10

  (* Map functions (not closures) to identifiers. *)
  let id_by_function : int HashPhysical.t = HashPhysical.create 10

  (* A single mutex guards both tables *)
  let tables_lock = Mutex.create ()

  (* (The caller must hold tables_lock) *)
  let store_non_closure_function fn boxed_fn id =
    try
      (* Return the existing identifier, if any. *)
      HashPhysical.find id_by_function fn
    with Not_found ->
      (* Add entries to both tables *)
      HashPhysical.add id_by_function fn id;
      Hashtbl.add function_by_id id boxed_fn;
      id

  let fresh () = Oo.id (object end)

  let finalise key =
    (* GC can be triggered while the lock is already held, in which case we
       abandon the attempt and re-install the finaliser. *)
    let rec cleanup fn =
      begin
        if Mutex.try_lock tables_lock then begin
          Hashtbl.remove function_by_id key;
          Mutex.unlock tables_lock;
        end
        else Gc.finalise cleanup fn;
      end
    in cleanup

  let record closure boxed_closure : int =
    let key = fresh () in
    try
      (* For closures we add an entry to function_by_id and a finaliser that
         removes the entry. *)
      Gc.finalise (finalise key) closure;
      begin
        Mutex.lock tables_lock;
        Hashtbl.add function_by_id key boxed_closure;
        Mutex.unlock tables_lock;
      end;
      key
    with Invalid_argument "Gc.finalise" ->
      (* For non-closures we add entries to function_by_id and
         id_by_function. *)
      begin
        Mutex.lock tables_lock;
        let id = store_non_closure_function closure boxed_closure key in
        Mutex.unlock tables_lock;
        id
      end

  let retrieve id =
    begin
      Mutex.lock tables_lock;
      let f =
        try Hashtbl.find function_by_id id
        with Not_found ->
          Mutex.unlock tables_lock;
          raise Not_found
      in begin
        Mutex.unlock tables_lock;
        f
      end
    end
end

end
module Ctypes_ffi_stubs
= struct
#1 "ctypes_ffi_stubs.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Stubs for binding to libffi. *)

open Ctypes_ptr

(* The type of structure types *)
type 'a ffitype = voidp
type struct_ffitype

external primitive_ffitype : 'a Ctypes_primitive_types.prim -> 'a ffitype
 = "ctypes_primitive_ffitype"

external pointer_ffitype : unit -> voidp ffitype
 = "ctypes_pointer_ffitype"

external void_ffitype : unit -> unit ffitype
 = "ctypes_void_ffitype"


(* Allocate a new C typed buffer specification *)
external allocate_struct_ffitype : int -> struct_ffitype
  = "ctypes_allocate_struct_ffitype"

external struct_type_set_argument : struct_ffitype -> int -> _ ffitype -> unit
  = "ctypes_struct_ffitype_set_argument"

(* Produce a structure type representation from the buffer specification. *)
external complete_struct_type : struct_ffitype -> unit
  = "ctypes_complete_structspec"

external ffi_type_of_struct_type : struct_ffitype -> _ ffitype
  = "ctypes_block_address"

(* A specification of argument C-types and C-return values *)
type callspec

(* Allocate a new C call specification *)
external allocate_callspec : check_errno:bool -> runtime_lock:bool ->
  thread_registration:bool -> callspec
  = "ctypes_allocate_callspec"

(* Add an argument to the C buffer specification *)
external add_argument : callspec -> _ ffitype -> int
  = "ctypes_add_argument"

(* Pass the return type and conclude the specification preparation *)
external prep_callspec : callspec -> int -> _ ffitype -> unit
  = "ctypes_prep_callspec"

(* Call the function specified by `callspec' at the given address.
   The callback functions write the arguments to the buffer and read
   the return value. *)
external call : string -> _ Ctypes_static.fn Fat.t -> callspec ->
  (voidp -> (Obj.t * int) array -> unit) -> (voidp -> 'a) -> 'a
  = "ctypes_call"


(* nary callbacks *)
type boxedfn =
  | Done of (voidp -> unit) * callspec
  | Fn of (voidp -> boxedfn)

type funptr_handle

(* Construct a pointer to an OCaml function represented by an identifier *)
external make_function_pointer : callspec -> int -> funptr_handle
  = "ctypes_make_function_pointer"

external raw_address_of_function_pointer : funptr_handle -> voidp
  = "ctypes_raw_address_of_function_pointer"

(* Set the function used to retrieve functions by identifier. *)
external set_closure_callback : (int -> Obj.t) -> unit
  = "ctypes_set_closure_callback"


(* An internal error: for example, an `ffi_type' object passed to ffi_prep_cif
   was incorrect. *)
exception Ffi_internal_error of string
let () = Callback.register_exception "FFI_internal_error"
  (Ffi_internal_error "")

(* A closure passed to C was collected by the OCaml garbage collector before
   it was called. *)
exception CallToExpiredClosure
let () = Callback.register_exception "CallToExpiredClosure"
  CallToExpiredClosure

end
module Ctypes_weak_ref : sig 
#1 "ctypes_weak_ref.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** A single-cell variant of the weak arrays in the standard library. *)

exception EmptyWeakReference
(** An expired weak reference was accessed. *)

type 'a t
(** The type of weak references.. *)

val make : 'a -> 'a t
(** Obtain a weak reference from a strong reference. *)

val set : 'a t -> 'a -> unit
(** Update a weak reference. *)

val get : 'a t -> 'a
(** Obtain a strong reference from a weak reference. *)

val is_empty : 'a t -> bool
(** Whether a weak reference is still live. *)

end = struct
#1 "ctypes_weak_ref.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

exception EmptyWeakReference

type 'a t = 'a Weak.t

let empty () = raise EmptyWeakReference
let make v = Weak.(let a = create 1 in set a 0 (Some v); a)
let set r v = Weak.set r 0 (Some v)
let get r = match Weak.get r 0 with Some v -> v | None -> empty ()
let is_empty r = Weak.check r 0

end
module Libffi_abi : sig 
#1 "libffi_abi.mli"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** Support for various ABIs. *)

type abi

val aix : abi
val darwin : abi
val eabi : abi
val fastcall : abi
val gcc_sysv : abi
val linux : abi
val linux64 : abi
val linux_soft_float : abi
val ms_cdecl : abi
val n32 : abi
val n32_soft_float : abi
val n64 : abi
val n64_soft_float : abi
val o32 : abi
val o32_soft_float : abi
val osf : abi
val pa32 : abi
val stdcall : abi
val sysv : abi
val thiscall : abi
val unix : abi
val unix64 : abi
val v8 : abi
val v8plus : abi
val v9 : abi
val vfp : abi

val default_abi : abi

val abi_code : abi -> int

end = struct
#1 "libffi_abi.ml"
(*
 * Copyright (c) 2014 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* Support for various ABIs *)

type abi = Code of int | Unsupported of string

let abi_code = function
   Code c -> c
 | Unsupported sym -> raise (Ctypes.Unsupported sym)

let aix = Unsupported "FFI_AIX"
let darwin = Unsupported "FFI_DARWIN"
let eabi = Unsupported "FFI_EABI"
let fastcall = Code 4
let gcc_sysv = Unsupported "FFI_GCC_SYSV"
let linux = Unsupported "FFI_LINUX"
let linux64 = Unsupported "FFI_LINUX64"
let linux_soft_float = Unsupported "FFI_LINUX_SOFT_FLOAT"
let ms_cdecl = Unsupported "FFI_MS_CDECL"
let n32 = Unsupported "FFI_N32"
let n32_soft_float = Unsupported "FFI_N32_SOFT_FLOAT"
let n64 = Unsupported "FFI_N64"
let n64_soft_float = Unsupported "FFI_N64_SOFT_FLOAT"
let o32 = Unsupported "FFI_O32"
let o32_soft_float = Unsupported "FFI_O32_SOFT_FLOAT"
let osf = Unsupported "FFI_OSF"
let pa32 = Unsupported "FFI_PA32"
let stdcall = Code 5
let sysv = Code 1
let thiscall = Code 3
let unix = Unsupported "FFI_UNIX"
let unix64 = Code 2
let v8 = Unsupported "FFI_V8"
let v8plus = Unsupported "FFI_V8PLUS"
let v9 = Unsupported "FFI_V9"
let vfp = Unsupported "FFI_VFP"
let default_abi = Code 2

end
module Ctypes_ffi : sig 
#1 "ctypes_ffi.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

module type CLOSURE_PROPERTIES =
sig
  val record : Obj.t -> Obj.t -> int
  (** [record c v] links the lifetimes of [c] and [v], ensuring that [v] is not
      collected while [c] is still live.  The return value is a key
      that can be used to retrieve [v] while [v] is still live. *)

  val retrieve : int -> Obj.t
  (** [retrieve v] retrieves a value using a key returned by [record], or raises
      [Not_found] if [v] is no longer live. *)
end

module Make(Closure_properties : CLOSURE_PROPERTIES) :
sig
  open Ctypes_static
  open Libffi_abi

  (** Dynamic function calls based on libffi *)

  val function_of_pointer : ?name:string -> abi:abi -> check_errno:bool ->
    release_runtime_lock:bool -> ('a -> 'b) fn -> ('a -> 'b) static_funptr ->
    ('a -> 'b)
  (** Build an OCaml function from a type specification and a pointer to a C
      function. *)

  val pointer_of_function : abi:abi -> acquire_runtime_lock:bool ->
    thread_registration:bool ->
    ('a -> 'b) fn -> ('a -> 'b) -> ('a -> 'b) static_funptr
  (** Build an C function from a type specification and an OCaml function.

      The C function pointer returned is callable as long as the OCaml function
      value is live. *)
end

end = struct
#1 "ctypes_ffi.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

module type CLOSURE_PROPERTIES =
sig
  val record : Obj.t -> Obj.t -> int
  (** [record c v] links the lifetimes of [c] and [v], ensuring that [v] is not
      collected while [c] is still live.  The return value is a key
      that can be used to retrieve [v] while [v] is still live. *)

  val retrieve : int -> Obj.t
  (** [retrieve v] retrieves a value using a key returned by [record], or raises
      [Not_found] if [v] is no longer live. *)
end

module Make(Closure_properties : CLOSURE_PROPERTIES) =
struct

  open Ctypes_static
  open Libffi_abi

  (* Register the closure lookup function with C. *)
  let () = Ctypes_ffi_stubs.set_closure_callback Closure_properties.retrieve

  type _ ccallspec =
      Call : bool * (Ctypes_ptr.voidp -> 'a) -> 'a ccallspec
    | WriteArg : ('a -> Ctypes_ptr.voidp -> (Obj.t * int) array -> unit) * 'b ccallspec ->
                 ('a -> 'b) ccallspec

  type arg_type = ArgType : 'a Ctypes_ffi_stubs.ffitype -> arg_type

  (* keep_alive ties the lifetimes of objects together.

     [keep_alive w ~while_live:v] ensures that [w] is not collected while [v] is
     still live.

     If the object v in the call [keep_alive w ~while_live:v] is
     static -- for example, if it is a top-level function -- then it
     is not possible to attach a finaliser to [v] and [w] should be
     kept alive indefinitely, which we achieve by adding it to the
     list [kept_alive_indefinitely].
  *)
  let kept_alive_indefinitely = ref []
  let keep_alive w ~while_live:v =
    try Gc.finalise (fun _ -> Ctypes_memory_stubs.use_value w; ()) v
    with Invalid_argument "Gc.finalise" ->
      kept_alive_indefinitely := Obj.repr w :: !kept_alive_indefinitely

  let report_unpassable what =
    let msg = Printf.sprintf "libffi does not support passing %s" what in
    raise (Unsupported msg)

  let rec arg_type : type a. a typ -> arg_type = function
    | Void                                -> ArgType (Ctypes_ffi_stubs.void_ffitype ())
    | Primitive p as prim                 -> let ffitype = Ctypes_ffi_stubs.primitive_ffitype p in
                                             if ffitype = Ctypes_ptr.Raw.null
                                             then report_unpassable
                                               (Ctypes_type_printing.string_of_typ prim)
                                             else ArgType ffitype
    | Pointer _                           -> ArgType (Ctypes_ffi_stubs.pointer_ffitype ())
    | Funptr _                            -> ArgType (Ctypes_ffi_stubs.pointer_ffitype ())
    | OCaml _                             -> ArgType (Ctypes_ffi_stubs.pointer_ffitype ())
    | Union _                             -> report_unpassable "unions"
    | Struct ({ spec = Complete _ } as s) -> struct_arg_type s
    | View { ty }                         -> arg_type ty
    | Array _                             -> report_unpassable "arrays"
    | Bigarray _                          -> report_unpassable "bigarrays"
    | Abstract _                          -> (report_unpassable
                                                "values of abstract type")
    (* The following case should never happen; incomplete types are excluded
       during type construction. *)
    | Struct { spec = Incomplete _ }      -> report_unpassable "incomplete types"
  and struct_arg_type : type s. s structure_type -> arg_type =
     fun ({fields} as s) ->
       let bufspec = Ctypes_ffi_stubs.allocate_struct_ffitype (List.length fields) in
       (* Ensure that `bufspec' stays alive as long as the type does. *)
       keep_alive bufspec ~while_live:s;
       List.iteri
         (fun i (BoxedField {ftype; foffset}) ->
           let ArgType t = arg_type ftype in
           Ctypes_ffi_stubs.struct_type_set_argument bufspec i t)
         fields;
       Ctypes_ffi_stubs.complete_struct_type bufspec;
       ArgType (Ctypes_ffi_stubs.ffi_type_of_struct_type bufspec)

  (*
    call addr callspec
     (fun buffer ->
          write arg_1 buffer v_1
          write arg buffer v
          ...
          write arg_n buffer v_n)
     read_return_value
  *)
  let rec invoke : type a b.
    string option ->
    a ccallspec ->
    (Ctypes_ptr.voidp -> (Obj.t * int) array -> unit) list ->
    Ctypes_ffi_stubs.callspec ->
    b fn Ctypes_ptr.Fat.t ->
    a
    = fun name -> function
      | Call (check_errno, read_return_value) ->
        let name = match name with Some name -> name | None -> "" in
        fun writers callspec addr ->
          Ctypes_ffi_stubs.call name addr callspec
            (fun buf arr -> List.iter (fun w -> w buf arr) writers)
            read_return_value
      | WriteArg (write, ccallspec) ->
        let next = invoke name ccallspec in
        fun writers callspec addr v ->
          next (write v :: writers) callspec addr

  let add_argument : type a. Ctypes_ffi_stubs.callspec -> a typ -> int
    = fun callspec -> function
      | Void -> 0
      | ty   -> let ArgType ffitype = arg_type ty in
                Ctypes_ffi_stubs.add_argument callspec ffitype

  let prep_callspec callspec abi ty =
    let ArgType ctype = arg_type ty in
    Ctypes_ffi_stubs.prep_callspec callspec (abi_code abi) ctype

  let rec box_function : type a. abi -> a fn -> Ctypes_ffi_stubs.callspec -> a Ctypes_weak_ref.t ->
      Ctypes_ffi_stubs.boxedfn
    = fun abi fn callspec -> match fn with
      | Returns ty ->
        let () = prep_callspec callspec abi ty in
        let write_rv = Ctypes_memory.write ty in
        fun f ->
          let w = write_rv (Ctypes_weak_ref.get f) in
          Ctypes_ffi_stubs.Done ((fun p -> w (Ctypes_ptr.Fat.make ~reftyp:Void p)),
                          callspec)
      | Function (p, f) ->
        let _ = add_argument callspec p in
        let box = box_function abi f callspec in
        let read = Ctypes_memory.build p in
        fun f -> Ctypes_ffi_stubs.Fn (fun buf ->
          let f' =
            try Ctypes_weak_ref.get f (read (Ctypes_ptr.Fat.make ~reftyp:Void buf))
            with Ctypes_weak_ref.EmptyWeakReference ->
              raise Ctypes_ffi_stubs.CallToExpiredClosure
          in
          let v = box (Ctypes_weak_ref.make f') in
          let () = Gc.finalise (fun _ -> Ctypes_memory_stubs.use_value f') v in
          v)

  let write_arg : type a. a typ -> offset:int -> idx:int -> a ->
                  Ctypes_ptr.voidp -> (Obj.t * int) array -> unit =
    let ocaml_arg elt_size =
      fun ~offset ~idx (OCamlRef (disp, obj, _)) dst mov ->
        mov.(idx) <- (Obj.repr obj, disp * elt_size)
    in function
    | OCaml String     -> ocaml_arg 1
    | OCaml Bytes      -> ocaml_arg 1
    | OCaml FloatArray -> ocaml_arg (Ctypes_primitives.sizeof Ctypes_primitive_types.Double)
    | ty -> (fun ~offset ~idx v dst mov -> Ctypes_memory.write ty v
      (Ctypes_ptr.Fat.(add_bytes (make ~reftyp:Void dst) offset)))

  (*
    callspec = allocate_callspec ()
    add_argument callspec arg1
    add_argument callspec arg2
    ...
    add_argument callspec argn
    prep_callspec callspec rettype
  *)
  let rec build_ccallspec : type a. abi:abi -> check_errno:bool -> ?idx:int -> a fn ->
    Ctypes_ffi_stubs.callspec -> a ccallspec
    = fun ~abi ~check_errno ?(idx=0) fn callspec -> match fn with
      | Returns t ->
        let () = prep_callspec callspec abi t in
        let b = Ctypes_memory.build t in
        Call (check_errno, (fun p -> b (Ctypes_ptr.Fat.make ~reftyp:Void p)))
      | Function (p, f) ->
        let offset = add_argument callspec p in
        let rest = build_ccallspec ~abi ~check_errno ~idx:(idx+1) f callspec in
        WriteArg (write_arg p ~offset ~idx, rest)

  let build_function ?name ~abi ~release_runtime_lock ~check_errno fn =
    let c = Ctypes_ffi_stubs.allocate_callspec ~check_errno
      ~runtime_lock:release_runtime_lock
      ~thread_registration:false
    in
    let e = build_ccallspec ~abi ~check_errno fn c in
    invoke name e [] c

  let funptr_of_rawptr fn raw_ptr =
    Static_funptr (Ctypes_ptr.Fat.make ~reftyp:fn raw_ptr)

  let function_of_pointer ?name ~abi ~check_errno ~release_runtime_lock fn =
    if release_runtime_lock && has_ocaml_argument fn
    then raise (Unsupported "Unsupported argument type when releasing runtime lock")
    else
      let f = build_function ?name ~abi ~check_errno ~release_runtime_lock fn in
      fun (Static_funptr p) -> f p

  let pointer_of_function ~abi ~acquire_runtime_lock ~thread_registration fn =
    let cs' = Ctypes_ffi_stubs.allocate_callspec
      ~check_errno:false
      ~runtime_lock:acquire_runtime_lock
      ~thread_registration
    in
    let cs = box_function abi fn cs' in
    fun f ->
      let boxed = cs (Ctypes_weak_ref.make f) in
      let id = Closure_properties.record (Obj.repr f) (Obj.repr boxed) in
      let funptr = Ctypes_ffi_stubs.make_function_pointer cs' id in
      (* TODO: use a more intelligent strategy for keeping function pointers
         associated with top-level functions alive (e.g. cache function
         pointer creation by (function, type), or possibly even just by
         function, since the C arity and types must be the same in each case.)
         See the note by [kept_alive_indefinitely].  *)
      let () = keep_alive funptr ~while_live:f in
      funptr_of_rawptr fn
        (Ctypes_ffi_stubs.raw_address_of_function_pointer funptr)
end

end
module Dl : sig 
#1 "dl.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** Bindings to the dlopen / dlsym interface. *)

type library
(** The type of dynamic libraries, as returned by {!dlopen}. *)

exception DL_error of string
(** An error condition occurred when calling {!dlopen}, {!dlclose} or
    {!dlsym}.  The argument is the string returned by the [dlerror]
    function. *)

(** Flags for {!dlopen}

Note for windows users: Only [RTLD_NOLOAD] and [RTLD_NODELETE] are supported.
Passing no or any other flags to {!dlopen} will result in standard behaviour:
just LoadLibrary is called. If [RTLD_NOLOAD] is specified and the module is
not already loaded, a {!DL_error} with the string "library not loaded" is
thrown; there is however no test, if such a library exists at all (like under
linux).
*)
type flag = 
    RTLD_LAZY
  | RTLD_NOW
  | RTLD_GLOBAL
  | RTLD_LOCAL
  | RTLD_NODELETE
  | RTLD_NOLOAD
  | RTLD_DEEPBIND

val dlopen : ?filename:string -> flags:flag list -> library
(** Open a dynamic library.

Note for windows users: the filename must be encoded in UTF-8 *)

val dlclose : handle:library -> unit
(** Close a dynamic library. *)

val dlsym : ?handle:library -> symbol:string -> Ctypes_ptr.voidp
(** Look up a symbol in a dynamic library. *)

end = struct
#1 "dl.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

type library

type flag = 
    RTLD_LAZY
  | RTLD_NOW
  | RTLD_GLOBAL
  | RTLD_LOCAL
  | RTLD_NODELETE
  | RTLD_NOLOAD
  | RTLD_DEEPBIND

exception DL_error of string

(* void *dlopen(const char *filename, int flag); *)
external _dlopen : ?filename:string -> flags:int -> library option
  = "ctypes_dlopen"
    
(* void *dlsym(void *handle, const char *symbol); *)
external _dlsym : ?handle:library -> symbol:string -> nativeint option
  = "ctypes_dlsym"

(* int dlclose(void *handle); *)
external _dlclose : handle:library -> int
  = "ctypes_dlclose"

(* char *dlerror(void); *)
external _dlerror : unit -> string option
  = "ctypes_dlerror"

external resolve_flag : flag -> int
  = "ctypes_resolve_dl_flag"

let _report_dl_error noload =
  match _dlerror () with
    | Some error -> raise (DL_error (error))
    | None       ->
      if noload then
        raise (DL_error "library not loaded")
      else
        failwith "dl_error: expected error, but no error reported"

let crush_flags f : 'a list -> int = List.fold_left (fun i o -> i lor (f o)) 0

let dlopen ?filename ~flags =
  match _dlopen ?filename ~flags:(crush_flags resolve_flag flags) with
    | Some library -> library
    | None         -> _report_dl_error (List.mem RTLD_NOLOAD flags)

let dlclose ~handle =
  match _dlclose ~handle with
    | 0 -> ()
    | _ -> _report_dl_error false

let dlsym ?handle ~symbol =
  match _dlsym ?handle ~symbol with
    | Some symbol -> Ctypes_ptr.Raw.of_nativeint symbol
    | None        -> _report_dl_error false

end
module Ctypes_foreign_basis
= struct
#1 "ctypes_foreign_basis.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

module Make(Closure_properties : Ctypes_ffi.CLOSURE_PROPERTIES) =
struct
  open Dl
  open Ctypes

  module Ffi = Ctypes_ffi.Make(Closure_properties)

  exception CallToExpiredClosure = Ctypes_ffi_stubs.CallToExpiredClosure

  let funptr ?(abi=Libffi_abi.default_abi) ?name ?(check_errno=false)
      ?(runtime_lock=false) ?(thread_registration=false) fn =
    let open Ffi in
    let read = function_of_pointer
      ~abi ~check_errno ~release_runtime_lock:runtime_lock ?name fn
    and write = pointer_of_function fn
      ~abi ~acquire_runtime_lock:runtime_lock ~thread_registration in
    Ctypes_static.(view ~read ~write (static_funptr fn))

  let funptr_opt ?abi ?name ?check_errno ?runtime_lock ?thread_registration fn =
    Ctypes_std_views.nullable_funptr_view
      (funptr ?abi ?name ?check_errno ?runtime_lock ?thread_registration fn) fn

  let funptr_of_raw_ptr p = 
    Ctypes.funptr_of_raw_address (Ctypes_ptr.Raw.to_nativeint p)

  let ptr_of_raw_ptr p = 
    Ctypes.ptr_of_raw_address (Ctypes_ptr.Raw.to_nativeint p)

  let foreign_value ?from symbol t =
    from_voidp t (ptr_of_raw_ptr (dlsym ?handle:from ~symbol))

  let foreign ?(abi=Libffi_abi.default_abi) ?from ?(stub=false)
      ?(check_errno=false) ?(release_runtime_lock=false) symbol typ =
    try
      let coerce = Ctypes_coerce.coerce (static_funptr (void @-> returning void))
        (funptr ~abi ~name:symbol ~check_errno ~runtime_lock:release_runtime_lock typ) in
      coerce (funptr_of_raw_ptr (dlsym ?handle:from ~symbol))
    with
    | exn -> if stub then fun _ -> raise exn else raise exn
end

end
module Ctypes_gc_mutex
= struct
#1 "ctypes_gc_mutex.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(* For internal use only, and really only for use with Closure_properties_base.
   A mutex for synchronizing between the GC (i.e. finalisers) and the single
   mutator thread.  Provides very few guarantees.  Since the program is
   single-threaded, there is no waiting; locking either succeeds or fails
   immediately.
*)

exception MutexError of string

type t = { mutable locked: bool }

let create () = { locked = false }

(* the only allocation below is exception raising *) 

let lock m =
  if m.locked then raise (MutexError "Locking locked mutex")
  else m.locked <- true

let try_lock m = 
  if m.locked then false
  else (m.locked <- true; true)

let unlock m = 
  if not m.locked then raise (MutexError "Unlocking unlocked mutex")
  else m.locked <- false

end
module Foreign : sig 
#1 "foreign.mli"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

(** High-level bindings for C functions and values *)

val foreign :
  ?abi:Libffi_abi.abi ->
  ?from:Dl.library ->
  ?stub:bool -> 
  ?check_errno:bool ->
  ?release_runtime_lock:bool ->
  string ->
  ('a -> 'b) Ctypes.fn ->
  ('a -> 'b)
(** [foreign name typ] exposes the C function of type [typ] named by [name] as
    an OCaml value.

    The argument [?from], if supplied, is a library handle returned by
    {!Dl.dlopen}.

    The argument [?stub], if [true] (defaults to [false]), indicates that the
    function should not raise an exception if [name] is not found but return
    an OCaml value that raises an exception when called.

    The value [?check_errno], which defaults to [false], indicates whether
    {!Unix.Unix_error} should be raised if the C function modifies [errno].
    Please note that a function that succeeds is allowed to change errno. So
    use this option with caution.

    The value [?release_runtime_lock], which defaults to [false], indicates
    whether the OCaml runtime lock should be released during the call to the C
    function, allowing other threads to run.  If the runtime lock is released
    then the C function must not access OCaml heap objects, such as arguments
    passed using {!Ctypes.ocaml_string} and {!Ctypes.ocaml_bytes}, and must not
    call back into OCaml.

    @raise Dl.DL_error if [name] is not found in [?from] and [?stub] is
    [false]. *)

val foreign_value : ?from:Dl.library -> string -> 'a Ctypes.typ -> 'a Ctypes.ptr
(** [foreign_value name typ] exposes the C value of type [typ] named by [name]
    as an OCaml value.  The argument [?from], if supplied, is a library handle
    returned by {!Dl.dlopen}.  *)

val funptr :
  ?abi:Libffi_abi.abi ->
  ?name:string ->
  ?check_errno:bool ->
  ?runtime_lock:bool ->
  ?thread_registration:bool ->
  ('a -> 'b) Ctypes.fn ->
  ('a -> 'b) Ctypes.typ
(** Construct a function pointer type from a function type.

    The ctypes library, like C itself, distinguishes functions and function
    pointers.  Functions are not first class: it is not possible to use them
    as arguments or return values of calls, or store them in addressable
    memory.  Function pointers are first class, and so have none of these
    restrictions.

    The value [?check_errno], which defaults to [false], indicates whether
    {!Unix.Unix_error} should be raised if the C function modifies [errno].

    The value [?runtime_lock], which defaults to [false], indicates whether
    the OCaml runtime lock should be released during the call to the C
    function, allowing other threads to run.  If the runtime lock is released
    then the C function must not access OCaml heap objects, such as arguments
    passed using {!Ctypes.ocaml_string} and {!Ctypes.ocaml_bytes}, and must
    not call back into OCaml.  If the function pointer is used to call into
    OCaml from C then the [?runtime_lock] argument indicates whether the lock
    should be acquired and held during the call.

    @raise Dl.DL_error if [name] is not found in [?from] and [?stub] is
    [false]. *)

val funptr_opt :
  ?abi:Libffi_abi.abi ->
  ?name:string ->
  ?check_errno:bool ->
  ?runtime_lock:bool ->
  ?thread_registration:bool ->
  ('a -> 'b) Ctypes.fn ->
  ('a -> 'b) option Ctypes.typ
(** Construct a function pointer type from a function type.

    This behaves like {!funptr}, except that null pointers appear in OCaml as
    [None]. *)

exception CallToExpiredClosure
(** A closure passed to C was collected by the OCaml garbage collector before
    it was called. *)

end = struct
#1 "foreign.ml"
(*
 * Copyright (c) 2013 Jeremy Yallop.
 *
 * This file is distributed under the terms of the MIT License.
 * See the file LICENSE for details.
 *)

include Ctypes_foreign_basis.Make(Ctypes_closure_properties.Make(Ctypes_gc_mutex))

end
module Tgl3 : sig 
#1 "tgl3.mli"
(*---------------------------------------------------------------------------
   Copyright (c) 2013 Daniel C. Bünzli. All rights reserved.
   Distributed under the ISC license, see terms at the end of the file.
   tgls v0.8.4
  ---------------------------------------------------------------------------*)

(* WARNING do not edit. This file was automatically generated with:
   _build/support/apiquery.native -mli -api gl3.3 *)

(** OpenGL 3.x thin bindings.

    [Tgl3] can program core OpenGL 3.2 and 3.3 contexts.
    Consult the {{!conventions}binding conventions}.

    Open the module use it, this defines only the module [Gl]
    in your scope. To use in the toplevel with [findlib],
    just [#require "tgls.tgl3"], it automatically loads the library and
    opens the [Tgl3] module.

    {b References}
    {ul
    {- {{:http://www.opengl.org/registry}OpenGL 3.x}}}

    {e v0.8.4 — OpenGL 3.x — {{:http://erratique.ch/software/tgls }homepage} } *)

(** {1 OpenGL 3.x} *)

(** OpenGL 3.x bindings.
    
    {{!types}Types}, {{!funs}functions} and {{!enums}enumerants}. *)
module Gl : sig

  (** {1:ba Bigarrays} *)

  type ('a, 'b) bigarray = ('a,'b, Bigarray.c_layout) Bigarray.Array1.t

  val bigarray_byte_size : ('a, 'b) bigarray -> int
  (** [bigarray_byte_size ba] is the size of [ba] in bytes. *)

  val string_of_bigarray : (char, Bigarray.int8_unsigned_elt) bigarray -> string
  (** [string_of_bigarray ba] is [ba] until the first ['\x00'], as a string. *)

  (** {1:types Types} *)

  type bitfield = int
  type enum = int
  type enum_bigarray = (int32, Bigarray.int32_elt) bigarray
  type int16 = int
  type sync
  type uint32_bigarray = (int32, Bigarray.int32_elt) bigarray
  type uint64 = int64
  type uint64_bigarray = (int64, Bigarray.int64_elt) bigarray
  type uint8 = int
  type debug_proc = enum -> enum -> int -> enum -> string -> unit
  
  (** {1:funs Functions} *)

  val active_texture : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glActiveTexture.xml}
      [glActiveTexture]} [texture] *)
  
  val attach_shader : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glAttachShader.xml}
      [glAttachShader]} [program shader] *)
  
  val begin_conditional_render : int -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBeginConditionalRender.xml}
      [glBeginConditionalRender]} [id mode] *)
  
  val begin_query : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBeginQuery.xml}
      [glBeginQuery]} [target id] *)
  
  val begin_transform_feedback : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBeginTransformFeedback.xml}
      [glBeginTransformFeedback]} [primitiveMode] *)
  
  val bind_attrib_location : int -> int -> string -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindAttribLocation.xml}
      [glBindAttribLocation]} [program index name] *)
  
  val bind_buffer : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindBuffer.xml}
      [glBindBuffer]} [target buffer] *)
  
  val bind_buffer_base : enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindBufferBase.xml}
      [glBindBufferBase]} [target index buffer] *)
  
  val bind_buffer_range : enum -> int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindBufferRange.xml}
      [glBindBufferRange]} [target index buffer offset size] *)
  
  val bind_frag_data_location : int -> int -> string -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindFragDataLocation.xml}
      [glBindFragDataLocation]} [program color name] *)
  
  val bind_frag_data_location_indexed : int -> int -> int -> string -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindFragDataLocationIndexed.xml}
      [glBindFragDataLocationIndexed]} [program colorNumber index name] *)
  
  val bind_framebuffer : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindFramebuffer.xml}
      [glBindFramebuffer]} [target framebuffer] *)
  
  val bind_renderbuffer : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindRenderbuffer.xml}
      [glBindRenderbuffer]} [target renderbuffer] *)
  
  val bind_sampler : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindSampler.xml}
      [glBindSampler]} [unit sampler] *)
  
  val bind_texture : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindTexture.xml}
      [glBindTexture]} [target texture] *)
  
  val bind_vertex_array : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBindVertexArray.xml}
      [glBindVertexArray]} [array] *)
  
  val blend_color : float -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBlendColor.xml}
      [glBlendColor]} [red green blue alpha] *)
  
  val blend_equation : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBlendEquation.xml}
      [glBlendEquation]} [mode] *)
  
  val blend_equation_separate : enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBlendEquationSeparate.xml}
      [glBlendEquationSeparate]} [modeRGB modeAlpha] *)
  
  val blend_func : enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBlendFunc.xml}
      [glBlendFunc]} [sfactor dfactor] *)
  
  val blend_func_separate : enum -> enum -> enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBlendFuncSeparate.xml}
      [glBlendFuncSeparate]} [sfactorRGB dfactorRGB sfactorAlpha
        dfactorAlpha] *)
  
  val blit_framebuffer : int -> int -> int -> int -> int -> int -> int ->
    int -> bitfield -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBlitFramebuffer.xml}
      [glBlitFramebuffer]} [srcX0 srcY0 srcX1 srcY1 dstX0 dstY0 dstX1 dstY1
        mask filter] *)
  
  val buffer_data : enum -> int -> ('a, 'b) bigarray option -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBufferData.xml}
      [glBufferData]} [target size data usage] *)
  
  val buffer_sub_data : enum -> int -> int -> ('a, 'b) bigarray option ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBufferSubData.xml}
      [glBufferSubData]} [target offset size data] *)
  
  val check_framebuffer_status : enum -> enum
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCheckFramebufferStatus.xml}
      [glCheckFramebufferStatus]} [target] *)
  
  val clamp_color : enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClampColor.xml}
      [glClampColor]} [target clamp] *)
  
  val clear : bitfield -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClear.xml}[glClear]}
        [mask] *)
  
  val clear_bufferfi : enum -> int -> float -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearBuffer.xml}
      [glClearBufferfi]} [buffer drawbuffer depth stencil] *)
  
  val clear_bufferfv : enum -> int ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearBuffer.xml}
      [glClearBufferfv]} [buffer drawbuffer value] *)
  
  val clear_bufferiv : enum -> int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearBuffer.xml}
      [glClearBufferiv]} [buffer drawbuffer value] *)
  
  val clear_bufferuiv : enum -> int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearBuffer.xml}
      [glClearBufferuiv]} [buffer drawbuffer value] *)
  
  val clear_color : float -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearColor.xml}
      [glClearColor]} [red green blue alpha] *)
  
  val clear_depth : float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearDepth.xml}
      [glClearDepth]} [depth] *)
  
  val clear_stencil : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClearStencil.xml}
      [glClearStencil]} [s] *)
  
  val client_wait_sync : sync -> bitfield -> uint64 -> enum
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glClientWaitSync.xml}
      [glClientWaitSync]} [sync flags timeout] *)
  
  val color_mask : bool -> bool -> bool -> bool -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glColorMask.xml}
      [glColorMask]} [red green blue alpha] *)
  
  val color_maski : int -> bool -> bool -> bool -> bool -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glColorMask.xml}
      [glColorMaski]} [index r g b a] *)
  
  val compile_shader : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompileShader.xml}
      [glCompileShader]} [shader] *)
  
  val compressed_tex_image1d : enum -> int -> enum -> int -> int -> int ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompressedTexImage1D.xml}
      [glCompressedTexImage1D]} [target level internalformat width border
        imageSize data] *)
  
  val compressed_tex_image2d : enum -> int -> enum -> int -> int -> int ->
    int -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompressedTexImage2D.xml}
      [glCompressedTexImage2D]} [target level internalformat width height
        border imageSize data] *)
  
  val compressed_tex_image3d : enum -> int -> enum -> int -> int -> int ->
    int -> int -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompressedTexImage3D.xml}
      [glCompressedTexImage3D]} [target level internalformat width height
        depth border imageSize data] *)
  
  val compressed_tex_sub_image1d : enum -> int -> int -> int -> enum ->
    int -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompressedTexSubImage1D.xml}
      [glCompressedTexSubImage1D]} [target level xoffset width format
        imageSize data] *)
  
  val compressed_tex_sub_image2d : enum -> int -> int -> int -> int -> int ->
    enum -> int -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompressedTexSubImage2D.xml}
      [glCompressedTexSubImage2D]} [target level xoffset yoffset width height
        format imageSize data] *)
  
  val compressed_tex_sub_image3d : enum -> int -> int -> int -> int -> int ->
    int -> int -> enum -> int ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCompressedTexSubImage3D.xml}
      [glCompressedTexSubImage3D]} [target level xoffset yoffset zoffset
        width height depth format imageSize data] *)
  
  val copy_buffer_sub_data : enum -> enum -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCopyBufferSubData.xml}
      [glCopyBufferSubData]} [readTarget writeTarget readOffset writeOffset
        size] *)
  
  val copy_tex_image1d : enum -> int -> enum -> int -> int -> int -> int ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCopyTexImage1D.xml}
      [glCopyTexImage1D]} [target level internalformat x y width border] *)
  
  val copy_tex_image2d : enum -> int -> enum -> int -> int -> int -> int ->
    int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCopyTexImage2D.xml}
      [glCopyTexImage2D]} [target level internalformat x y width height
        border] *)
  
  val copy_tex_sub_image1d : enum -> int -> int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCopyTexSubImage1D.xml}
      [glCopyTexSubImage1D]} [target level xoffset x y width] *)
  
  val copy_tex_sub_image2d : enum -> int -> int -> int -> int -> int ->
    int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCopyTexSubImage2D.xml}
      [glCopyTexSubImage2D]} [target level xoffset yoffset x y width height] *)
  
  val copy_tex_sub_image3d : enum -> int -> int -> int -> int -> int ->
    int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCopyTexSubImage3D.xml}
      [glCopyTexSubImage3D]} [target level xoffset yoffset zoffset x y width
        height] *)
  
  val create_program : unit -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCreateProgram.xml}
      [glCreateProgram]} [()] *)
  
  val create_shader : enum -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCreateShader.xml}
      [glCreateShader]} [type_] *)
  
  val cull_face : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glCullFace.xml}
      [glCullFace]} [mode] *)
  
  val delete_buffers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteBuffers.xml}
      [glDeleteBuffers]} [n buffers] *)
  
  val delete_framebuffers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteFramebuffers.xml}
      [glDeleteFramebuffers]} [n framebuffers] *)
  
  val delete_program : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteProgram.xml}
      [glDeleteProgram]} [program] *)
  
  val delete_queries : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteQueries.xml}
      [glDeleteQueries]} [n ids] *)
  
  val delete_renderbuffers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteRenderbuffers.xml}
      [glDeleteRenderbuffers]} [n renderbuffers] *)
  
  val delete_samplers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteSamplers.xml}
      [glDeleteSamplers]} [count samplers] *)
  
  val delete_shader : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteShader.xml}
      [glDeleteShader]} [shader] *)
  
  val delete_sync : sync -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteSync.xml}
      [glDeleteSync]} [sync] *)
  
  val delete_textures : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteTextures.xml}
      [glDeleteTextures]} [n textures] *)
  
  val delete_vertex_arrays : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDeleteVertexArrays.xml}
      [glDeleteVertexArrays]} [n arrays] *)
  
  val depth_func : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDepthFunc.xml}
      [glDepthFunc]} [func] *)
  
  val depth_mask : bool -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDepthMask.xml}
      [glDepthMask]} [flag] *)
  
  val depth_range : float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDepthRange.xml}
      [glDepthRange]} [near far] *)
  
  val detach_shader : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDetachShader.xml}
      [glDetachShader]} [program shader] *)
  
  val disable : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glEnable.xml}[glDisable]}
        [cap] *)
  
  val disable_vertex_attrib_array : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glEnableVertexAttribArray.xml}
      [glDisableVertexAttribArray]} [index] *)
  
  val disablei : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glEnable.xml}[glDisablei]}
        [target index] *)
  
  val draw_arrays : enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawArrays.xml}
      [glDrawArrays]} [mode first count] *)
  
  val draw_arrays_instanced : enum -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawArraysInstanced.xml}
      [glDrawArraysInstanced]} [mode first count instancecount] *)
  
  val draw_buffer : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawBuffer.xml}
      [glDrawBuffer]} [buf] *)
  
  val draw_buffers : int -> enum_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawBuffers.xml}
      [glDrawBuffers]} [n bufs] *)
  
  val draw_elements : enum -> int -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawElements.xml}
      [glDrawElements]} [mode count type_ indices] *)
  
  val draw_elements_base_vertex : enum -> int -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawElementsBaseVertex.xml}
      [glDrawElementsBaseVertex]} [mode count type_ indices basevertex] *)
  
  val draw_elements_instanced : enum -> int -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawElementsInstanced.xml}
      [glDrawElementsInstanced]} [mode count type_ indices instancecount] *)
  
  val draw_elements_instanced_base_vertex : enum -> int -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawElementsInstancedBaseVertex.xml}
      [glDrawElementsInstancedBaseVertex]} [mode count type_ indices
        instancecount basevertex] *)
  
  val draw_range_elements : enum -> int -> int -> int -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawRangeElements.xml}
      [glDrawRangeElements]} [mode start end_ count type_ indices] *)
  
  val draw_range_elements_base_vertex : enum -> int -> int -> int -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glDrawRangeElementsBaseVertex.xml}
      [glDrawRangeElementsBaseVertex]} [mode start end_ count type_ indices
        basevertex] *)
  
  val enable : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glEnable.xml}[glEnable]}
        [cap] *)
  
  val enable_vertex_attrib_array : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glEnableVertexAttribArray.xml}
      [glEnableVertexAttribArray]} [index] *)
  
  val enablei : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glEnable.xml}[glEnablei]}
        [target index] *)
  
  val end_conditional_render : unit -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBeginConditionalRender.xml}
      [glEndConditionalRender]} [()] *)
  
  val end_query : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBeginQuery.xml}
      [glEndQuery]} [target] *)
  
  val end_transform_feedback : unit -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glBeginTransformFeedback.xml}
      [glEndTransformFeedback]} [()] *)
  
  val fence_sync : enum -> bitfield -> sync
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFenceSync.xml}
      [glFenceSync]} [condition flags] *)
  
  val finish : unit -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFinish.xml}[glFinish]}
        [()] *)
  
  val flush : unit -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFlush.xml}[glFlush]}
        [()] *)
  
  val flush_mapped_buffer_range : enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFlushMappedBufferRange.xml}
      [glFlushMappedBufferRange]} [target offset length] *)
  
  val framebuffer_renderbuffer : enum -> enum -> enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFramebufferRenderbuffer.xml}
      [glFramebufferRenderbuffer]} [target attachment renderbuffertarget
        renderbuffer] *)
  
  val framebuffer_texture : enum -> enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFramebufferTexture.xml}
      [glFramebufferTexture]} [target attachment texture level] *)
  
  val framebuffer_texture1d : enum -> enum -> enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFramebufferTexture.xml}
      [glFramebufferTexture1D]} [target attachment textarget texture level] *)
  
  val framebuffer_texture2d : enum -> enum -> enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFramebufferTexture.xml}
      [glFramebufferTexture2D]} [target attachment textarget texture level] *)
  
  val framebuffer_texture3d : enum -> enum -> enum -> int -> int -> int ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFramebufferTexture.xml}
      [glFramebufferTexture3D]} [target attachment textarget texture level
        zoffset] *)
  
  val framebuffer_texture_layer : enum -> enum -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFramebufferTextureLayer.xml}
      [glFramebufferTextureLayer]} [target attachment texture level layer] *)
  
  val front_face : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glFrontFace.xml}
      [glFrontFace]} [mode] *)
  
  val gen_buffers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenBuffers.xml}
      [glGenBuffers]} [n buffers] *)
  
  val gen_framebuffers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenFramebuffers.xml}
      [glGenFramebuffers]} [n framebuffers] *)
  
  val gen_queries : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenQueries.xml}
      [glGenQueries]} [n ids] *)
  
  val gen_renderbuffers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenRenderbuffers.xml}
      [glGenRenderbuffers]} [n renderbuffers] *)
  
  val gen_samplers : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenSamplers.xml}
      [glGenSamplers]} [count samplers] *)
  
  val gen_textures : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenTextures.xml}
      [glGenTextures]} [n textures] *)
  
  val gen_vertex_arrays : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenVertexArrays.xml}
      [glGenVertexArrays]} [n arrays] *)
  
  val generate_mipmap : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGenerateMipmap.xml}
      [glGenerateMipmap]} [target] *)
  
  val get_active_attrib : int -> int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (int32, Bigarray.int32_elt) bigarray -> enum_bigarray ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetActiveAttrib.xml}
      [glGetActiveAttrib]} [program index bufSize length size type_ name] *)
  
  val get_active_uniform : int -> int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (int32, Bigarray.int32_elt) bigarray -> enum_bigarray ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetActiveUniform.xml}
      [glGetActiveUniform]} [program index bufSize length size type_ name] *)
  
  val get_active_uniform_block_name : int -> int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetActiveUniformBlockName.xml}
      [glGetActiveUniformBlockName]} [program uniformBlockIndex bufSize
        length uniformBlockName] *)
  
  val get_active_uniform_blockiv : int -> int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetActiveUniformBlock.xml}
      [glGetActiveUniformBlockiv]} [program uniformBlockIndex pname params] *)
  
  val get_active_uniform_name : int -> int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetActiveUniformName.xml}
      [glGetActiveUniformName]} [program uniformIndex bufSize length
        uniformName] *)
  
  val get_active_uniformsiv : int -> int -> uint32_bigarray -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetActiveUniformsiv.xml}
      [glGetActiveUniformsiv]} [program uniformCount uniformIndices pname
        params] *)
  
  val get_attached_shaders : int -> int ->
    (int32, Bigarray.int32_elt) bigarray option -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetAttachedShaders.xml}
      [glGetAttachedShaders]} [program maxCount count shaders] *)
  
  val get_attrib_location : int -> string -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetAttribLocation.xml}
      [glGetAttribLocation]} [program name] *)
  
  val get_booleani_v : enum -> int ->
    (int, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}
      [glGetBooleani_v]} [target index data] *)
  
  val get_booleanv : enum -> (int, Bigarray.int8_unsigned_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}[glGetBooleanv]}
        [pname data] *)
  
  val get_buffer_parameteri64v : enum -> enum ->
    (int64, Bigarray.int64_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetBufferParameter.xml}
      [glGetBufferParameteri64v]} [target pname params] *)
  
  val get_buffer_parameteriv : enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetBufferParameter.xml}
      [glGetBufferParameteriv]} [target pname params] *)
  
  val get_buffer_pointerv : enum -> enum ->
    (nativeint, Bigarray.nativeint_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetBufferPointerv.xml}
      [glGetBufferPointerv]} [target pname params] *)
  
  val get_buffer_sub_data : enum -> int -> int -> ('a, 'b) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetBufferSubData.xml}
      [glGetBufferSubData]} [target offset size data] *)
  
  val get_compressed_tex_image : enum -> int ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetCompressedTexImage.xml}
      [glGetCompressedTexImage]} [target level img] *)
  
  val get_doublev : enum -> (float, Bigarray.float64_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}[glGetDoublev]}
        [pname data] *)
  
  val get_error : unit -> enum
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetError.xml}
      [glGetError]} [()] *)
  
  val get_floatv : enum -> (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}[glGetFloatv]}
        [pname data] *)
  
  val get_frag_data_index : int -> string -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetFragDataIndex.xml}
      [glGetFragDataIndex]} [program name] *)
  
  val get_frag_data_location : int -> string -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetFragDataLocation.xml}
      [glGetFragDataLocation]} [program name] *)
  
  val get_framebuffer_attachment_parameteriv : enum -> enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetFramebufferAttachmentParameter.xml}
      [glGetFramebufferAttachmentParameteriv]} [target attachment pname
        params] *)
  
  val get_integer64i_v : enum -> int ->
    (int64, Bigarray.int64_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}
      [glGetInteger64i_v]} [target index data] *)
  
  val get_integer64v : enum -> (int64, Bigarray.int64_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}
      [glGetInteger64v]} [pname data] *)
  
  val get_integeri_v : enum -> int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}
      [glGetIntegeri_v]} [target index data] *)
  
  val get_integerv : enum -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGet.xml}[glGetIntegerv]}
        [pname data] *)
  
  val get_multisamplefv : enum -> int ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetMultisample.xml}
      [glGetMultisamplefv]} [pname index val_] *)
  
  val get_program_info_log : int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetProgramInfoLog.xml}
      [glGetProgramInfoLog]} [program bufSize length infoLog] *)
  
  val get_programiv : int -> enum -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetProgram.xml}
      [glGetProgramiv]} [program pname params] *)
  
  val get_query_objecti64v : int -> enum ->
    (int64, Bigarray.int64_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetQueryObject.xml}
      [glGetQueryObjecti64v]} [id pname params] *)
  
  val get_query_objectiv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetQueryObject.xml}
      [glGetQueryObjectiv]} [id pname params] *)
  
  val get_query_objectui64v : int -> enum -> uint64_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetQueryObject.xml}
      [glGetQueryObjectui64v]} [id pname params] *)
  
  val get_query_objectuiv : int -> enum -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetQueryObject.xml}
      [glGetQueryObjectuiv]} [id pname params] *)
  
  val get_queryiv : enum -> enum -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetQueryiv.xml}
      [glGetQueryiv]} [target pname params] *)
  
  val get_renderbuffer_parameteriv : enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetRenderbufferParameter.xml}
      [glGetRenderbufferParameteriv]} [target pname params] *)
  
  val get_sampler_parameter_iiv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetSamplerParameter.xml}
      [glGetSamplerParameterIiv]} [sampler pname params] *)
  
  val get_sampler_parameter_iuiv : int -> enum -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetSamplerParameter.xml}
      [glGetSamplerParameterIuiv]} [sampler pname params] *)
  
  val get_sampler_parameterfv : int -> enum ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetSamplerParameter.xml}
      [glGetSamplerParameterfv]} [sampler pname params] *)
  
  val get_sampler_parameteriv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetSamplerParameter.xml}
      [glGetSamplerParameteriv]} [sampler pname params] *)
  
  val get_shader_info_log : int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetShaderInfoLog.xml}
      [glGetShaderInfoLog]} [shader bufSize length infoLog] *)
  
  val get_shader_source : int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetShaderSource.xml}
      [glGetShaderSource]} [shader bufSize length source] *)
  
  val get_shaderiv : int -> enum -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetShader.xml}
      [glGetShaderiv]} [shader pname params] *)
  
  val get_string : enum -> string option
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetString.xml}
      [glGetString]} [name] *)
  
  val get_stringi : enum -> int -> string option
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetString.xml}
      [glGetStringi]} [name index] *)
  
  val get_synciv : sync -> enum -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetSync.xml}
      [glGetSynciv]} [sync pname bufSize length values] *)
  
  val get_tex_image : enum -> int -> enum -> enum -> ('a, 'b) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexImage.xml}
      [glGetTexImage]} [target level format type_ pixels] *)
  
  val get_tex_level_parameterfv : enum -> int -> enum ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexLevelParameter.xml}
      [glGetTexLevelParameterfv]} [target level pname params] *)
  
  val get_tex_level_parameteriv : enum -> int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexLevelParameter.xml}
      [glGetTexLevelParameteriv]} [target level pname params] *)
  
  val get_tex_parameter_iiv : enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexParameter.xml}
      [glGetTexParameterIiv]} [target pname params] *)
  
  val get_tex_parameter_iuiv : enum -> enum -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexParameter.xml}
      [glGetTexParameterIuiv]} [target pname params] *)
  
  val get_tex_parameterfv : enum -> enum ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexParameter.xml}
      [glGetTexParameterfv]} [target pname params] *)
  
  val get_tex_parameteriv : enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTexParameter.xml}
      [glGetTexParameteriv]} [target pname params] *)
  
  val get_transform_feedback_varying : int -> int -> int ->
    (int32, Bigarray.int32_elt) bigarray option ->
    (int32, Bigarray.int32_elt) bigarray -> enum_bigarray ->
    (char, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetTransformFeedbackVarying.xml}
      [glGetTransformFeedbackVarying]} [program index bufSize length size
        type_ name] *)
  
  val get_uniform_block_index : int -> string -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetUniformBlockIndex.xml}
      [glGetUniformBlockIndex]} [program uniformBlockName] *)
  
  val get_uniform_indices : int -> string list -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetUniformIndices.xml}
      [glGetUniformIndices]} [program uniformNames uniformIndices] *)
  val get_uniform_location : int -> string -> int
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetUniformLocation.xml}
      [glGetUniformLocation]} [program name] *)
  
  val get_uniformfv : int -> int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetUniform.xml}
      [glGetUniformfv]} [program location params] *)
  
  val get_uniformiv : int -> int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetUniform.xml}
      [glGetUniformiv]} [program location params] *)
  
  val get_uniformuiv : int -> int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetUniform.xml}
      [glGetUniformuiv]} [program location params] *)
  
  val get_vertex_attrib_iiv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetVertexAttrib.xml}
      [glGetVertexAttribIiv]} [index pname params] *)
  
  val get_vertex_attrib_iuiv : int -> enum -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetVertexAttrib.xml}
      [glGetVertexAttribIuiv]} [index pname params] *)
  
  val get_vertex_attrib_pointerv : int -> enum ->
    (nativeint, Bigarray.nativeint_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetVertexAttribPointerv.xml}
      [glGetVertexAttribPointerv]} [index pname pointer] *)
  
  val get_vertex_attribdv : int -> enum ->
    (float, Bigarray.float64_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetVertexAttrib.xml}
      [glGetVertexAttribdv]} [index pname params] *)
  
  val get_vertex_attribfv : int -> enum ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetVertexAttrib.xml}
      [glGetVertexAttribfv]} [index pname params] *)
  
  val get_vertex_attribiv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glGetVertexAttrib.xml}
      [glGetVertexAttribiv]} [index pname params] *)
  
  val hint : enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glHint.xml}[glHint]}
        [target mode] *)
  
  val is_buffer : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsBuffer.xml}
      [glIsBuffer]} [buffer] *)
  
  val is_enabled : enum -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsEnabled.xml}
      [glIsEnabled]} [cap] *)
  
  val is_enabledi : enum -> int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsEnabled.xml}
      [glIsEnabledi]} [target index] *)
  
  val is_framebuffer : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsFramebuffer.xml}
      [glIsFramebuffer]} [framebuffer] *)
  
  val is_program : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsProgram.xml}
      [glIsProgram]} [program] *)
  
  val is_query : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsQuery.xml}[glIsQuery]}
        [id] *)
  
  val is_renderbuffer : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsRenderbuffer.xml}
      [glIsRenderbuffer]} [renderbuffer] *)
  
  val is_sampler : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsSampler.xml}
      [glIsSampler]} [sampler] *)
  
  val is_shader : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsShader.xml}
      [glIsShader]} [shader] *)
  
  val is_sync : sync -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsSync.xml}[glIsSync]}
        [sync] *)
  
  val is_texture : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsTexture.xml}
      [glIsTexture]} [texture] *)
  
  val is_vertex_array : int -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glIsVertexArray.xml}
      [glIsVertexArray]} [array] *)
  
  val line_width : float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glLineWidth.xml}
      [glLineWidth]} [width] *)
  
  val link_program : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glLinkProgram.xml}
      [glLinkProgram]} [program] *)
  
  val logic_op : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glLogicOp.xml}[glLogicOp]}
        [opcode] *)
  
  val map_buffer : enum -> int -> enum -> ('a, 'b) Bigarray.kind ->
    ('a, 'b) bigarray
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glMapBuffer.xml}
      [glMapBuffer]} [target length access kind]
  
      {b Note.} [length] is the length, in number of bigarray elements, of the
      mapped buffer.
  
      {b Warning.} The bigarray becomes invalid once the buffer is unmapped and
      program termination may happen if you don't respect the access policy. *)
  
  val map_buffer_range : enum -> int -> int -> enum ->
    ('a, 'b) Bigarray.kind -> ('a, 'b) bigarray
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glMapBufferRange.xml}
      [glMapBufferRange]} [target offset length access kind]
  
      {b Note.} [length] is the length in number of bigarray elements of the
      mapped buffer. [offset] is in bytes.
  
      {b Warning.} The bigarray becomes invalid once the buffer is unmapped and
      program termination may happen if you don't respect the access policy. *)
  
  val multi_draw_arrays : enum -> (int32, Bigarray.int32_elt) bigarray ->
    (int32, Bigarray.int32_elt) bigarray -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glMultiDrawArrays.xml}
      [glMultiDrawArrays]} [mode first count drawcount] *)
  
  val multi_draw_elements : enum -> (int32, Bigarray.int32_elt) bigarray ->
    enum -> ('a, 'b) bigarray -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glMultiDrawElements.xml}
      [glMultiDrawElements]} [mode count type_ indices drawcount]
      
      {b Note.} [indices] are byte offsets in the buffer bound on
      {!Gl.element_array_buffer}. Directly specifiying index arrays is
      unsupported. *)
  
  val multi_draw_elements_base_vertex : enum ->
    (int32, Bigarray.int32_elt) bigarray -> enum -> ('a, 'b) bigarray ->
    int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glMultiDrawElementsBaseVertex.xml}
      [glMultiDrawElementsBaseVertex]} [mode count type_ indices drawcount
        basevertex]
      
      {b Note.} [indices] are byte offsets in the buffer bound on
      {!Gl.element_array_buffer}. Directly specifiying index arrays is
      unsupported. *)
  
  val pixel_storef : enum -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPixelStore.xml}
      [glPixelStoref]} [pname param] *)
  
  val pixel_storei : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPixelStore.xml}
      [glPixelStorei]} [pname param] *)
  
  val point_parameterf : enum -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPointParameter.xml}
      [glPointParameterf]} [pname param] *)
  
  val point_parameterfv : enum -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPointParameter.xml}
      [glPointParameterfv]} [pname params] *)
  
  val point_parameteri : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPointParameter.xml}
      [glPointParameteri]} [pname param] *)
  
  val point_parameteriv : enum -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPointParameter.xml}
      [glPointParameteriv]} [pname params] *)
  
  val point_size : float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPointSize.xml}
      [glPointSize]} [size] *)
  
  val polygon_mode : enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPolygonMode.xml}
      [glPolygonMode]} [face mode] *)
  
  val polygon_offset : float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPolygonOffset.xml}
      [glPolygonOffset]} [factor units] *)
  
  val primitive_restart_index : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glPrimitiveRestartIndex.xml}
      [glPrimitiveRestartIndex]} [index] *)
  
  val provoking_vertex : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glProvokingVertex.xml}
      [glProvokingVertex]} [mode] *)
  
  val query_counter : int -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glQueryCounter.xml}
      [glQueryCounter]} [id target] *)
  
  val read_buffer : enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glReadBuffer.xml}
      [glReadBuffer]} [src] *)
  
  val read_pixels : int -> int -> int -> int -> enum -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glReadPixels.xml}
      [glReadPixels]} [x y width height format type_ pixels] *)
  
  val renderbuffer_storage : enum -> enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glRenderbufferStorage.xml}
      [glRenderbufferStorage]} [target internalformat width height] *)
  
  val renderbuffer_storage_multisample : enum -> int -> enum -> int -> int ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glRenderbufferStorageMultisample.xml}
      [glRenderbufferStorageMultisample]} [target samples internalformat
        width height] *)
  
  val sample_coverage : float -> bool -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSampleCoverage.xml}
      [glSampleCoverage]} [value invert] *)
  
  val sample_maski : int -> bitfield -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSampleMaski.xml}
      [glSampleMaski]} [maskNumber mask] *)
  
  val sampler_parameter_iiv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSamplerParameter.xml}
      [glSamplerParameterIiv]} [sampler pname param] *)
  
  val sampler_parameter_iuiv : int -> enum -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSamplerParameter.xml}
      [glSamplerParameterIuiv]} [sampler pname param] *)
  
  val sampler_parameterf : int -> enum -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSamplerParameter.xml}
      [glSamplerParameterf]} [sampler pname param] *)
  
  val sampler_parameterfv : int -> enum ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSamplerParameter.xml}
      [glSamplerParameterfv]} [sampler pname param] *)
  
  val sampler_parameteri : int -> enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSamplerParameter.xml}
      [glSamplerParameteri]} [sampler pname param] *)
  
  val sampler_parameteriv : int -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glSamplerParameter.xml}
      [glSamplerParameteriv]} [sampler pname param] *)
  
  val scissor : int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glScissor.xml}[glScissor]}
        [x y width height] *)
  
  val shader_source : int -> string -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glShaderSource.xml}
      [glShaderSource]} [shader source] *)
  
  val stencil_func : enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glStencilFunc.xml}
      [glStencilFunc]} [func ref mask] *)
  
  val stencil_func_separate : enum -> enum -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glStencilFuncSeparate.xml}
      [glStencilFuncSeparate]} [face func ref mask] *)
  
  val stencil_mask : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glStencilMask.xml}
      [glStencilMask]} [mask] *)
  
  val stencil_mask_separate : enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glStencilMaskSeparate.xml}
      [glStencilMaskSeparate]} [face mask] *)
  
  val stencil_op : enum -> enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glStencilOp.xml}
      [glStencilOp]} [fail zfail zpass] *)
  
  val stencil_op_separate : enum -> enum -> enum -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glStencilOpSeparate.xml}
      [glStencilOpSeparate]} [face sfail dpfail dppass] *)
  
  val tex_buffer : enum -> enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexBuffer.xml}
      [glTexBuffer]} [target internalformat buffer] *)
  
  val tex_image1d : enum -> int -> int -> int -> int -> enum -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexImage1D.xml}
      [glTexImage1D]} [target level internalformat width border format type_
        pixels] *)
  
  val tex_image2d : enum -> int -> int -> int -> int -> int -> enum ->
    enum -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexImage2D.xml}
      [glTexImage2D]} [target level internalformat width height border format
        type_ pixels] *)
  
  val tex_image2d_multisample : enum -> int -> enum -> int -> int -> bool ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexImage2DMultisample.xml}
      [glTexImage2DMultisample]} [target samples internalformat width height
        fixedsamplelocations] *)
  
  val tex_image3d : enum -> int -> int -> int -> int -> int -> int -> enum ->
    enum -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexImage3D.xml}
      [glTexImage3D]} [target level internalformat width height depth border
        format type_ pixels] *)
  
  val tex_image3d_multisample : enum -> int -> enum -> int -> int -> int ->
    bool -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexImage3DMultisample.xml}
      [glTexImage3DMultisample]} [target samples internalformat width height
        depth fixedsamplelocations] *)
  
  val tex_parameter_iiv : enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexParameter.xml}
      [glTexParameterIiv]} [target pname params] *)
  
  val tex_parameter_iuiv : enum -> enum -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexParameter.xml}
      [glTexParameterIuiv]} [target pname params] *)
  
  val tex_parameterf : enum -> enum -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexParameter.xml}
      [glTexParameterf]} [target pname param] *)
  
  val tex_parameterfv : enum -> enum ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexParameter.xml}
      [glTexParameterfv]} [target pname params] *)
  
  val tex_parameteri : enum -> enum -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexParameter.xml}
      [glTexParameteri]} [target pname param] *)
  
  val tex_parameteriv : enum -> enum ->
    (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexParameter.xml}
      [glTexParameteriv]} [target pname params] *)
  
  val tex_sub_image1d : enum -> int -> int -> int -> enum -> enum ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexSubImage1D.xml}
      [glTexSubImage1D]} [target level xoffset width format type_ pixels] *)
  
  val tex_sub_image2d : enum -> int -> int -> int -> int -> int -> enum ->
    enum -> [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexSubImage2D.xml}
      [glTexSubImage2D]} [target level xoffset yoffset width height format
        type_ pixels] *)
  
  val tex_sub_image3d : enum -> int -> int -> int -> int -> int -> int ->
    int -> enum -> enum -> [ `Offset of int | `Data of ('a, 'b) bigarray ] ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTexSubImage3D.xml}
      [glTexSubImage3D]} [target level xoffset yoffset zoffset width height
        depth format type_ pixels] *)
  
  val transform_feedback_varyings : int -> string list -> enum -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glTransformFeedbackVaryings.xml}
      [glTransformFeedbackVaryings]} [program varyings bufferMode] *)
  val uniform1f : int -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform1f]} [location v0] *)
  
  val uniform1fv : int -> int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform1fv]} [location count value] *)
  
  val uniform1i : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform1i]} [location v0] *)
  
  val uniform1iv : int -> int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform1iv]} [location count value] *)
  
  val uniform1ui : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform1ui]} [location v0] *)
  
  val uniform1uiv : int -> int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform1uiv]} [location count value] *)
  
  val uniform2f : int -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform2f]} [location v0 v1] *)
  
  val uniform2fv : int -> int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform2fv]} [location count value] *)
  
  val uniform2i : int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform2i]} [location v0 v1] *)
  
  val uniform2iv : int -> int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform2iv]} [location count value] *)
  
  val uniform2ui : int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform2ui]} [location v0 v1] *)
  
  val uniform2uiv : int -> int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform2uiv]} [location count value] *)
  
  val uniform3f : int -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform3f]} [location v0 v1 v2] *)
  
  val uniform3fv : int -> int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform3fv]} [location count value] *)
  
  val uniform3i : int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform3i]} [location v0 v1 v2] *)
  
  val uniform3iv : int -> int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform3iv]} [location count value] *)
  
  val uniform3ui : int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform3ui]} [location v0 v1 v2] *)
  
  val uniform3uiv : int -> int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform3uiv]} [location count value] *)
  
  val uniform4f : int -> float -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform4f]} [location v0 v1 v2 v3] *)
  
  val uniform4fv : int -> int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform4fv]} [location count value] *)
  
  val uniform4i : int -> int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform4i]} [location v0 v1 v2 v3] *)
  
  val uniform4iv : int -> int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform4iv]} [location count value] *)
  
  val uniform4ui : int -> int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform4ui]} [location v0 v1 v2 v3] *)
  
  val uniform4uiv : int -> int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniform4uiv]} [location count value] *)
  
  val uniform_block_binding : int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniformBlockBinding.xml}
      [glUniformBlockBinding]} [program uniformBlockIndex
        uniformBlockBinding] *)
  
  val uniform_matrix2fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix2fv]} [location count transpose value] *)
  
  val uniform_matrix2x3fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix2x3fv]} [location count transpose value] *)
  
  val uniform_matrix2x4fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix2x4fv]} [location count transpose value] *)
  
  val uniform_matrix3fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix3fv]} [location count transpose value] *)
  
  val uniform_matrix3x2fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix3x2fv]} [location count transpose value] *)
  
  val uniform_matrix3x4fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix3x4fv]} [location count transpose value] *)
  
  val uniform_matrix4fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix4fv]} [location count transpose value] *)
  
  val uniform_matrix4x2fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix4x2fv]} [location count transpose value] *)
  
  val uniform_matrix4x3fv : int -> int -> bool ->
    (float, Bigarray.float32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUniform.xml}
      [glUniformMatrix4x3fv]} [location count transpose value] *)
  
  val unmap_buffer : enum -> bool
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUnmapBuffer.xml}
      [glUnmapBuffer]} [target] *)
  
  val use_program : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glUseProgram.xml}
      [glUseProgram]} [program] *)
  
  val validate_program : int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glValidateProgram.xml}
      [glValidateProgram]} [program] *)
  
  val vertex_attrib1d : int -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib1d]} [index x] *)
  
  val vertex_attrib1dv : int -> (float, Bigarray.float64_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib1dv]} [index v] *)
  
  val vertex_attrib1f : int -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib1f]} [index x] *)
  
  val vertex_attrib1fv : int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib1fv]} [index v] *)
  
  val vertex_attrib1s : int -> int16 -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib1s]} [index x] *)
  
  val vertex_attrib1sv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib1sv]} [index v] *)
  
  val vertex_attrib2d : int -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib2d]} [index x y] *)
  
  val vertex_attrib2dv : int -> (float, Bigarray.float64_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib2dv]} [index v] *)
  
  val vertex_attrib2f : int -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib2f]} [index x y] *)
  
  val vertex_attrib2fv : int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib2fv]} [index v] *)
  
  val vertex_attrib2s : int -> int16 -> int16 -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib2s]} [index x y] *)
  
  val vertex_attrib2sv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib2sv]} [index v] *)
  
  val vertex_attrib3d : int -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib3d]} [index x y z] *)
  
  val vertex_attrib3dv : int -> (float, Bigarray.float64_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib3dv]} [index v] *)
  
  val vertex_attrib3f : int -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib3f]} [index x y z] *)
  
  val vertex_attrib3fv : int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib3fv]} [index v] *)
  
  val vertex_attrib3s : int -> int16 -> int16 -> int16 -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib3s]} [index x y z] *)
  
  val vertex_attrib3sv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib3sv]} [index v] *)
  
  val vertex_attrib4nbv : int -> (int, Bigarray.int8_signed_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Nbv]} [index v] *)
  
  val vertex_attrib4niv : int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Niv]} [index v] *)
  
  val vertex_attrib4nsv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Nsv]} [index v] *)
  
  val vertex_attrib4nub : int -> uint8 -> uint8 -> uint8 -> uint8 -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Nub]} [index x y z w] *)
  
  val vertex_attrib4nubv : int ->
    (int, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Nubv]} [index v] *)
  
  val vertex_attrib4nuiv : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Nuiv]} [index v] *)
  
  val vertex_attrib4nusv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4Nusv]} [index v] *)
  
  val vertex_attrib4bv : int -> (int, Bigarray.int8_signed_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4bv]} [index v] *)
  
  val vertex_attrib4d : int -> float -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4d]} [index x y z w] *)
  
  val vertex_attrib4dv : int -> (float, Bigarray.float64_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4dv]} [index v] *)
  
  val vertex_attrib4f : int -> float -> float -> float -> float -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4f]} [index x y z w] *)
  
  val vertex_attrib4fv : int -> (float, Bigarray.float32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4fv]} [index v] *)
  
  val vertex_attrib4iv : int -> (int32, Bigarray.int32_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4iv]} [index v] *)
  
  val vertex_attrib4s : int -> int16 -> int16 -> int16 -> int16 -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4s]} [index x y z w] *)
  
  val vertex_attrib4sv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4sv]} [index v] *)
  
  val vertex_attrib4ubv : int ->
    (int, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4ubv]} [index v] *)
  
  val vertex_attrib4uiv : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4uiv]} [index v] *)
  
  val vertex_attrib4usv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttrib4usv]} [index v] *)
  
  val vertex_attrib_divisor : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttribDivisor.xml}
      [glVertexAttribDivisor]} [index divisor] *)
  
  val vertex_attrib_i1i : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI1i]} [index x] *)
  
  val vertex_attrib_i1iv : int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI1iv]} [index v] *)
  
  val vertex_attrib_i1ui : int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI1ui]} [index x] *)
  
  val vertex_attrib_i1uiv : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI1uiv]} [index v] *)
  
  val vertex_attrib_i2i : int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI2i]} [index x y] *)
  
  val vertex_attrib_i2iv : int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI2iv]} [index v] *)
  
  val vertex_attrib_i2ui : int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI2ui]} [index x y] *)
  
  val vertex_attrib_i2uiv : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI2uiv]} [index v] *)
  
  val vertex_attrib_i3i : int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI3i]} [index x y z] *)
  
  val vertex_attrib_i3iv : int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI3iv]} [index v] *)
  
  val vertex_attrib_i3ui : int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI3ui]} [index x y z] *)
  
  val vertex_attrib_i3uiv : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI3uiv]} [index v] *)
  
  val vertex_attrib_i4bv : int -> (int, Bigarray.int8_signed_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4bv]} [index v] *)
  
  val vertex_attrib_i4i : int -> int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4i]} [index x y z w] *)
  
  val vertex_attrib_i4iv : int -> (int32, Bigarray.int32_elt) bigarray ->
    unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4iv]} [index v] *)
  
  val vertex_attrib_i4sv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4sv]} [index v] *)
  
  val vertex_attrib_i4ubv : int ->
    (int, Bigarray.int8_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4ubv]} [index v] *)
  
  val vertex_attrib_i4ui : int -> int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4ui]} [index x y z w] *)
  
  val vertex_attrib_i4uiv : int -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4uiv]} [index v] *)
  
  val vertex_attrib_i4usv : int ->
    (int, Bigarray.int16_unsigned_elt) bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribI4usv]} [index v] *)
  
  val vertex_attrib_ipointer : int -> int -> enum -> int ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttribPointer.xml}
      [glVertexAttribIPointer]} [index size type_ stride pointer] *)
  
  val vertex_attrib_p1ui : int -> enum -> bool -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP1ui]} [index type_ normalized value] *)
  
  val vertex_attrib_p1uiv : int -> enum -> bool -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP1uiv]} [index type_ normalized value] *)
  
  val vertex_attrib_p2ui : int -> enum -> bool -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP2ui]} [index type_ normalized value] *)
  
  val vertex_attrib_p2uiv : int -> enum -> bool -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP2uiv]} [index type_ normalized value] *)
  
  val vertex_attrib_p3ui : int -> enum -> bool -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP3ui]} [index type_ normalized value] *)
  
  val vertex_attrib_p3uiv : int -> enum -> bool -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP3uiv]} [index type_ normalized value] *)
  
  val vertex_attrib_p4ui : int -> enum -> bool -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP4ui]} [index type_ normalized value] *)
  
  val vertex_attrib_p4uiv : int -> enum -> bool -> uint32_bigarray -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttrib.xml}
      [glVertexAttribP4uiv]} [index type_ normalized value] *)
  
  val vertex_attrib_pointer : int -> int -> enum -> bool -> int ->
    [ `Offset of int | `Data of ('a, 'b) bigarray ] -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glVertexAttribPointer.xml}
      [glVertexAttribPointer]} [index size type_ normalized stride pointer] *)
  
  val viewport : int -> int -> int -> int -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glViewport.xml}
      [glViewport]} [x y width height] *)
  
  val wait_sync : sync -> bitfield -> uint64 -> unit
  (** {{:http://www.opengl.org/sdk/docs/man3/xhtml/glWaitSync.xml}
      [glWaitSync]} [sync flags timeout] *)
  
  (** {1:enums Enums} *)

  val active_attributes : enum
  
  val active_attribute_max_length : enum
  
  val active_texture_enum : enum
  
  val active_uniforms : enum
  
  val active_uniform_blocks : enum
  
  val active_uniform_block_max_name_length : enum
  
  val active_uniform_max_length : enum
  
  val aliased_line_width_range : enum
  
  val alpha : enum
  
  val already_signaled : enum
  
  val always : enum
  
  val and_ : enum
  
  val and_inverted : enum
  
  val and_reverse : enum
  
  val any_samples_passed : enum
  
  val array_buffer : enum
  
  val array_buffer_binding : enum
  
  val attached_shaders : enum
  
  val back : enum
  
  val back_left : enum
  
  val back_right : enum
  
  val bgr : enum
  
  val bgra : enum
  
  val bgra_integer : enum
  
  val bgr_integer : enum
  
  val blend : enum
  
  val blend_dst : enum
  
  val blend_dst_alpha : enum
  
  val blend_dst_rgb : enum
  
  val blend_equation_alpha : enum
  
  val blend_equation_rgb : enum
  
  val blend_src : enum
  
  val blend_src_alpha : enum
  
  val blend_src_rgb : enum
  
  val blue : enum
  
  val blue_integer : enum
  
  val bool : enum
  
  val bool_vec2 : enum
  
  val bool_vec3 : enum
  
  val bool_vec4 : enum
  
  val buffer_access : enum
  
  val buffer_access_flags : enum
  
  val buffer_mapped : enum
  
  val buffer_map_length : enum
  
  val buffer_map_offset : enum
  
  val buffer_map_pointer : enum
  
  val buffer_size : enum
  
  val buffer_usage : enum
  
  val byte : enum
  
  val ccw : enum
  
  val clamp_read_color : enum
  
  val clamp_to_border : enum
  
  val clamp_to_edge : enum
  
  val clear_enum : enum
  
  val clip_distance0 : enum
  
  val clip_distance1 : enum
  
  val clip_distance2 : enum
  
  val clip_distance3 : enum
  
  val clip_distance4 : enum
  
  val clip_distance5 : enum
  
  val clip_distance6 : enum
  
  val clip_distance7 : enum
  
  val color : enum
  
  val color_attachment0 : enum
  
  val color_attachment1 : enum
  
  val color_attachment10 : enum
  
  val color_attachment11 : enum
  
  val color_attachment12 : enum
  
  val color_attachment13 : enum
  
  val color_attachment14 : enum
  
  val color_attachment15 : enum
  
  val color_attachment16 : enum
  
  val color_attachment17 : enum
  
  val color_attachment18 : enum
  
  val color_attachment19 : enum
  
  val color_attachment2 : enum
  
  val color_attachment20 : enum
  
  val color_attachment21 : enum
  
  val color_attachment22 : enum
  
  val color_attachment23 : enum
  
  val color_attachment24 : enum
  
  val color_attachment25 : enum
  
  val color_attachment26 : enum
  
  val color_attachment27 : enum
  
  val color_attachment28 : enum
  
  val color_attachment29 : enum
  
  val color_attachment3 : enum
  
  val color_attachment30 : enum
  
  val color_attachment31 : enum
  
  val color_attachment4 : enum
  
  val color_attachment5 : enum
  
  val color_attachment6 : enum
  
  val color_attachment7 : enum
  
  val color_attachment8 : enum
  
  val color_attachment9 : enum
  
  val color_buffer_bit : enum
  
  val color_clear_value : enum
  
  val color_logic_op : enum
  
  val color_writemask : enum
  
  val compare_ref_to_texture : enum
  
  val compile_status : enum
  
  val compressed_red : enum
  
  val compressed_red_rgtc1 : enum
  
  val compressed_rg : enum
  
  val compressed_rgb : enum
  
  val compressed_rgba : enum
  
  val compressed_rg_rgtc2 : enum
  
  val compressed_signed_red_rgtc1 : enum
  
  val compressed_signed_rg_rgtc2 : enum
  
  val compressed_srgb : enum
  
  val compressed_srgb_alpha : enum
  
  val compressed_texture_formats : enum
  
  val condition_satisfied : enum
  
  val constant_alpha : enum
  
  val constant_color : enum
  
  val context_compatibility_profile_bit : enum
  
  val context_core_profile_bit : enum
  
  val context_flags : enum
  
  val context_flag_forward_compatible_bit : enum
  
  val context_profile_mask : enum
  
  val copy : enum
  
  val copy_inverted : enum
  
  val copy_read_buffer : enum
  
  val copy_write_buffer : enum
  
  val cull_face_enum : enum
  
  val cull_face_mode : enum
  
  val current_program : enum
  
  val current_query : enum
  
  val current_vertex_attrib : enum
  
  val cw : enum
  
  val decr : enum
  
  val decr_wrap : enum
  
  val delete_status : enum
  
  val depth : enum
  
  val depth24_stencil8 : enum
  
  val depth32f_stencil8 : enum
  
  val depth_attachment : enum
  
  val depth_buffer_bit : enum
  
  val depth_clamp : enum
  
  val depth_clear_value : enum
  
  val depth_component : enum
  
  val depth_component16 : enum
  
  val depth_component24 : enum
  
  val depth_component32 : enum
  
  val depth_component32f : enum
  
  val depth_func_enum : enum
  
  val depth_range_enum : enum
  
  val depth_stencil : enum
  
  val depth_stencil_attachment : enum
  
  val depth_test : enum
  
  val depth_writemask : enum
  
  val dither : enum
  
  val dont_care : enum
  
  val double : enum
  
  val doublebuffer : enum
  
  val draw_buffer_enum : enum
  
  val draw_buffer0 : enum
  
  val draw_buffer1 : enum
  
  val draw_buffer10 : enum
  
  val draw_buffer11 : enum
  
  val draw_buffer12 : enum
  
  val draw_buffer13 : enum
  
  val draw_buffer14 : enum
  
  val draw_buffer15 : enum
  
  val draw_buffer2 : enum
  
  val draw_buffer3 : enum
  
  val draw_buffer4 : enum
  
  val draw_buffer5 : enum
  
  val draw_buffer6 : enum
  
  val draw_buffer7 : enum
  
  val draw_buffer8 : enum
  
  val draw_buffer9 : enum
  
  val draw_framebuffer : enum
  
  val draw_framebuffer_binding : enum
  
  val dst_alpha : enum
  
  val dst_color : enum
  
  val dynamic_copy : enum
  
  val dynamic_draw : enum
  
  val dynamic_read : enum
  
  val element_array_buffer : enum
  
  val element_array_buffer_binding : enum
  
  val equal : enum
  
  val equiv : enum
  
  val extensions : enum
  
  val false_ : enum
  
  val fastest : enum
  
  val fill : enum
  
  val first_vertex_convention : enum
  
  val fixed_only : enum
  
  val float : enum
  
  val float_32_unsigned_int_24_8_rev : enum
  
  val float_mat2 : enum
  
  val float_mat2x3 : enum
  
  val float_mat2x4 : enum
  
  val float_mat3 : enum
  
  val float_mat3x2 : enum
  
  val float_mat3x4 : enum
  
  val float_mat4 : enum
  
  val float_mat4x2 : enum
  
  val float_mat4x3 : enum
  
  val float_vec2 : enum
  
  val float_vec3 : enum
  
  val float_vec4 : enum
  
  val fragment_shader : enum
  
  val fragment_shader_derivative_hint : enum
  
  val framebuffer : enum
  
  val framebuffer_attachment_alpha_size : enum
  
  val framebuffer_attachment_blue_size : enum
  
  val framebuffer_attachment_color_encoding : enum
  
  val framebuffer_attachment_component_type : enum
  
  val framebuffer_attachment_depth_size : enum
  
  val framebuffer_attachment_green_size : enum
  
  val framebuffer_attachment_layered : enum
  
  val framebuffer_attachment_object_name : enum
  
  val framebuffer_attachment_object_type : enum
  
  val framebuffer_attachment_red_size : enum
  
  val framebuffer_attachment_stencil_size : enum
  
  val framebuffer_attachment_texture_cube_map_face : enum
  
  val framebuffer_attachment_texture_layer : enum
  
  val framebuffer_attachment_texture_level : enum
  
  val framebuffer_binding : enum
  
  val framebuffer_complete : enum
  
  val framebuffer_default : enum
  
  val framebuffer_incomplete_attachment : enum
  
  val framebuffer_incomplete_draw_buffer : enum
  
  val framebuffer_incomplete_layer_targets : enum
  
  val framebuffer_incomplete_missing_attachment : enum
  
  val framebuffer_incomplete_multisample : enum
  
  val framebuffer_incomplete_read_buffer : enum
  
  val framebuffer_srgb : enum
  
  val framebuffer_undefined : enum
  
  val framebuffer_unsupported : enum
  
  val front : enum
  
  val front_and_back : enum
  
  val front_face_enum : enum
  
  val front_left : enum
  
  val front_right : enum
  
  val func_add : enum
  
  val func_reverse_subtract : enum
  
  val func_subtract : enum
  
  val geometry_input_type : enum
  
  val geometry_output_type : enum
  
  val geometry_shader : enum
  
  val geometry_vertices_out : enum
  
  val gequal : enum
  
  val greater : enum
  
  val green : enum
  
  val green_integer : enum
  
  val half_float : enum
  
  val incr : enum
  
  val incr_wrap : enum
  
  val info_log_length : enum
  
  val int : enum
  
  val interleaved_attribs : enum
  
  val int_2_10_10_10_rev : enum
  
  val int_sampler_1d : enum
  
  val int_sampler_1d_array : enum
  
  val int_sampler_2d : enum
  
  val int_sampler_2d_array : enum
  
  val int_sampler_2d_multisample : enum
  
  val int_sampler_2d_multisample_array : enum
  
  val int_sampler_2d_rect : enum
  
  val int_sampler_3d : enum
  
  val int_sampler_buffer : enum
  
  val int_sampler_cube : enum
  
  val int_vec2 : enum
  
  val int_vec3 : enum
  
  val int_vec4 : enum
  
  val invalid_enum : enum
  
  val invalid_framebuffer_operation : enum
  
  val invalid_index : int32
  
  val invalid_operation : enum
  
  val invalid_value : enum
  
  val invert : enum
  
  val keep : enum
  
  val last_vertex_convention : enum
  
  val left : enum
  
  val lequal : enum
  
  val less : enum
  
  val line : enum
  
  val linear : enum
  
  val linear_mipmap_linear : enum
  
  val linear_mipmap_nearest : enum
  
  val lines : enum
  
  val lines_adjacency : enum
  
  val line_loop : enum
  
  val line_smooth : enum
  
  val line_smooth_hint : enum
  
  val line_strip : enum
  
  val line_strip_adjacency : enum
  
  val line_width_enum : enum
  
  val line_width_granularity : enum
  
  val line_width_range : enum
  
  val link_status : enum
  
  val logic_op_mode : enum
  
  val lower_left : enum
  
  val major_version : enum
  
  val map_flush_explicit_bit : enum
  
  val map_invalidate_buffer_bit : enum
  
  val map_invalidate_range_bit : enum
  
  val map_read_bit : enum
  
  val map_unsynchronized_bit : enum
  
  val map_write_bit : enum
  
  val max : enum
  
  val max_3d_texture_size : enum
  
  val max_array_texture_layers : enum
  
  val max_clip_distances : enum
  
  val max_color_attachments : enum
  
  val max_color_texture_samples : enum
  
  val max_combined_fragment_uniform_components : enum
  
  val max_combined_geometry_uniform_components : enum
  
  val max_combined_texture_image_units : enum
  
  val max_combined_uniform_blocks : enum
  
  val max_combined_vertex_uniform_components : enum
  
  val max_cube_map_texture_size : enum
  
  val max_depth_texture_samples : enum
  
  val max_draw_buffers : enum
  
  val max_dual_source_draw_buffers : enum
  
  val max_elements_indices : enum
  
  val max_elements_vertices : enum
  
  val max_fragment_input_components : enum
  
  val max_fragment_uniform_blocks : enum
  
  val max_fragment_uniform_components : enum
  
  val max_geometry_input_components : enum
  
  val max_geometry_output_components : enum
  
  val max_geometry_output_vertices : enum
  
  val max_geometry_texture_image_units : enum
  
  val max_geometry_total_output_components : enum
  
  val max_geometry_uniform_blocks : enum
  
  val max_geometry_uniform_components : enum
  
  val max_integer_samples : enum
  
  val max_program_texel_offset : enum
  
  val max_rectangle_texture_size : enum
  
  val max_renderbuffer_size : enum
  
  val max_samples : enum
  
  val max_sample_mask_words : enum
  
  val max_server_wait_timeout : enum
  
  val max_texture_buffer_size : enum
  
  val max_texture_image_units : enum
  
  val max_texture_lod_bias : enum
  
  val max_texture_size : enum
  
  val max_transform_feedback_interleaved_components : enum
  
  val max_transform_feedback_separate_attribs : enum
  
  val max_transform_feedback_separate_components : enum
  
  val max_uniform_block_size : enum
  
  val max_uniform_buffer_bindings : enum
  
  val max_varying_components : enum
  
  val max_varying_floats : enum
  
  val max_vertex_attribs : enum
  
  val max_vertex_output_components : enum
  
  val max_vertex_texture_image_units : enum
  
  val max_vertex_uniform_blocks : enum
  
  val max_vertex_uniform_components : enum
  
  val max_viewport_dims : enum
  
  val min : enum
  
  val minor_version : enum
  
  val min_program_texel_offset : enum
  
  val mirrored_repeat : enum
  
  val multisample : enum
  
  val nand : enum
  
  val nearest : enum
  
  val nearest_mipmap_linear : enum
  
  val nearest_mipmap_nearest : enum
  
  val never : enum
  
  val nicest : enum
  
  val none : enum
  
  val noop : enum
  
  val nor : enum
  
  val notequal : enum
  
  val no_error : enum
  
  val num_compressed_texture_formats : enum
  
  val num_extensions : enum
  
  val object_type : enum
  
  val one : enum
  
  val one_minus_constant_alpha : enum
  
  val one_minus_constant_color : enum
  
  val one_minus_dst_alpha : enum
  
  val one_minus_dst_color : enum
  
  val one_minus_src1_alpha : enum
  
  val one_minus_src1_color : enum
  
  val one_minus_src_alpha : enum
  
  val one_minus_src_color : enum
  
  val or_ : enum
  
  val or_inverted : enum
  
  val or_reverse : enum
  
  val out_of_memory : enum
  
  val pack_alignment : enum
  
  val pack_image_height : enum
  
  val pack_lsb_first : enum
  
  val pack_row_length : enum
  
  val pack_skip_images : enum
  
  val pack_skip_pixels : enum
  
  val pack_skip_rows : enum
  
  val pack_swap_bytes : enum
  
  val pixel_pack_buffer : enum
  
  val pixel_pack_buffer_binding : enum
  
  val pixel_unpack_buffer : enum
  
  val pixel_unpack_buffer_binding : enum
  
  val point : enum
  
  val points : enum
  
  val point_fade_threshold_size : enum
  
  val point_size_enum : enum
  
  val point_size_granularity : enum
  
  val point_size_range : enum
  
  val point_sprite_coord_origin : enum
  
  val polygon_mode_enum : enum
  
  val polygon_offset_factor : enum
  
  val polygon_offset_fill : enum
  
  val polygon_offset_line : enum
  
  val polygon_offset_point : enum
  
  val polygon_offset_units : enum
  
  val polygon_smooth : enum
  
  val polygon_smooth_hint : enum
  
  val primitives_generated : enum
  
  val primitive_restart : enum
  
  val primitive_restart_index_enum : enum
  
  val program_point_size : enum
  
  val provoking_vertex_enum : enum
  
  val proxy_texture_1d : enum
  
  val proxy_texture_1d_array : enum
  
  val proxy_texture_2d : enum
  
  val proxy_texture_2d_array : enum
  
  val proxy_texture_2d_multisample : enum
  
  val proxy_texture_2d_multisample_array : enum
  
  val proxy_texture_3d : enum
  
  val proxy_texture_cube_map : enum
  
  val proxy_texture_rectangle : enum
  
  val quads_follow_provoking_vertex_convention : enum
  
  val query_by_region_no_wait : enum
  
  val query_by_region_wait : enum
  
  val query_counter_bits : enum
  
  val query_no_wait : enum
  
  val query_result : enum
  
  val query_result_available : enum
  
  val query_wait : enum
  
  val r11f_g11f_b10f : enum
  
  val r16 : enum
  
  val r16f : enum
  
  val r16i : enum
  
  val r16ui : enum
  
  val r16_snorm : enum
  
  val r32f : enum
  
  val r32i : enum
  
  val r32ui : enum
  
  val r3_g3_b2 : enum
  
  val r8 : enum
  
  val r8i : enum
  
  val r8ui : enum
  
  val r8_snorm : enum
  
  val rasterizer_discard : enum
  
  val read_buffer_enum : enum
  
  val read_framebuffer : enum
  
  val read_framebuffer_binding : enum
  
  val read_only : enum
  
  val read_write : enum
  
  val red : enum
  
  val red_integer : enum
  
  val renderbuffer : enum
  
  val renderbuffer_alpha_size : enum
  
  val renderbuffer_binding : enum
  
  val renderbuffer_blue_size : enum
  
  val renderbuffer_depth_size : enum
  
  val renderbuffer_green_size : enum
  
  val renderbuffer_height : enum
  
  val renderbuffer_internal_format : enum
  
  val renderbuffer_red_size : enum
  
  val renderbuffer_samples : enum
  
  val renderbuffer_stencil_size : enum
  
  val renderbuffer_width : enum
  
  val renderer : enum
  
  val repeat : enum
  
  val replace : enum
  
  val rg : enum
  
  val rg16 : enum
  
  val rg16f : enum
  
  val rg16i : enum
  
  val rg16ui : enum
  
  val rg16_snorm : enum
  
  val rg32f : enum
  
  val rg32i : enum
  
  val rg32ui : enum
  
  val rg8 : enum
  
  val rg8i : enum
  
  val rg8ui : enum
  
  val rg8_snorm : enum
  
  val rgb : enum
  
  val rgb10 : enum
  
  val rgb10_a2 : enum
  
  val rgb10_a2ui : enum
  
  val rgb12 : enum
  
  val rgb16 : enum
  
  val rgb16f : enum
  
  val rgb16i : enum
  
  val rgb16ui : enum
  
  val rgb16_snorm : enum
  
  val rgb32f : enum
  
  val rgb32i : enum
  
  val rgb32ui : enum
  
  val rgb4 : enum
  
  val rgb5 : enum
  
  val rgb5_a1 : enum
  
  val rgb8 : enum
  
  val rgb8i : enum
  
  val rgb8ui : enum
  
  val rgb8_snorm : enum
  
  val rgb9_e5 : enum
  
  val rgba : enum
  
  val rgba12 : enum
  
  val rgba16 : enum
  
  val rgba16f : enum
  
  val rgba16i : enum
  
  val rgba16ui : enum
  
  val rgba16_snorm : enum
  
  val rgba2 : enum
  
  val rgba32f : enum
  
  val rgba32i : enum
  
  val rgba32ui : enum
  
  val rgba4 : enum
  
  val rgba8 : enum
  
  val rgba8i : enum
  
  val rgba8ui : enum
  
  val rgba8_snorm : enum
  
  val rgba_integer : enum
  
  val rgb_integer : enum
  
  val rg_integer : enum
  
  val right : enum
  
  val sampler_1d : enum
  
  val sampler_1d_array : enum
  
  val sampler_1d_array_shadow : enum
  
  val sampler_1d_shadow : enum
  
  val sampler_2d : enum
  
  val sampler_2d_array : enum
  
  val sampler_2d_array_shadow : enum
  
  val sampler_2d_multisample : enum
  
  val sampler_2d_multisample_array : enum
  
  val sampler_2d_rect : enum
  
  val sampler_2d_rect_shadow : enum
  
  val sampler_2d_shadow : enum
  
  val sampler_3d : enum
  
  val sampler_binding : enum
  
  val sampler_buffer : enum
  
  val sampler_cube : enum
  
  val sampler_cube_shadow : enum
  
  val samples : enum
  
  val samples_passed : enum
  
  val sample_alpha_to_coverage : enum
  
  val sample_alpha_to_one : enum
  
  val sample_buffers : enum
  
  val sample_coverage_enum : enum
  
  val sample_coverage_invert : enum
  
  val sample_coverage_value : enum
  
  val sample_mask : enum
  
  val sample_mask_value : enum
  
  val sample_position : enum
  
  val scissor_box : enum
  
  val scissor_test : enum
  
  val separate_attribs : enum
  
  val set : enum
  
  val shader_source_length : enum
  
  val shader_type : enum
  
  val shading_language_version : enum
  
  val short : enum
  
  val signaled : enum
  
  val signed_normalized : enum
  
  val smooth_line_width_granularity : enum
  
  val smooth_line_width_range : enum
  
  val smooth_point_size_granularity : enum
  
  val smooth_point_size_range : enum
  
  val src1_alpha : enum
  
  val src1_color : enum
  
  val src_alpha : enum
  
  val src_alpha_saturate : enum
  
  val src_color : enum
  
  val srgb : enum
  
  val srgb8 : enum
  
  val srgb8_alpha8 : enum
  
  val srgb_alpha : enum
  
  val static_copy : enum
  
  val static_draw : enum
  
  val static_read : enum
  
  val stencil : enum
  
  val stencil_attachment : enum
  
  val stencil_back_fail : enum
  
  val stencil_back_func : enum
  
  val stencil_back_pass_depth_fail : enum
  
  val stencil_back_pass_depth_pass : enum
  
  val stencil_back_ref : enum
  
  val stencil_back_value_mask : enum
  
  val stencil_back_writemask : enum
  
  val stencil_buffer_bit : enum
  
  val stencil_clear_value : enum
  
  val stencil_fail : enum
  
  val stencil_func_enum : enum
  
  val stencil_index : enum
  
  val stencil_index1 : enum
  
  val stencil_index16 : enum
  
  val stencil_index4 : enum
  
  val stencil_index8 : enum
  
  val stencil_pass_depth_fail : enum
  
  val stencil_pass_depth_pass : enum
  
  val stencil_ref : enum
  
  val stencil_test : enum
  
  val stencil_value_mask : enum
  
  val stencil_writemask : enum
  
  val stereo : enum
  
  val stream_copy : enum
  
  val stream_draw : enum
  
  val stream_read : enum
  
  val subpixel_bits : enum
  
  val sync_condition : enum
  
  val sync_fence : enum
  
  val sync_flags : enum
  
  val sync_flush_commands_bit : enum
  
  val sync_gpu_commands_complete : enum
  
  val sync_status : enum
  
  val texture : enum
  
  val texture0 : enum
  
  val texture1 : enum
  
  val texture10 : enum
  
  val texture11 : enum
  
  val texture12 : enum
  
  val texture13 : enum
  
  val texture14 : enum
  
  val texture15 : enum
  
  val texture16 : enum
  
  val texture17 : enum
  
  val texture18 : enum
  
  val texture19 : enum
  
  val texture2 : enum
  
  val texture20 : enum
  
  val texture21 : enum
  
  val texture22 : enum
  
  val texture23 : enum
  
  val texture24 : enum
  
  val texture25 : enum
  
  val texture26 : enum
  
  val texture27 : enum
  
  val texture28 : enum
  
  val texture29 : enum
  
  val texture3 : enum
  
  val texture30 : enum
  
  val texture31 : enum
  
  val texture4 : enum
  
  val texture5 : enum
  
  val texture6 : enum
  
  val texture7 : enum
  
  val texture8 : enum
  
  val texture9 : enum
  
  val texture_1d : enum
  
  val texture_1d_array : enum
  
  val texture_2d : enum
  
  val texture_2d_array : enum
  
  val texture_2d_multisample : enum
  
  val texture_2d_multisample_array : enum
  
  val texture_3d : enum
  
  val texture_alpha_size : enum
  
  val texture_alpha_type : enum
  
  val texture_base_level : enum
  
  val texture_binding_1d : enum
  
  val texture_binding_1d_array : enum
  
  val texture_binding_2d : enum
  
  val texture_binding_2d_array : enum
  
  val texture_binding_2d_multisample : enum
  
  val texture_binding_2d_multisample_array : enum
  
  val texture_binding_3d : enum
  
  val texture_binding_buffer : enum
  
  val texture_binding_cube_map : enum
  
  val texture_binding_rectangle : enum
  
  val texture_blue_size : enum
  
  val texture_blue_type : enum
  
  val texture_border_color : enum
  
  val texture_buffer : enum
  
  val texture_buffer_data_store_binding : enum
  
  val texture_compare_func : enum
  
  val texture_compare_mode : enum
  
  val texture_compressed : enum
  
  val texture_compressed_image_size : enum
  
  val texture_compression_hint : enum
  
  val texture_cube_map : enum
  
  val texture_cube_map_negative_x : enum
  
  val texture_cube_map_negative_y : enum
  
  val texture_cube_map_negative_z : enum
  
  val texture_cube_map_positive_x : enum
  
  val texture_cube_map_positive_y : enum
  
  val texture_cube_map_positive_z : enum
  
  val texture_cube_map_seamless : enum
  
  val texture_depth : enum
  
  val texture_depth_size : enum
  
  val texture_depth_type : enum
  
  val texture_fixed_sample_locations : enum
  
  val texture_green_size : enum
  
  val texture_green_type : enum
  
  val texture_height : enum
  
  val texture_internal_format : enum
  
  val texture_lod_bias : enum
  
  val texture_mag_filter : enum
  
  val texture_max_level : enum
  
  val texture_max_lod : enum
  
  val texture_min_filter : enum
  
  val texture_min_lod : enum
  
  val texture_rectangle : enum
  
  val texture_red_size : enum
  
  val texture_red_type : enum
  
  val texture_samples : enum
  
  val texture_shared_size : enum
  
  val texture_stencil_size : enum
  
  val texture_swizzle_a : enum
  
  val texture_swizzle_b : enum
  
  val texture_swizzle_g : enum
  
  val texture_swizzle_r : enum
  
  val texture_swizzle_rgba : enum
  
  val texture_width : enum
  
  val texture_wrap_r : enum
  
  val texture_wrap_s : enum
  
  val texture_wrap_t : enum
  
  val timeout_expired : enum
  
  val timeout_ignored : int64
  
  val timestamp : enum
  
  val time_elapsed : enum
  
  val transform_feedback_buffer : enum
  
  val transform_feedback_buffer_binding : enum
  
  val transform_feedback_buffer_mode : enum
  
  val transform_feedback_buffer_size : enum
  
  val transform_feedback_buffer_start : enum
  
  val transform_feedback_primitives_written : enum
  
  val transform_feedback_varyings_enum : enum
  
  val transform_feedback_varying_max_length : enum
  
  val triangles : enum
  
  val triangles_adjacency : enum
  
  val triangle_fan : enum
  
  val triangle_strip : enum
  
  val triangle_strip_adjacency : enum
  
  val true_ : enum
  
  val uniform_array_stride : enum
  
  val uniform_block_active_uniforms : enum
  
  val uniform_block_active_uniform_indices : enum
  
  val uniform_block_binding_enum : enum
  
  val uniform_block_data_size : enum
  
  val uniform_block_index : enum
  
  val uniform_block_name_length : enum
  
  val uniform_block_referenced_by_fragment_shader : enum
  
  val uniform_block_referenced_by_geometry_shader : enum
  
  val uniform_block_referenced_by_vertex_shader : enum
  
  val uniform_buffer : enum
  
  val uniform_buffer_binding : enum
  
  val uniform_buffer_offset_alignment : enum
  
  val uniform_buffer_size : enum
  
  val uniform_buffer_start : enum
  
  val uniform_is_row_major : enum
  
  val uniform_matrix_stride : enum
  
  val uniform_name_length : enum
  
  val uniform_offset : enum
  
  val uniform_size : enum
  
  val uniform_type : enum
  
  val unpack_alignment : enum
  
  val unpack_image_height : enum
  
  val unpack_lsb_first : enum
  
  val unpack_row_length : enum
  
  val unpack_skip_images : enum
  
  val unpack_skip_pixels : enum
  
  val unpack_skip_rows : enum
  
  val unpack_swap_bytes : enum
  
  val unsignaled : enum
  
  val unsigned_byte : enum
  
  val unsigned_byte_2_3_3_rev : enum
  
  val unsigned_byte_3_3_2 : enum
  
  val unsigned_int : enum
  
  val unsigned_int_10f_11f_11f_rev : enum
  
  val unsigned_int_10_10_10_2 : enum
  
  val unsigned_int_24_8 : enum
  
  val unsigned_int_2_10_10_10_rev : enum
  
  val unsigned_int_5_9_9_9_rev : enum
  
  val unsigned_int_8_8_8_8 : enum
  
  val unsigned_int_8_8_8_8_rev : enum
  
  val unsigned_int_sampler_1d : enum
  
  val unsigned_int_sampler_1d_array : enum
  
  val unsigned_int_sampler_2d : enum
  
  val unsigned_int_sampler_2d_array : enum
  
  val unsigned_int_sampler_2d_multisample : enum
  
  val unsigned_int_sampler_2d_multisample_array : enum
  
  val unsigned_int_sampler_2d_rect : enum
  
  val unsigned_int_sampler_3d : enum
  
  val unsigned_int_sampler_buffer : enum
  
  val unsigned_int_sampler_cube : enum
  
  val unsigned_int_vec2 : enum
  
  val unsigned_int_vec3 : enum
  
  val unsigned_int_vec4 : enum
  
  val unsigned_normalized : enum
  
  val unsigned_short : enum
  
  val unsigned_short_1_5_5_5_rev : enum
  
  val unsigned_short_4_4_4_4 : enum
  
  val unsigned_short_4_4_4_4_rev : enum
  
  val unsigned_short_5_5_5_1 : enum
  
  val unsigned_short_5_6_5 : enum
  
  val unsigned_short_5_6_5_rev : enum
  
  val upper_left : enum
  
  val validate_status : enum
  
  val vendor : enum
  
  val version : enum
  
  val vertex_array_binding : enum
  
  val vertex_attrib_array_buffer_binding : enum
  
  val vertex_attrib_array_divisor : enum
  
  val vertex_attrib_array_enabled : enum
  
  val vertex_attrib_array_integer : enum
  
  val vertex_attrib_array_normalized : enum
  
  val vertex_attrib_array_pointer : enum
  
  val vertex_attrib_array_size : enum
  
  val vertex_attrib_array_stride : enum
  
  val vertex_attrib_array_type : enum
  
  val vertex_program_point_size : enum
  
  val vertex_shader : enum
  
  val viewport_enum : enum
  
  val wait_failed : enum
  
  val write_only : enum
  
  val xor : enum
  
  val zero : enum
  
end

(** {1:conventions Conventions}

    To find the name of an OCaml function corresponding to a C
    function name, map the [gl] prefix to the module name
    {!Tgl3.Gl},
    add an underscore between each minuscule and majuscule and lower
    case the result. For example [glGetError] maps to
    {!Tgl3.Gl.get_error}

    To find the name of an OCaml value corresponding to a C enumerant name,
    map the [GL_] prefix to the module name {!Tgl3.Gl}
    and lower case the rest. For example [GL_COLOR_BUFFER_BIT] maps to
    {!Tgl3.Gl.color_buffer_bit}.

    The following exceptions occur:
    {ul
    {- A few enumerant names do clash with functions name. In that case we
       postfix the enumerant name with [_enum]. For example we have
       {!Tgl3.Gl.viewport} and {!Tgl3.Gl.viewport_enum}.}
    {- If applying the above procedures results in an identifier that
       doesn't start with a letter, prefix the identifier with a ['_'].}
    {- If applying the above procedures results in an identifier that
       is an OCaml keyword, suffix the identifier with a ['_'].}} *)

(*---------------------------------------------------------------------------
   Copyright (c) 2013 Daniel C. Bünzli

   Permission to use, copy, modify, and/or distribute this software for any
   purpose with or without fee is hereby granted, provided that the above
   copyright notice and this permission notice appear in all copies.

   THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
   WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
   MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
   ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
   WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
   ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
   OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
  ---------------------------------------------------------------------------*)

end = struct
#1 "tgl3.ml"
(*---------------------------------------------------------------------------
   Copyright (c) 2013 Daniel C. Bünzli. All rights reserved.
   Distributed under the ISC license, see terms at the end of the file.
   tgls v0.8.4
  ---------------------------------------------------------------------------*)

(* WARNING do not edit. This file was automatically generated with:
   _build/support/apiquery.native -ml -api gl3.3 *)

open Ctypes
open Foreign

let abi = Libffi_abi.(if Sys.win32 then stdcall else default_abi)
let foreign ?from ?stub ?check_errno ?release_runtime_lock f fn =
foreign ~abi ?from ?stub ?check_errno ?release_runtime_lock f fn

(* OpenGL 3.x bindings *)

module Gl = struct

  (* Bigarrays *)

  type ('a, 'b) bigarray = ('a,'b, Bigarray.c_layout) Bigarray.Array1.t

  let ba_kind_byte_size : ('a, 'b) Bigarray.kind -> int = fun k ->
    let open Bigarray in
    (* FIXME: see http://caml.inria.fr/mantis/view.php?id=6263 *)
    match Obj.magic k with
    | k when k = char || k = int8_signed || k = int8_unsigned -> 1
    | k when k = int16_signed || k = int16_unsigned -> 2
    | k when k = int32 || k = float32 -> 4
    | k when k = float64 || k = int64 || k = complex32 -> 8
    | k when k = complex64 -> 16
    | k when k = int || k = nativeint -> Sys.word_size / 8
    | k -> assert false

 let bigarray_byte_size ba =
   let el_size = ba_kind_byte_size (Bigarray.Array1.kind ba) in
   el_size * Bigarray.Array1.dim ba

 let access_ptr_typ_of_ba_kind : ('a, 'b) Bigarray.kind -> 'a ptr typ =
   fun k ->
   let open Bigarray in
   (* FIXME: use typ_of_bigarray_kind when ctypes support it. *)
   match Obj.magic k with
   | k when k = float32 -> Obj.magic (ptr Ctypes.float)
   | k when k = float64 -> Obj.magic (ptr Ctypes.double)
   | k when k = complex32 -> Obj.magic (ptr Ctypes.complex32)
   | k when k = complex64 -> Obj.magic (ptr Ctypes.complex64)
   | k when k = int8_signed -> Obj.magic (ptr Ctypes.int8_t)
   | k when k = int8_unsigned -> Obj.magic (ptr Ctypes.uint8_t)
   | k when k = int16_signed -> Obj.magic (ptr Ctypes.int16_t)
   | k when k = int16_unsigned -> Obj.magic (ptr Ctypes.uint16_t)
   | k when k = int -> Obj.magic (ptr Ctypes.camlint)
   | k when k = int32 -> Obj.magic (ptr Ctypes.int32_t)
   | k when k = int64 -> Obj.magic (ptr Ctypes.int64_t)
   | k when k = nativeint -> Obj.magic (ptr Ctypes.nativeint)
   | k when k = char -> Obj.magic (ptr Ctypes.char)
   | _ -> assert false

 let string_of_bigarray ba =
   let len = Bigarray.Array1.dim ba in
   let b = Buffer.create (len - 1) in
   try
     for i = 0 to len - 1 do
       if ba.{i} = '\x00' then raise Exit else Buffer.add_char b ba.{i}
     done;
     raise Exit;
   with Exit -> Buffer.contents b

  (* Types *)

  let ba_as_charp =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_float32p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_float64p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_uint16p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_int8p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_uint8p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_int32p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_opt_as_int32p =
    view ~read:(fun _ -> assert false)
         ~write:(function
          | None -> null
          | Some b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_int64p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  let ba_as_nativeint =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  type bitfield = int
  let int_as_uint =
    view ~read:Unsigned.UInt.to_int
         ~write:Unsigned.UInt.of_int
         uint
  
  let bool =
    view ~read:(fun u -> Unsigned.UChar.(compare u zero <> 0))
         ~write:(fun b -> Unsigned.UChar.(of_int (Pervasives.compare b false)))
         uchar
  
  type enum = int
  type enum_bigarray = (int32, Bigarray.int32_elt) bigarray
  let ba_as_enump =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  type int16 = int
  type sync = unit ptr
  let sync : sync typ = ptr void
  let sync_opt : sync option typ = ptr_opt void
  
  type uint32_bigarray = (int32, Bigarray.int32_elt) bigarray
  let ba_as_uint32p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  type uint64 = int64
  let int64_as_uint64_t =
    view ~read:Unsigned.UInt64.to_int64
         ~write:Unsigned.UInt64.of_int64
         uint64_t
  
  type uint64_bigarray = (int64, Bigarray.int64_elt) bigarray
  let ba_as_uint64p =
    view ~read:(fun _ -> assert false)
         ~write:(fun b -> to_voidp (bigarray_start array1 b))
         (ptr void)
  
  type uint8 = int
  let int_as_uint8_t =
    view ~read:Unsigned.UInt8.to_int
         ~write:Unsigned.UInt8.of_int
         uint8_t
  
  type debug_proc = enum -> enum -> int -> enum -> string -> unit
  
  (* Functions *)

  let stub = true

  let active_texture =
    foreign ~stub "glActiveTexture" (int_as_uint @-> returning void)
  
  let attach_shader =
    foreign ~stub "glAttachShader"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let begin_conditional_render =
    foreign ~stub "glBeginConditionalRender"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let begin_query =
    foreign ~stub "glBeginQuery"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let begin_transform_feedback =
    foreign ~stub "glBeginTransformFeedback" (int_as_uint @-> returning void)
  
  let bind_attrib_location =
    foreign ~stub "glBindAttribLocation"
      (int_as_uint @-> int_as_uint @-> string @-> returning void)
  
  let bind_buffer =
    foreign ~stub "glBindBuffer"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let bind_buffer_base =
    foreign ~stub "glBindBufferBase"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> returning void)
  
  let bind_buffer_range =
    foreign ~stub "glBindBufferRange"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int @-> int @->
       returning void)
  
  let bind_frag_data_location =
    foreign ~stub "glBindFragDataLocation"
      (int_as_uint @-> int_as_uint @-> string @-> returning void)
  
  let bind_frag_data_location_indexed =
    foreign ~stub "glBindFragDataLocationIndexed"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> string @->
       returning void)
  
  let bind_framebuffer =
    foreign ~stub "glBindFramebuffer"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let bind_renderbuffer =
    foreign ~stub "glBindRenderbuffer"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let bind_sampler =
    foreign ~stub "glBindSampler"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let bind_texture =
    foreign ~stub "glBindTexture"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let bind_vertex_array =
    foreign ~stub "glBindVertexArray" (int_as_uint @-> returning void)
  
  let blend_color =
    foreign ~stub "glBlendColor"
      (float @-> float @-> float @-> float @-> returning void)
  
  let blend_equation =
    foreign ~stub "glBlendEquation" (int_as_uint @-> returning void)
  
  let blend_equation_separate =
    foreign ~stub "glBlendEquationSeparate"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let blend_func =
    foreign ~stub "glBlendFunc"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let blend_func_separate =
    foreign ~stub "glBlendFuncSeparate"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       returning void)
  
  let blit_framebuffer =
    foreign ~stub "glBlitFramebuffer"
      (int @-> int @-> int @-> int @-> int @-> int @-> int @-> int @->
       int_as_uint @-> int_as_uint @-> returning void)
  
  let buffer_data =
    foreign ~stub "glBufferData"
      (int_as_uint @-> int @-> (ptr void) @-> int_as_uint @-> returning void)
  
  let buffer_data target size data usage =
    let data = match data with
    | None -> null | Some b -> to_voidp (bigarray_start array1 b)
    in
    buffer_data target size data usage
  
  let buffer_sub_data =
    foreign ~stub "glBufferSubData"
      (int_as_uint @-> int @-> int @-> (ptr void) @-> returning void)
  
  let buffer_sub_data target offset size data =
    let data = match data with
    | None -> null | Some b -> to_voidp (bigarray_start array1 b)
    in
    buffer_sub_data target offset size data
  
  let check_framebuffer_status =
    foreign ~stub "glCheckFramebufferStatus"
      (int_as_uint @-> returning int_as_uint)
  
  let clamp_color =
    foreign ~stub "glClampColor"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let clear =
    foreign ~stub "glClear" (int_as_uint @-> returning void)
  
  let clear_bufferfi =
    foreign ~stub "glClearBufferfi"
      (int_as_uint @-> int @-> float @-> int @-> returning void)
  
  let clear_bufferfv =
    foreign ~stub "glClearBufferfv"
      (int_as_uint @-> int @-> ba_as_float32p @-> returning void)
  
  let clear_bufferiv =
    foreign ~stub "glClearBufferiv"
      (int_as_uint @-> int @-> ba_as_int32p @-> returning void)
  
  let clear_bufferuiv =
    foreign ~stub "glClearBufferuiv"
      (int_as_uint @-> int @-> ba_as_uint32p @-> returning void)
  
  let clear_color =
    foreign ~stub "glClearColor"
      (float @-> float @-> float @-> float @-> returning void)
  
  let clear_depth =
    foreign ~stub "glClearDepth" (double @-> returning void)
  
  let clear_stencil =
    foreign ~stub "glClearStencil" (int @-> returning void)
  
  let client_wait_sync =
    foreign ~stub "glClientWaitSync"
      (sync @-> int_as_uint @-> int64_as_uint64_t @-> returning int_as_uint)
  
  let color_mask =
    foreign ~stub "glColorMask"
      (bool @-> bool @-> bool @-> bool @-> returning void)
  
  let color_maski =
    foreign ~stub "glColorMaski"
      (int_as_uint @-> bool @-> bool @-> bool @-> bool @-> returning void)
  
  let compile_shader =
    foreign ~stub "glCompileShader" (int_as_uint @-> returning void)
  
  let compressed_tex_image1d =
    foreign ~stub "glCompressedTexImage1D"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> int @->
       (ptr void) @-> returning void)
  
  let compressed_tex_image1d target level internalformat width border
                             imageSize data =
    let data = match data with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    compressed_tex_image1d target level internalformat width border imageSize
      data
  
  let compressed_tex_image2d =
    foreign ~stub "glCompressedTexImage2D"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> int @->
       int @-> (ptr void) @-> returning void)
  
  let compressed_tex_image2d target level internalformat width height border
                             imageSize data =
    let data = match data with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    compressed_tex_image2d target level internalformat width height border
      imageSize data
  
  let compressed_tex_image3d =
    foreign ~stub "glCompressedTexImage3D"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> int @->
       int @-> int @-> (ptr void) @-> returning void)
  
  let compressed_tex_image3d target level internalformat width height depth
                             border imageSize data =
    let data = match data with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    compressed_tex_image3d target level internalformat width height depth
      border imageSize data
  
  let compressed_tex_sub_image1d =
    foreign ~stub "glCompressedTexSubImage1D"
      (int_as_uint @-> int @-> int @-> int @-> int_as_uint @-> int @->
       (ptr void) @-> returning void)
  
  let compressed_tex_sub_image1d target level xoffset width format imageSize
                                 data =
    let data = match data with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    compressed_tex_sub_image1d target level xoffset width format imageSize
      data
  
  let compressed_tex_sub_image2d =
    foreign ~stub "glCompressedTexSubImage2D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @->
       int_as_uint @-> int @-> (ptr void) @-> returning void)
  
  let compressed_tex_sub_image2d target level xoffset yoffset width height
                                 format imageSize data =
    let data = match data with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    compressed_tex_sub_image2d target level xoffset yoffset width height
      format imageSize data
  
  let compressed_tex_sub_image3d =
    foreign ~stub "glCompressedTexSubImage3D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @-> int @->
       int @-> int_as_uint @-> int @-> (ptr void) @-> returning void)
  
  let compressed_tex_sub_image3d target level xoffset yoffset zoffset width
                                 height depth format imageSize data =
    let data = match data with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    compressed_tex_sub_image3d target level xoffset yoffset zoffset width
      height depth format imageSize data
  
  let copy_buffer_sub_data =
    foreign ~stub "glCopyBufferSubData"
      (int_as_uint @-> int_as_uint @-> int @-> int @-> int @->
       returning void)
  
  let copy_tex_image1d =
    foreign ~stub "glCopyTexImage1D"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> int @->
       int @-> returning void)
  
  let copy_tex_image2d =
    foreign ~stub "glCopyTexImage2D"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> int @->
       int @-> int @-> returning void)
  
  let copy_tex_sub_image1d =
    foreign ~stub "glCopyTexSubImage1D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @->
       returning void)
  
  let copy_tex_sub_image2d =
    foreign ~stub "glCopyTexSubImage2D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @-> int @->
       int @-> returning void)
  
  let copy_tex_sub_image3d =
    foreign ~stub "glCopyTexSubImage3D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @-> int @->
       int @-> int @-> returning void)
  
  let create_program =
    foreign ~stub "glCreateProgram" (void @-> returning int_as_uint)
  
  let create_shader =
    foreign ~stub "glCreateShader" (int_as_uint @-> returning int_as_uint)
  
  let cull_face =
    foreign ~stub "glCullFace" (int_as_uint @-> returning void)
  
  let delete_buffers =
    foreign ~stub "glDeleteBuffers"
      (int @-> ba_as_uint32p @-> returning void)
  
  let delete_framebuffers =
    foreign ~stub "glDeleteFramebuffers"
      (int @-> ba_as_uint32p @-> returning void)
  
  let delete_program =
    foreign ~stub "glDeleteProgram" (int_as_uint @-> returning void)
  
  let delete_queries =
    foreign ~stub "glDeleteQueries"
      (int @-> ba_as_uint32p @-> returning void)
  
  let delete_renderbuffers =
    foreign ~stub "glDeleteRenderbuffers"
      (int @-> ba_as_uint32p @-> returning void)
  
  let delete_samplers =
    foreign ~stub "glDeleteSamplers"
      (int @-> ba_as_uint32p @-> returning void)
  
  let delete_shader =
    foreign ~stub "glDeleteShader" (int_as_uint @-> returning void)
  
  let delete_sync =
    foreign ~stub "glDeleteSync" (sync @-> returning void)
  
  let delete_textures =
    foreign ~stub "glDeleteTextures"
      (int @-> ba_as_uint32p @-> returning void)
  
  let delete_vertex_arrays =
    foreign ~stub "glDeleteVertexArrays"
      (int @-> ba_as_uint32p @-> returning void)
  
  let depth_func =
    foreign ~stub "glDepthFunc" (int_as_uint @-> returning void)
  
  let depth_mask =
    foreign ~stub "glDepthMask" (bool @-> returning void)
  
  let depth_range =
    foreign ~stub "glDepthRange" (double @-> double @-> returning void)
  
  let detach_shader =
    foreign ~stub "glDetachShader"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let disable =
    foreign ~stub "glDisable" (int_as_uint @-> returning void)
  
  let disable_vertex_attrib_array =
    foreign ~stub "glDisableVertexAttribArray"
      (int_as_uint @-> returning void)
  
  let disablei =
    foreign ~stub "glDisablei"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let draw_arrays =
    foreign ~stub "glDrawArrays"
      (int_as_uint @-> int @-> int @-> returning void)
  
  let draw_arrays_instanced =
    foreign ~stub "glDrawArraysInstanced"
      (int_as_uint @-> int @-> int @-> int @-> returning void)
  
  let draw_buffer =
    foreign ~stub "glDrawBuffer" (int_as_uint @-> returning void)
  
  let draw_buffers =
    foreign ~stub "glDrawBuffers" (int @-> ba_as_enump @-> returning void)
  
  let draw_elements =
    foreign ~stub "glDrawElements"
      (int_as_uint @-> int @-> int_as_uint @-> (ptr void) @-> returning void)
  
  let draw_elements mode count type_ indices =
    let indices = match indices with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    draw_elements mode count type_ indices
  
  let draw_elements_base_vertex =
    foreign ~stub "glDrawElementsBaseVertex"
      (int_as_uint @-> int @-> int_as_uint @-> (ptr void) @-> int @->
       returning void)
  
  let draw_elements_base_vertex mode count type_ indices basevertex =
    let indices = match indices with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    draw_elements_base_vertex mode count type_ indices basevertex
  
  let draw_elements_instanced =
    foreign ~stub "glDrawElementsInstanced"
      (int_as_uint @-> int @-> int_as_uint @-> (ptr void) @-> int @->
       returning void)
  
  let draw_elements_instanced mode count type_ indices instancecount =
    let indices = match indices with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    draw_elements_instanced mode count type_ indices instancecount
  
  let draw_elements_instanced_base_vertex =
    foreign ~stub "glDrawElementsInstancedBaseVertex"
      (int_as_uint @-> int @-> int_as_uint @-> (ptr void) @-> int @-> int @->
       returning void)
  
  let draw_elements_instanced_base_vertex mode count type_ indices
                                          instancecount basevertex =
    let indices = match indices with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    draw_elements_instanced_base_vertex mode count type_ indices
      instancecount basevertex
  
  let draw_range_elements =
    foreign ~stub "glDrawRangeElements"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int @->
       int_as_uint @-> (ptr void) @-> returning void)
  
  let draw_range_elements mode start end_ count type_ indices =
    let indices = match indices with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    draw_range_elements mode start end_ count type_ indices
  
  let draw_range_elements_base_vertex =
    foreign ~stub "glDrawRangeElementsBaseVertex"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int @->
       int_as_uint @-> (ptr void) @-> int @-> returning void)
  
  let draw_range_elements_base_vertex mode start end_ count type_ indices
                                      basevertex =
    let indices = match indices with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    draw_range_elements_base_vertex mode start end_ count type_ indices
      basevertex
  
  let enable =
    foreign ~stub "glEnable" (int_as_uint @-> returning void)
  
  let enable_vertex_attrib_array =
    foreign ~stub "glEnableVertexAttribArray"
      (int_as_uint @-> returning void)
  
  let enablei =
    foreign ~stub "glEnablei"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let end_conditional_render =
    foreign ~stub "glEndConditionalRender" (void @-> returning void)
  
  let end_query =
    foreign ~stub "glEndQuery" (int_as_uint @-> returning void)
  
  let end_transform_feedback =
    foreign ~stub "glEndTransformFeedback" (void @-> returning void)
  
  let fence_sync =
    foreign ~stub "glFenceSync"
      (int_as_uint @-> int_as_uint @-> returning sync)
  
  let finish =
    foreign ~stub "glFinish" (void @-> returning void)
  
  let flush =
    foreign ~stub "glFlush" (void @-> returning void)
  
  let flush_mapped_buffer_range =
    foreign ~stub "glFlushMappedBufferRange"
      (int_as_uint @-> int @-> int @-> returning void)
  
  let framebuffer_renderbuffer =
    foreign ~stub "glFramebufferRenderbuffer"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       returning void)
  
  let framebuffer_texture =
    foreign ~stub "glFramebufferTexture"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int @->
       returning void)
  
  let framebuffer_texture1d =
    foreign ~stub "glFramebufferTexture1D"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       int @-> returning void)
  
  let framebuffer_texture2d =
    foreign ~stub "glFramebufferTexture2D"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       int @-> returning void)
  
  let framebuffer_texture3d =
    foreign ~stub "glFramebufferTexture3D"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       int @-> int @-> returning void)
  
  let framebuffer_texture_layer =
    foreign ~stub "glFramebufferTextureLayer"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int @-> int @->
       returning void)
  
  let front_face =
    foreign ~stub "glFrontFace" (int_as_uint @-> returning void)
  
  let gen_buffers =
    foreign ~stub "glGenBuffers" (int @-> ba_as_uint32p @-> returning void)
  
  let gen_framebuffers =
    foreign ~stub "glGenFramebuffers"
      (int @-> ba_as_uint32p @-> returning void)
  
  let gen_queries =
    foreign ~stub "glGenQueries" (int @-> ba_as_uint32p @-> returning void)
  
  let gen_renderbuffers =
    foreign ~stub "glGenRenderbuffers"
      (int @-> ba_as_uint32p @-> returning void)
  
  let gen_samplers =
    foreign ~stub "glGenSamplers" (int @-> ba_as_uint32p @-> returning void)
  
  let gen_textures =
    foreign ~stub "glGenTextures" (int @-> ba_as_uint32p @-> returning void)
  
  let gen_vertex_arrays =
    foreign ~stub "glGenVertexArrays"
      (int @-> ba_as_uint32p @-> returning void)
  
  let generate_mipmap =
    foreign ~stub "glGenerateMipmap" (int_as_uint @-> returning void)
  
  let get_active_attrib =
    foreign ~stub "glGetActiveAttrib"
      (int_as_uint @-> int_as_uint @-> int @-> ba_opt_as_int32p @->
       ba_as_int32p @-> ba_as_enump @-> ba_as_charp @-> returning void)
  
  let get_active_uniform =
    foreign ~stub "glGetActiveUniform"
      (int_as_uint @-> int_as_uint @-> int @-> ba_opt_as_int32p @->
       ba_as_int32p @-> ba_as_enump @-> ba_as_charp @-> returning void)
  
  let get_active_uniform_block_name =
    foreign ~stub "glGetActiveUniformBlockName"
      (int_as_uint @-> int_as_uint @-> int @-> ba_opt_as_int32p @->
       ba_as_charp @-> returning void)
  
  let get_active_uniform_blockiv =
    foreign ~stub "glGetActiveUniformBlockiv"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> ba_as_int32p @->
       returning void)
  
  let get_active_uniform_name =
    foreign ~stub "glGetActiveUniformName"
      (int_as_uint @-> int_as_uint @-> int @-> ba_opt_as_int32p @->
       ba_as_charp @-> returning void)
  
  let get_active_uniformsiv =
    foreign ~stub "glGetActiveUniformsiv"
      (int_as_uint @-> int @-> ba_as_uint32p @-> int_as_uint @->
       ba_as_int32p @-> returning void)
  
  let get_attached_shaders =
    foreign ~stub "glGetAttachedShaders"
      (int_as_uint @-> int @-> ba_opt_as_int32p @-> ba_as_uint32p @->
       returning void)
  
  let get_attrib_location =
    foreign ~stub "glGetAttribLocation"
      (int_as_uint @-> string @-> returning int)
  
  let get_booleani_v =
    foreign ~stub "glGetBooleani_v"
      (int_as_uint @-> int_as_uint @-> ba_as_uint8p @-> returning void)
  
  let get_booleanv =
    foreign ~stub "glGetBooleanv"
      (int_as_uint @-> ba_as_uint8p @-> returning void)
  
  let get_buffer_parameteri64v =
    foreign ~stub "glGetBufferParameteri64v"
      (int_as_uint @-> int_as_uint @-> ba_as_int64p @-> returning void)
  
  let get_buffer_parameteriv =
    foreign ~stub "glGetBufferParameteriv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_buffer_pointerv =
    foreign ~stub "glGetBufferPointerv"
      (int_as_uint @-> int_as_uint @-> ba_as_nativeint @-> returning void)
  
  let get_buffer_sub_data =
    foreign ~stub "glGetBufferSubData"
      (int_as_uint @-> int @-> int @-> (ptr void) @-> returning void)
  
  let get_buffer_sub_data target offset size data =
    let data = to_voidp (bigarray_start array1 data) in
    get_buffer_sub_data target offset size data
  
  let get_compressed_tex_image =
    foreign ~stub "glGetCompressedTexImage"
      (int_as_uint @-> int @-> (ptr void) @-> returning void)
  
  let get_compressed_tex_image target level img =
    let img = match img with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    get_compressed_tex_image target level img
  
  let get_doublev =
    foreign ~stub "glGetDoublev"
      (int_as_uint @-> ba_as_float64p @-> returning void)
  
  let get_error =
    foreign ~stub "glGetError" (void @-> returning int_as_uint)
  
  let get_floatv =
    foreign ~stub "glGetFloatv"
      (int_as_uint @-> ba_as_float32p @-> returning void)
  
  let get_frag_data_index =
    foreign ~stub "glGetFragDataIndex"
      (int_as_uint @-> string @-> returning int)
  
  let get_frag_data_location =
    foreign ~stub "glGetFragDataLocation"
      (int_as_uint @-> string @-> returning int)
  
  let get_framebuffer_attachment_parameteriv =
    foreign ~stub "glGetFramebufferAttachmentParameteriv"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> ba_as_int32p @->
       returning void)
  
  let get_integer64i_v =
    foreign ~stub "glGetInteger64i_v"
      (int_as_uint @-> int_as_uint @-> ba_as_int64p @-> returning void)
  
  let get_integer64v =
    foreign ~stub "glGetInteger64v"
      (int_as_uint @-> ba_as_int64p @-> returning void)
  
  let get_integeri_v =
    foreign ~stub "glGetIntegeri_v"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_integerv =
    foreign ~stub "glGetIntegerv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_multisamplefv =
    foreign ~stub "glGetMultisamplefv"
      (int_as_uint @-> int_as_uint @-> ba_as_float32p @-> returning void)
  
  let get_program_info_log =
    foreign ~stub "glGetProgramInfoLog"
      (int_as_uint @-> int @-> ba_opt_as_int32p @-> ba_as_charp @->
       returning void)
  
  let get_programiv =
    foreign ~stub "glGetProgramiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_query_objecti64v =
    foreign ~stub "glGetQueryObjecti64v"
      (int_as_uint @-> int_as_uint @-> ba_as_int64p @-> returning void)
  
  let get_query_objectiv =
    foreign ~stub "glGetQueryObjectiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_query_objectui64v =
    foreign ~stub "glGetQueryObjectui64v"
      (int_as_uint @-> int_as_uint @-> ba_as_uint64p @-> returning void)
  
  let get_query_objectuiv =
    foreign ~stub "glGetQueryObjectuiv"
      (int_as_uint @-> int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let get_queryiv =
    foreign ~stub "glGetQueryiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_renderbuffer_parameteriv =
    foreign ~stub "glGetRenderbufferParameteriv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_sampler_parameter_iiv =
    foreign ~stub "glGetSamplerParameterIiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_sampler_parameter_iuiv =
    foreign ~stub "glGetSamplerParameterIuiv"
      (int_as_uint @-> int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let get_sampler_parameterfv =
    foreign ~stub "glGetSamplerParameterfv"
      (int_as_uint @-> int_as_uint @-> ba_as_float32p @-> returning void)
  
  let get_sampler_parameteriv =
    foreign ~stub "glGetSamplerParameteriv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_shader_info_log =
    foreign ~stub "glGetShaderInfoLog"
      (int_as_uint @-> int @-> ba_opt_as_int32p @-> ba_as_charp @->
       returning void)
  
  let get_shader_source =
    foreign ~stub "glGetShaderSource"
      (int_as_uint @-> int @-> ba_opt_as_int32p @-> ba_as_charp @->
       returning void)
  
  let get_shaderiv =
    foreign ~stub "glGetShaderiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_string =
    foreign ~stub "glGetString" (int_as_uint @-> returning string_opt)
  
  let get_stringi =
    foreign ~stub "glGetStringi"
      (int_as_uint @-> int_as_uint @-> returning string_opt)
  
  let get_synciv =
    foreign ~stub "glGetSynciv"
      (sync @-> int_as_uint @-> int @-> ba_opt_as_int32p @-> ba_as_int32p @->
       returning void)
  
  let get_tex_image =
    foreign ~stub "glGetTexImage"
      (int_as_uint @-> int @-> int_as_uint @-> int_as_uint @-> (ptr void) @->
       returning void)
  
  let get_tex_image target level format type_ pixels =
    let pixels = to_voidp (bigarray_start array1 pixels) in
    get_tex_image target level format type_ pixels
  
  let get_tex_level_parameterfv =
    foreign ~stub "glGetTexLevelParameterfv"
      (int_as_uint @-> int @-> int_as_uint @-> ba_as_float32p @->
       returning void)
  
  let get_tex_level_parameteriv =
    foreign ~stub "glGetTexLevelParameteriv"
      (int_as_uint @-> int @-> int_as_uint @-> ba_as_int32p @->
       returning void)
  
  let get_tex_parameter_iiv =
    foreign ~stub "glGetTexParameterIiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_tex_parameter_iuiv =
    foreign ~stub "glGetTexParameterIuiv"
      (int_as_uint @-> int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let get_tex_parameterfv =
    foreign ~stub "glGetTexParameterfv"
      (int_as_uint @-> int_as_uint @-> ba_as_float32p @-> returning void)
  
  let get_tex_parameteriv =
    foreign ~stub "glGetTexParameteriv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_transform_feedback_varying =
    foreign ~stub "glGetTransformFeedbackVarying"
      (int_as_uint @-> int_as_uint @-> int @-> ba_opt_as_int32p @->
       ba_as_int32p @-> ba_as_enump @-> ba_as_charp @-> returning void)
  
  let get_uniform_block_index =
    foreign ~stub "glGetUniformBlockIndex"
      (int_as_uint @-> string @-> returning int_as_uint)
  
  let get_uniform_indices =
    foreign ~stub "glGetUniformIndices"
      (int_as_uint @-> int @-> ptr string @-> ptr void @-> returning void)
  
  let get_uniform_indices program names indices =
    let count = List.length names in
    let names = CArray.(start (of_list string names)) in
    let indices = to_voidp (bigarray_start array1 indices) in
    get_uniform_indices program count names indices
  
  let get_uniform_location =
    foreign ~stub "glGetUniformLocation"
      (int_as_uint @-> string @-> returning int)
  
  let get_uniformfv =
    foreign ~stub "glGetUniformfv"
      (int_as_uint @-> int @-> ba_as_float32p @-> returning void)
  
  let get_uniformiv =
    foreign ~stub "glGetUniformiv"
      (int_as_uint @-> int @-> ba_as_int32p @-> returning void)
  
  let get_uniformuiv =
    foreign ~stub "glGetUniformuiv"
      (int_as_uint @-> int @-> ba_as_uint32p @-> returning void)
  
  let get_vertex_attrib_iiv =
    foreign ~stub "glGetVertexAttribIiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let get_vertex_attrib_iuiv =
    foreign ~stub "glGetVertexAttribIuiv"
      (int_as_uint @-> int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let get_vertex_attrib_pointerv =
    foreign ~stub "glGetVertexAttribPointerv"
      (int_as_uint @-> int_as_uint @-> ba_as_nativeint @-> returning void)
  
  let get_vertex_attribdv =
    foreign ~stub "glGetVertexAttribdv"
      (int_as_uint @-> int_as_uint @-> ba_as_float64p @-> returning void)
  
  let get_vertex_attribfv =
    foreign ~stub "glGetVertexAttribfv"
      (int_as_uint @-> int_as_uint @-> ba_as_float32p @-> returning void)
  
  let get_vertex_attribiv =
    foreign ~stub "glGetVertexAttribiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let hint =
    foreign ~stub "glHint" (int_as_uint @-> int_as_uint @-> returning void)
  
  let is_buffer =
    foreign ~stub "glIsBuffer" (int_as_uint @-> returning bool)
  
  let is_enabled =
    foreign ~stub "glIsEnabled" (int_as_uint @-> returning bool)
  
  let is_enabledi =
    foreign ~stub "glIsEnabledi"
      (int_as_uint @-> int_as_uint @-> returning bool)
  
  let is_framebuffer =
    foreign ~stub "glIsFramebuffer" (int_as_uint @-> returning bool)
  
  let is_program =
    foreign ~stub "glIsProgram" (int_as_uint @-> returning bool)
  
  let is_query =
    foreign ~stub "glIsQuery" (int_as_uint @-> returning bool)
  
  let is_renderbuffer =
    foreign ~stub "glIsRenderbuffer" (int_as_uint @-> returning bool)
  
  let is_sampler =
    foreign ~stub "glIsSampler" (int_as_uint @-> returning bool)
  
  let is_shader =
    foreign ~stub "glIsShader" (int_as_uint @-> returning bool)
  
  let is_sync =
    foreign ~stub "glIsSync" (sync @-> returning bool)
  
  let is_texture =
    foreign ~stub "glIsTexture" (int_as_uint @-> returning bool)
  
  let is_vertex_array =
    foreign ~stub "glIsVertexArray" (int_as_uint @-> returning bool)
  
  let line_width =
    foreign ~stub "glLineWidth" (float @-> returning void)
  
  let link_program =
    foreign ~stub "glLinkProgram" (int_as_uint @-> returning void)
  
  let logic_op =
    foreign ~stub "glLogicOp" (int_as_uint @-> returning void)
  
  let map_buffer =
    foreign ~stub "glMapBuffer"
      (int_as_uint @-> int_as_uint @-> returning (ptr void))
  
  let map_buffer target len access kind =
    let p = map_buffer target access in
    let p = coerce (ptr void) (access_ptr_typ_of_ba_kind kind) p in
    bigarray_of_ptr array1 len kind p
  
  let map_buffer_range =
    foreign ~stub "glMapBufferRange"
      (int_as_uint @-> int @-> int @-> int_as_uint @-> returning (ptr void))
  
  let map_buffer_range target offset len access kind =
    let len_bytes = ba_kind_byte_size kind * len in
    let p = map_buffer_range target offset len_bytes access in
    let p = coerce (ptr void) (access_ptr_typ_of_ba_kind kind) p in
    bigarray_of_ptr array1 len kind p
  
  let multi_draw_arrays =
    foreign ~stub "glMultiDrawArrays"
      (int_as_uint @-> ba_as_int32p @-> ba_as_int32p @-> int @->
       returning void)
  
  let multi_draw_elements =
    foreign ~stub "glMultiDrawElements"
      (int_as_uint @-> ba_as_int32p @-> int_as_uint @-> (ptr void) @->
       int @-> returning void)
  
  let multi_draw_elements mode count type_ indices drawcount =
    let indices = to_voidp (bigarray_start array1 indices) in
    multi_draw_elements mode count type_ indices drawcount
  
  let multi_draw_elements_base_vertex =
    foreign ~stub "glMultiDrawElementsBaseVertex"
      (int_as_uint @-> ba_as_int32p @-> int_as_uint @-> (ptr void) @->
       int @-> ba_as_int32p @-> returning void)
  
  let multi_draw_elements_base_vertex mode count type_ indices drawcount
                                      basevertex =
    let indices = to_voidp (bigarray_start array1 indices) in
    multi_draw_elements_base_vertex mode count type_ indices drawcount
      basevertex
  
  let pixel_storef =
    foreign ~stub "glPixelStoref" (int_as_uint @-> float @-> returning void)
  
  let pixel_storei =
    foreign ~stub "glPixelStorei" (int_as_uint @-> int @-> returning void)
  
  let point_parameterf =
    foreign ~stub "glPointParameterf"
      (int_as_uint @-> float @-> returning void)
  
  let point_parameterfv =
    foreign ~stub "glPointParameterfv"
      (int_as_uint @-> ba_as_float32p @-> returning void)
  
  let point_parameteri =
    foreign ~stub "glPointParameteri"
      (int_as_uint @-> int @-> returning void)
  
  let point_parameteriv =
    foreign ~stub "glPointParameteriv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let point_size =
    foreign ~stub "glPointSize" (float @-> returning void)
  
  let polygon_mode =
    foreign ~stub "glPolygonMode"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let polygon_offset =
    foreign ~stub "glPolygonOffset" (float @-> float @-> returning void)
  
  let primitive_restart_index =
    foreign ~stub "glPrimitiveRestartIndex" (int_as_uint @-> returning void)
  
  let provoking_vertex =
    foreign ~stub "glProvokingVertex" (int_as_uint @-> returning void)
  
  let query_counter =
    foreign ~stub "glQueryCounter"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let read_buffer =
    foreign ~stub "glReadBuffer" (int_as_uint @-> returning void)
  
  let read_pixels =
    foreign ~stub "glReadPixels"
      (int @-> int @-> int @-> int @-> int_as_uint @-> int_as_uint @->
       (ptr void) @-> returning void)
  
  let read_pixels x y width height format type_ pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    read_pixels x y width height format type_ pixels
  
  let renderbuffer_storage =
    foreign ~stub "glRenderbufferStorage"
      (int_as_uint @-> int_as_uint @-> int @-> int @-> returning void)
  
  let renderbuffer_storage_multisample =
    foreign ~stub "glRenderbufferStorageMultisample"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @->
       returning void)
  
  let sample_coverage =
    foreign ~stub "glSampleCoverage" (float @-> bool @-> returning void)
  
  let sample_maski =
    foreign ~stub "glSampleMaski"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let sampler_parameter_iiv =
    foreign ~stub "glSamplerParameterIiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let sampler_parameter_iuiv =
    foreign ~stub "glSamplerParameterIuiv"
      (int_as_uint @-> int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let sampler_parameterf =
    foreign ~stub "glSamplerParameterf"
      (int_as_uint @-> int_as_uint @-> float @-> returning void)
  
  let sampler_parameterfv =
    foreign ~stub "glSamplerParameterfv"
      (int_as_uint @-> int_as_uint @-> ba_as_float32p @-> returning void)
  
  let sampler_parameteri =
    foreign ~stub "glSamplerParameteri"
      (int_as_uint @-> int_as_uint @-> int @-> returning void)
  
  let sampler_parameteriv =
    foreign ~stub "glSamplerParameteriv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let scissor =
    foreign ~stub "glScissor"
      (int @-> int @-> int @-> int @-> returning void)
  
  let shader_source =
    foreign ~stub "glShaderSource"
      (int_as_uint @-> int @-> ptr string @-> ptr void @-> returning void)
  
  let shader_source sh src =
    let src = allocate string src in
    shader_source sh 1 src null
  
  let stencil_func =
    foreign ~stub "glStencilFunc"
      (int_as_uint @-> int @-> int_as_uint @-> returning void)
  
  let stencil_func_separate =
    foreign ~stub "glStencilFuncSeparate"
      (int_as_uint @-> int_as_uint @-> int @-> int_as_uint @->
       returning void)
  
  let stencil_mask =
    foreign ~stub "glStencilMask" (int_as_uint @-> returning void)
  
  let stencil_mask_separate =
    foreign ~stub "glStencilMaskSeparate"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let stencil_op =
    foreign ~stub "glStencilOp"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> returning void)
  
  let stencil_op_separate =
    foreign ~stub "glStencilOpSeparate"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       returning void)
  
  let tex_buffer =
    foreign ~stub "glTexBuffer"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> returning void)
  
  let tex_image1d =
    foreign ~stub "glTexImage1D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int_as_uint @->
       int_as_uint @-> (ptr void) @-> returning void)
  
  let tex_image1d target level internalformat width border format type_
                  pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    tex_image1d target level internalformat width border format type_ pixels
  
  let tex_image2d =
    foreign ~stub "glTexImage2D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @->
       int_as_uint @-> int_as_uint @-> (ptr void) @-> returning void)
  
  let tex_image2d target level internalformat width height border format
                  type_ pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    tex_image2d target level internalformat width height border format type_
      pixels
  
  let tex_image2d_multisample =
    foreign ~stub "glTexImage2DMultisample"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> bool @->
       returning void)
  
  let tex_image3d =
    foreign ~stub "glTexImage3D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @-> int @->
       int_as_uint @-> int_as_uint @-> (ptr void) @-> returning void)
  
  let tex_image3d target level internalformat width height depth border
                  format type_ pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    tex_image3d target level internalformat width height depth border format
      type_ pixels
  
  let tex_image3d_multisample =
    foreign ~stub "glTexImage3DMultisample"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> int @-> int @->
       bool @-> returning void)
  
  let tex_parameter_iiv =
    foreign ~stub "glTexParameterIiv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let tex_parameter_iuiv =
    foreign ~stub "glTexParameterIuiv"
      (int_as_uint @-> int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let tex_parameterf =
    foreign ~stub "glTexParameterf"
      (int_as_uint @-> int_as_uint @-> float @-> returning void)
  
  let tex_parameterfv =
    foreign ~stub "glTexParameterfv"
      (int_as_uint @-> int_as_uint @-> ba_as_float32p @-> returning void)
  
  let tex_parameteri =
    foreign ~stub "glTexParameteri"
      (int_as_uint @-> int_as_uint @-> int @-> returning void)
  
  let tex_parameteriv =
    foreign ~stub "glTexParameteriv"
      (int_as_uint @-> int_as_uint @-> ba_as_int32p @-> returning void)
  
  let tex_sub_image1d =
    foreign ~stub "glTexSubImage1D"
      (int_as_uint @-> int @-> int @-> int @-> int_as_uint @->
       int_as_uint @-> (ptr void) @-> returning void)
  
  let tex_sub_image1d target level xoffset width format type_ pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    tex_sub_image1d target level xoffset width format type_ pixels
  
  let tex_sub_image2d =
    foreign ~stub "glTexSubImage2D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @->
       int_as_uint @-> int_as_uint @-> (ptr void) @-> returning void)
  
  let tex_sub_image2d target level xoffset yoffset width height format type_
                      pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    tex_sub_image2d target level xoffset yoffset width height format type_
      pixels
  
  let tex_sub_image3d =
    foreign ~stub "glTexSubImage3D"
      (int_as_uint @-> int @-> int @-> int @-> int @-> int @-> int @->
       int @-> int_as_uint @-> int_as_uint @-> (ptr void) @-> returning void)
  
  let tex_sub_image3d target level xoffset yoffset zoffset width height depth
                      format type_ pixels =
    let pixels = match pixels with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    tex_sub_image3d target level xoffset yoffset zoffset width height depth
      format type_ pixels
  
  let transform_feedback_varyings =
    foreign ~stub "glTransformFeedbackVaryings"
      (int_as_uint @-> int @-> ptr string @-> int_as_uint @-> returning void)
  
  let transform_feedback_varyings program varyings mode =
    let count = List.length varyings in
    let varyings = CArray.(start (of_list string varyings)) in
    transform_feedback_varyings program count varyings mode
  
  let uniform1f =
    foreign ~stub "glUniform1f" (int @-> float @-> returning void)
  
  let uniform1fv =
    foreign ~stub "glUniform1fv"
      (int @-> int @-> ba_as_float32p @-> returning void)
  
  let uniform1i =
    foreign ~stub "glUniform1i" (int @-> int @-> returning void)
  
  let uniform1iv =
    foreign ~stub "glUniform1iv"
      (int @-> int @-> ba_as_int32p @-> returning void)
  
  let uniform1ui =
    foreign ~stub "glUniform1ui" (int @-> int_as_uint @-> returning void)
  
  let uniform1uiv =
    foreign ~stub "glUniform1uiv"
      (int @-> int @-> ba_as_uint32p @-> returning void)
  
  let uniform2f =
    foreign ~stub "glUniform2f" (int @-> float @-> float @-> returning void)
  
  let uniform2fv =
    foreign ~stub "glUniform2fv"
      (int @-> int @-> ba_as_float32p @-> returning void)
  
  let uniform2i =
    foreign ~stub "glUniform2i" (int @-> int @-> int @-> returning void)
  
  let uniform2iv =
    foreign ~stub "glUniform2iv"
      (int @-> int @-> ba_as_int32p @-> returning void)
  
  let uniform2ui =
    foreign ~stub "glUniform2ui"
      (int @-> int_as_uint @-> int_as_uint @-> returning void)
  
  let uniform2uiv =
    foreign ~stub "glUniform2uiv"
      (int @-> int @-> ba_as_uint32p @-> returning void)
  
  let uniform3f =
    foreign ~stub "glUniform3f"
      (int @-> float @-> float @-> float @-> returning void)
  
  let uniform3fv =
    foreign ~stub "glUniform3fv"
      (int @-> int @-> ba_as_float32p @-> returning void)
  
  let uniform3i =
    foreign ~stub "glUniform3i"
      (int @-> int @-> int @-> int @-> returning void)
  
  let uniform3iv =
    foreign ~stub "glUniform3iv"
      (int @-> int @-> ba_as_int32p @-> returning void)
  
  let uniform3ui =
    foreign ~stub "glUniform3ui"
      (int @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       returning void)
  
  let uniform3uiv =
    foreign ~stub "glUniform3uiv"
      (int @-> int @-> ba_as_uint32p @-> returning void)
  
  let uniform4f =
    foreign ~stub "glUniform4f"
      (int @-> float @-> float @-> float @-> float @-> returning void)
  
  let uniform4fv =
    foreign ~stub "glUniform4fv"
      (int @-> int @-> ba_as_float32p @-> returning void)
  
  let uniform4i =
    foreign ~stub "glUniform4i"
      (int @-> int @-> int @-> int @-> int @-> returning void)
  
  let uniform4iv =
    foreign ~stub "glUniform4iv"
      (int @-> int @-> ba_as_int32p @-> returning void)
  
  let uniform4ui =
    foreign ~stub "glUniform4ui"
      (int @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       int_as_uint @-> returning void)
  
  let uniform4uiv =
    foreign ~stub "glUniform4uiv"
      (int @-> int @-> ba_as_uint32p @-> returning void)
  
  let uniform_block_binding =
    foreign ~stub "glUniformBlockBinding"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> returning void)
  
  let uniform_matrix2fv =
    foreign ~stub "glUniformMatrix2fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix2x3fv =
    foreign ~stub "glUniformMatrix2x3fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix2x4fv =
    foreign ~stub "glUniformMatrix2x4fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix3fv =
    foreign ~stub "glUniformMatrix3fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix3x2fv =
    foreign ~stub "glUniformMatrix3x2fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix3x4fv =
    foreign ~stub "glUniformMatrix3x4fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix4fv =
    foreign ~stub "glUniformMatrix4fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix4x2fv =
    foreign ~stub "glUniformMatrix4x2fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let uniform_matrix4x3fv =
    foreign ~stub "glUniformMatrix4x3fv"
      (int @-> int @-> bool @-> ba_as_float32p @-> returning void)
  
  let unmap_buffer =
    foreign ~stub "glUnmapBuffer" (int_as_uint @-> returning bool)
  
  let use_program =
    foreign ~stub "glUseProgram" (int_as_uint @-> returning void)
  
  let validate_program =
    foreign ~stub "glValidateProgram" (int_as_uint @-> returning void)
  
  let vertex_attrib1d =
    foreign ~stub "glVertexAttrib1d"
      (int_as_uint @-> double @-> returning void)
  
  let vertex_attrib1dv =
    foreign ~stub "glVertexAttrib1dv"
      (int_as_uint @-> ba_as_float64p @-> returning void)
  
  let vertex_attrib1f =
    foreign ~stub "glVertexAttrib1f"
      (int_as_uint @-> float @-> returning void)
  
  let vertex_attrib1fv =
    foreign ~stub "glVertexAttrib1fv"
      (int_as_uint @-> ba_as_float32p @-> returning void)
  
  let vertex_attrib1s =
    foreign ~stub "glVertexAttrib1s"
      (int_as_uint @-> short @-> returning void)
  
  let vertex_attrib1sv =
    foreign ~stub "glVertexAttrib1sv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib2d =
    foreign ~stub "glVertexAttrib2d"
      (int_as_uint @-> double @-> double @-> returning void)
  
  let vertex_attrib2dv =
    foreign ~stub "glVertexAttrib2dv"
      (int_as_uint @-> ba_as_float64p @-> returning void)
  
  let vertex_attrib2f =
    foreign ~stub "glVertexAttrib2f"
      (int_as_uint @-> float @-> float @-> returning void)
  
  let vertex_attrib2fv =
    foreign ~stub "glVertexAttrib2fv"
      (int_as_uint @-> ba_as_float32p @-> returning void)
  
  let vertex_attrib2s =
    foreign ~stub "glVertexAttrib2s"
      (int_as_uint @-> short @-> short @-> returning void)
  
  let vertex_attrib2sv =
    foreign ~stub "glVertexAttrib2sv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib3d =
    foreign ~stub "glVertexAttrib3d"
      (int_as_uint @-> double @-> double @-> double @-> returning void)
  
  let vertex_attrib3dv =
    foreign ~stub "glVertexAttrib3dv"
      (int_as_uint @-> ba_as_float64p @-> returning void)
  
  let vertex_attrib3f =
    foreign ~stub "glVertexAttrib3f"
      (int_as_uint @-> float @-> float @-> float @-> returning void)
  
  let vertex_attrib3fv =
    foreign ~stub "glVertexAttrib3fv"
      (int_as_uint @-> ba_as_float32p @-> returning void)
  
  let vertex_attrib3s =
    foreign ~stub "glVertexAttrib3s"
      (int_as_uint @-> short @-> short @-> short @-> returning void)
  
  let vertex_attrib3sv =
    foreign ~stub "glVertexAttrib3sv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib4nbv =
    foreign ~stub "glVertexAttrib4Nbv"
      (int_as_uint @-> ba_as_int8p @-> returning void)
  
  let vertex_attrib4niv =
    foreign ~stub "glVertexAttrib4Niv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let vertex_attrib4nsv =
    foreign ~stub "glVertexAttrib4Nsv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib4nub =
    foreign ~stub "glVertexAttrib4Nub"
      (int_as_uint @-> int_as_uint8_t @-> int_as_uint8_t @->
       int_as_uint8_t @-> int_as_uint8_t @-> returning void)
  
  let vertex_attrib4nubv =
    foreign ~stub "glVertexAttrib4Nubv"
      (int_as_uint @-> ba_as_uint8p @-> returning void)
  
  let vertex_attrib4nuiv =
    foreign ~stub "glVertexAttrib4Nuiv"
      (int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let vertex_attrib4nusv =
    foreign ~stub "glVertexAttrib4Nusv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib4bv =
    foreign ~stub "glVertexAttrib4bv"
      (int_as_uint @-> ba_as_int8p @-> returning void)
  
  let vertex_attrib4d =
    foreign ~stub "glVertexAttrib4d"
      (int_as_uint @-> double @-> double @-> double @-> double @->
       returning void)
  
  let vertex_attrib4dv =
    foreign ~stub "glVertexAttrib4dv"
      (int_as_uint @-> ba_as_float64p @-> returning void)
  
  let vertex_attrib4f =
    foreign ~stub "glVertexAttrib4f"
      (int_as_uint @-> float @-> float @-> float @-> float @->
       returning void)
  
  let vertex_attrib4fv =
    foreign ~stub "glVertexAttrib4fv"
      (int_as_uint @-> ba_as_float32p @-> returning void)
  
  let vertex_attrib4iv =
    foreign ~stub "glVertexAttrib4iv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let vertex_attrib4s =
    foreign ~stub "glVertexAttrib4s"
      (int_as_uint @-> short @-> short @-> short @-> short @->
       returning void)
  
  let vertex_attrib4sv =
    foreign ~stub "glVertexAttrib4sv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib4ubv =
    foreign ~stub "glVertexAttrib4ubv"
      (int_as_uint @-> ba_as_uint8p @-> returning void)
  
  let vertex_attrib4uiv =
    foreign ~stub "glVertexAttrib4uiv"
      (int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let vertex_attrib4usv =
    foreign ~stub "glVertexAttrib4usv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib_divisor =
    foreign ~stub "glVertexAttribDivisor"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let vertex_attrib_i1i =
    foreign ~stub "glVertexAttribI1i"
      (int_as_uint @-> int @-> returning void)
  
  let vertex_attrib_i1iv =
    foreign ~stub "glVertexAttribI1iv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let vertex_attrib_i1ui =
    foreign ~stub "glVertexAttribI1ui"
      (int_as_uint @-> int_as_uint @-> returning void)
  
  let vertex_attrib_i1uiv =
    foreign ~stub "glVertexAttribI1uiv"
      (int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let vertex_attrib_i2i =
    foreign ~stub "glVertexAttribI2i"
      (int_as_uint @-> int @-> int @-> returning void)
  
  let vertex_attrib_i2iv =
    foreign ~stub "glVertexAttribI2iv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let vertex_attrib_i2ui =
    foreign ~stub "glVertexAttribI2ui"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> returning void)
  
  let vertex_attrib_i2uiv =
    foreign ~stub "glVertexAttribI2uiv"
      (int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let vertex_attrib_i3i =
    foreign ~stub "glVertexAttribI3i"
      (int_as_uint @-> int @-> int @-> int @-> returning void)
  
  let vertex_attrib_i3iv =
    foreign ~stub "glVertexAttribI3iv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let vertex_attrib_i3ui =
    foreign ~stub "glVertexAttribI3ui"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       returning void)
  
  let vertex_attrib_i3uiv =
    foreign ~stub "glVertexAttribI3uiv"
      (int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let vertex_attrib_i4bv =
    foreign ~stub "glVertexAttribI4bv"
      (int_as_uint @-> ba_as_int8p @-> returning void)
  
  let vertex_attrib_i4i =
    foreign ~stub "glVertexAttribI4i"
      (int_as_uint @-> int @-> int @-> int @-> int @-> returning void)
  
  let vertex_attrib_i4iv =
    foreign ~stub "glVertexAttribI4iv"
      (int_as_uint @-> ba_as_int32p @-> returning void)
  
  let vertex_attrib_i4sv =
    foreign ~stub "glVertexAttribI4sv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib_i4ubv =
    foreign ~stub "glVertexAttribI4ubv"
      (int_as_uint @-> ba_as_uint8p @-> returning void)
  
  let vertex_attrib_i4ui =
    foreign ~stub "glVertexAttribI4ui"
      (int_as_uint @-> int_as_uint @-> int_as_uint @-> int_as_uint @->
       int_as_uint @-> returning void)
  
  let vertex_attrib_i4uiv =
    foreign ~stub "glVertexAttribI4uiv"
      (int_as_uint @-> ba_as_uint32p @-> returning void)
  
  let vertex_attrib_i4usv =
    foreign ~stub "glVertexAttribI4usv"
      (int_as_uint @-> ba_as_uint16p @-> returning void)
  
  let vertex_attrib_ipointer =
    foreign ~stub "glVertexAttribIPointer"
      (int_as_uint @-> int @-> int_as_uint @-> int @-> (ptr void) @->
       returning void)
  
  let vertex_attrib_ipointer index size type_ stride pointer =
    let pointer = match pointer with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    vertex_attrib_ipointer index size type_ stride pointer
  
  let vertex_attrib_p1ui =
    foreign ~stub "glVertexAttribP1ui"
      (int_as_uint @-> int_as_uint @-> bool @-> int_as_uint @->
       returning void)
  
  let vertex_attrib_p1uiv =
    foreign ~stub "glVertexAttribP1uiv"
      (int_as_uint @-> int_as_uint @-> bool @-> ba_as_uint32p @->
       returning void)
  
  let vertex_attrib_p2ui =
    foreign ~stub "glVertexAttribP2ui"
      (int_as_uint @-> int_as_uint @-> bool @-> int_as_uint @->
       returning void)
  
  let vertex_attrib_p2uiv =
    foreign ~stub "glVertexAttribP2uiv"
      (int_as_uint @-> int_as_uint @-> bool @-> ba_as_uint32p @->
       returning void)
  
  let vertex_attrib_p3ui =
    foreign ~stub "glVertexAttribP3ui"
      (int_as_uint @-> int_as_uint @-> bool @-> int_as_uint @->
       returning void)
  
  let vertex_attrib_p3uiv =
    foreign ~stub "glVertexAttribP3uiv"
      (int_as_uint @-> int_as_uint @-> bool @-> ba_as_uint32p @->
       returning void)
  
  let vertex_attrib_p4ui =
    foreign ~stub "glVertexAttribP4ui"
      (int_as_uint @-> int_as_uint @-> bool @-> int_as_uint @->
       returning void)
  
  let vertex_attrib_p4uiv =
    foreign ~stub "glVertexAttribP4uiv"
      (int_as_uint @-> int_as_uint @-> bool @-> ba_as_uint32p @->
       returning void)
  
  let vertex_attrib_pointer =
    foreign ~stub "glVertexAttribPointer"
      (int_as_uint @-> int @-> int_as_uint @-> bool @-> int @->
       (ptr void) @-> returning void)
  
  let vertex_attrib_pointer index size type_ normalized stride pointer =
    let pointer = match pointer with
    | `Offset o -> ptr_of_raw_address (Nativeint.of_int o)
    | `Data b -> to_voidp (bigarray_start array1 b)
    in
    vertex_attrib_pointer index size type_ normalized stride pointer
  
  let viewport =
    foreign ~stub "glViewport"
      (int @-> int @-> int @-> int @-> returning void)
  
  let wait_sync =
    foreign ~stub "glWaitSync"
      (sync @-> int_as_uint @-> int64_as_uint64_t @-> returning void)
  

  (* Enums *)

  let active_attributes = 0x8B89
  let active_attribute_max_length = 0x8B8A
  let active_texture_enum = 0x84E0
  let active_uniforms = 0x8B86
  let active_uniform_blocks = 0x8A36
  let active_uniform_block_max_name_length = 0x8A35
  let active_uniform_max_length = 0x8B87
  let aliased_line_width_range = 0x846E
  let alpha = 0x1906
  let already_signaled = 0x911A
  let always = 0x207
  let and_ = 0x1501
  let and_inverted = 0x1504
  let and_reverse = 0x1502
  let any_samples_passed = 0x8C2F
  let array_buffer = 0x8892
  let array_buffer_binding = 0x8894
  let attached_shaders = 0x8B85
  let back = 0x405
  let back_left = 0x402
  let back_right = 0x403
  let bgr = 0x80E0
  let bgra = 0x80E1
  let bgra_integer = 0x8D9B
  let bgr_integer = 0x8D9A
  let blend = 0xBE2
  let blend_dst = 0xBE0
  let blend_dst_alpha = 0x80CA
  let blend_dst_rgb = 0x80C8
  let blend_equation_alpha = 0x883D
  let blend_equation_rgb = 0x8009
  let blend_src = 0xBE1
  let blend_src_alpha = 0x80CB
  let blend_src_rgb = 0x80C9
  let blue = 0x1905
  let blue_integer = 0x8D96
  let bool = 0x8B56
  let bool_vec2 = 0x8B57
  let bool_vec3 = 0x8B58
  let bool_vec4 = 0x8B59
  let buffer_access = 0x88BB
  let buffer_access_flags = 0x911F
  let buffer_mapped = 0x88BC
  let buffer_map_length = 0x9120
  let buffer_map_offset = 0x9121
  let buffer_map_pointer = 0x88BD
  let buffer_size = 0x8764
  let buffer_usage = 0x8765
  let byte = 0x1400
  let ccw = 0x901
  let clamp_read_color = 0x891C
  let clamp_to_border = 0x812D
  let clamp_to_edge = 0x812F
  let clear_enum = 0x1500
  let clip_distance0 = 0x3000
  let clip_distance1 = 0x3001
  let clip_distance2 = 0x3002
  let clip_distance3 = 0x3003
  let clip_distance4 = 0x3004
  let clip_distance5 = 0x3005
  let clip_distance6 = 0x3006
  let clip_distance7 = 0x3007
  let color = 0x1800
  let color_attachment0 = 0x8CE0
  let color_attachment1 = 0x8CE1
  let color_attachment10 = 0x8CEA
  let color_attachment11 = 0x8CEB
  let color_attachment12 = 0x8CEC
  let color_attachment13 = 0x8CED
  let color_attachment14 = 0x8CEE
  let color_attachment15 = 0x8CEF
  let color_attachment16 = 0x8CF0
  let color_attachment17 = 0x8CF1
  let color_attachment18 = 0x8CF2
  let color_attachment19 = 0x8CF3
  let color_attachment2 = 0x8CE2
  let color_attachment20 = 0x8CF4
  let color_attachment21 = 0x8CF5
  let color_attachment22 = 0x8CF6
  let color_attachment23 = 0x8CF7
  let color_attachment24 = 0x8CF8
  let color_attachment25 = 0x8CF9
  let color_attachment26 = 0x8CFA
  let color_attachment27 = 0x8CFB
  let color_attachment28 = 0x8CFC
  let color_attachment29 = 0x8CFD
  let color_attachment3 = 0x8CE3
  let color_attachment30 = 0x8CFE
  let color_attachment31 = 0x8CFF
  let color_attachment4 = 0x8CE4
  let color_attachment5 = 0x8CE5
  let color_attachment6 = 0x8CE6
  let color_attachment7 = 0x8CE7
  let color_attachment8 = 0x8CE8
  let color_attachment9 = 0x8CE9
  let color_buffer_bit = 0x4000
  let color_clear_value = 0xC22
  let color_logic_op = 0xBF2
  let color_writemask = 0xC23
  let compare_ref_to_texture = 0x884E
  let compile_status = 0x8B81
  let compressed_red = 0x8225
  let compressed_red_rgtc1 = 0x8DBB
  let compressed_rg = 0x8226
  let compressed_rgb = 0x84ED
  let compressed_rgba = 0x84EE
  let compressed_rg_rgtc2 = 0x8DBD
  let compressed_signed_red_rgtc1 = 0x8DBC
  let compressed_signed_rg_rgtc2 = 0x8DBE
  let compressed_srgb = 0x8C48
  let compressed_srgb_alpha = 0x8C49
  let compressed_texture_formats = 0x86A3
  let condition_satisfied = 0x911C
  let constant_alpha = 0x8003
  let constant_color = 0x8001
  let context_compatibility_profile_bit = 0x2
  let context_core_profile_bit = 0x1
  let context_flags = 0x821E
  let context_flag_forward_compatible_bit = 0x1
  let context_profile_mask = 0x9126
  let copy = 0x1503
  let copy_inverted = 0x150C
  let copy_read_buffer = 0x8F36
  let copy_write_buffer = 0x8F37
  let cull_face_enum = 0xB44
  let cull_face_mode = 0xB45
  let current_program = 0x8B8D
  let current_query = 0x8865
  let current_vertex_attrib = 0x8626
  let cw = 0x900
  let decr = 0x1E03
  let decr_wrap = 0x8508
  let delete_status = 0x8B80
  let depth = 0x1801
  let depth24_stencil8 = 0x88F0
  let depth32f_stencil8 = 0x8CAD
  let depth_attachment = 0x8D00
  let depth_buffer_bit = 0x100
  let depth_clamp = 0x864F
  let depth_clear_value = 0xB73
  let depth_component = 0x1902
  let depth_component16 = 0x81A5
  let depth_component24 = 0x81A6
  let depth_component32 = 0x81A7
  let depth_component32f = 0x8CAC
  let depth_func_enum = 0xB74
  let depth_range_enum = 0xB70
  let depth_stencil = 0x84F9
  let depth_stencil_attachment = 0x821A
  let depth_test = 0xB71
  let depth_writemask = 0xB72
  let dither = 0xBD0
  let dont_care = 0x1100
  let double = 0x140A
  let doublebuffer = 0xC32
  let draw_buffer_enum = 0xC01
  let draw_buffer0 = 0x8825
  let draw_buffer1 = 0x8826
  let draw_buffer10 = 0x882F
  let draw_buffer11 = 0x8830
  let draw_buffer12 = 0x8831
  let draw_buffer13 = 0x8832
  let draw_buffer14 = 0x8833
  let draw_buffer15 = 0x8834
  let draw_buffer2 = 0x8827
  let draw_buffer3 = 0x8828
  let draw_buffer4 = 0x8829
  let draw_buffer5 = 0x882A
  let draw_buffer6 = 0x882B
  let draw_buffer7 = 0x882C
  let draw_buffer8 = 0x882D
  let draw_buffer9 = 0x882E
  let draw_framebuffer = 0x8CA9
  let draw_framebuffer_binding = 0x8CA6
  let dst_alpha = 0x304
  let dst_color = 0x306
  let dynamic_copy = 0x88EA
  let dynamic_draw = 0x88E8
  let dynamic_read = 0x88E9
  let element_array_buffer = 0x8893
  let element_array_buffer_binding = 0x8895
  let equal = 0x202
  let equiv = 0x1509
  let extensions = 0x1F03
  let false_ = 0x0
  let fastest = 0x1101
  let fill = 0x1B02
  let first_vertex_convention = 0x8E4D
  let fixed_only = 0x891D
  let float = 0x1406
  let float_32_unsigned_int_24_8_rev = 0x8DAD
  let float_mat2 = 0x8B5A
  let float_mat2x3 = 0x8B65
  let float_mat2x4 = 0x8B66
  let float_mat3 = 0x8B5B
  let float_mat3x2 = 0x8B67
  let float_mat3x4 = 0x8B68
  let float_mat4 = 0x8B5C
  let float_mat4x2 = 0x8B69
  let float_mat4x3 = 0x8B6A
  let float_vec2 = 0x8B50
  let float_vec3 = 0x8B51
  let float_vec4 = 0x8B52
  let fragment_shader = 0x8B30
  let fragment_shader_derivative_hint = 0x8B8B
  let framebuffer = 0x8D40
  let framebuffer_attachment_alpha_size = 0x8215
  let framebuffer_attachment_blue_size = 0x8214
  let framebuffer_attachment_color_encoding = 0x8210
  let framebuffer_attachment_component_type = 0x8211
  let framebuffer_attachment_depth_size = 0x8216
  let framebuffer_attachment_green_size = 0x8213
  let framebuffer_attachment_layered = 0x8DA7
  let framebuffer_attachment_object_name = 0x8CD1
  let framebuffer_attachment_object_type = 0x8CD0
  let framebuffer_attachment_red_size = 0x8212
  let framebuffer_attachment_stencil_size = 0x8217
  let framebuffer_attachment_texture_cube_map_face = 0x8CD3
  let framebuffer_attachment_texture_layer = 0x8CD4
  let framebuffer_attachment_texture_level = 0x8CD2
  let framebuffer_binding = 0x8CA6
  let framebuffer_complete = 0x8CD5
  let framebuffer_default = 0x8218
  let framebuffer_incomplete_attachment = 0x8CD6
  let framebuffer_incomplete_draw_buffer = 0x8CDB
  let framebuffer_incomplete_layer_targets = 0x8DA8
  let framebuffer_incomplete_missing_attachment = 0x8CD7
  let framebuffer_incomplete_multisample = 0x8D56
  let framebuffer_incomplete_read_buffer = 0x8CDC
  let framebuffer_srgb = 0x8DB9
  let framebuffer_undefined = 0x8219
  let framebuffer_unsupported = 0x8CDD
  let front = 0x404
  let front_and_back = 0x408
  let front_face_enum = 0xB46
  let front_left = 0x400
  let front_right = 0x401
  let func_add = 0x8006
  let func_reverse_subtract = 0x800B
  let func_subtract = 0x800A
  let geometry_input_type = 0x8917
  let geometry_output_type = 0x8918
  let geometry_shader = 0x8DD9
  let geometry_vertices_out = 0x8916
  let gequal = 0x206
  let greater = 0x204
  let green = 0x1904
  let green_integer = 0x8D95
  let half_float = 0x140B
  let incr = 0x1E02
  let incr_wrap = 0x8507
  let info_log_length = 0x8B84
  let int = 0x1404
  let interleaved_attribs = 0x8C8C
  let int_2_10_10_10_rev = 0x8D9F
  let int_sampler_1d = 0x8DC9
  let int_sampler_1d_array = 0x8DCE
  let int_sampler_2d = 0x8DCA
  let int_sampler_2d_array = 0x8DCF
  let int_sampler_2d_multisample = 0x9109
  let int_sampler_2d_multisample_array = 0x910C
  let int_sampler_2d_rect = 0x8DCD
  let int_sampler_3d = 0x8DCB
  let int_sampler_buffer = 0x8DD0
  let int_sampler_cube = 0x8DCC
  let int_vec2 = 0x8B53
  let int_vec3 = 0x8B54
  let int_vec4 = 0x8B55
  let invalid_enum = 0x500
  let invalid_framebuffer_operation = 0x506
  let invalid_index = 0xFFFFFFFFl
  let invalid_operation = 0x502
  let invalid_value = 0x501
  let invert = 0x150A
  let keep = 0x1E00
  let last_vertex_convention = 0x8E4E
  let left = 0x406
  let lequal = 0x203
  let less = 0x201
  let line = 0x1B01
  let linear = 0x2601
  let linear_mipmap_linear = 0x2703
  let linear_mipmap_nearest = 0x2701
  let lines = 0x1
  let lines_adjacency = 0xA
  let line_loop = 0x2
  let line_smooth = 0xB20
  let line_smooth_hint = 0xC52
  let line_strip = 0x3
  let line_strip_adjacency = 0xB
  let line_width_enum = 0xB21
  let line_width_granularity = 0xB23
  let line_width_range = 0xB22
  let link_status = 0x8B82
  let logic_op_mode = 0xBF0
  let lower_left = 0x8CA1
  let major_version = 0x821B
  let map_flush_explicit_bit = 0x10
  let map_invalidate_buffer_bit = 0x8
  let map_invalidate_range_bit = 0x4
  let map_read_bit = 0x1
  let map_unsynchronized_bit = 0x20
  let map_write_bit = 0x2
  let max = 0x8008
  let max_3d_texture_size = 0x8073
  let max_array_texture_layers = 0x88FF
  let max_clip_distances = 0xD32
  let max_color_attachments = 0x8CDF
  let max_color_texture_samples = 0x910E
  let max_combined_fragment_uniform_components = 0x8A33
  let max_combined_geometry_uniform_components = 0x8A32
  let max_combined_texture_image_units = 0x8B4D
  let max_combined_uniform_blocks = 0x8A2E
  let max_combined_vertex_uniform_components = 0x8A31
  let max_cube_map_texture_size = 0x851C
  let max_depth_texture_samples = 0x910F
  let max_draw_buffers = 0x8824
  let max_dual_source_draw_buffers = 0x88FC
  let max_elements_indices = 0x80E9
  let max_elements_vertices = 0x80E8
  let max_fragment_input_components = 0x9125
  let max_fragment_uniform_blocks = 0x8A2D
  let max_fragment_uniform_components = 0x8B49
  let max_geometry_input_components = 0x9123
  let max_geometry_output_components = 0x9124
  let max_geometry_output_vertices = 0x8DE0
  let max_geometry_texture_image_units = 0x8C29
  let max_geometry_total_output_components = 0x8DE1
  let max_geometry_uniform_blocks = 0x8A2C
  let max_geometry_uniform_components = 0x8DDF
  let max_integer_samples = 0x9110
  let max_program_texel_offset = 0x8905
  let max_rectangle_texture_size = 0x84F8
  let max_renderbuffer_size = 0x84E8
  let max_samples = 0x8D57
  let max_sample_mask_words = 0x8E59
  let max_server_wait_timeout = 0x9111
  let max_texture_buffer_size = 0x8C2B
  let max_texture_image_units = 0x8872
  let max_texture_lod_bias = 0x84FD
  let max_texture_size = 0xD33
  let max_transform_feedback_interleaved_components = 0x8C8A
  let max_transform_feedback_separate_attribs = 0x8C8B
  let max_transform_feedback_separate_components = 0x8C80
  let max_uniform_block_size = 0x8A30
  let max_uniform_buffer_bindings = 0x8A2F
  let max_varying_components = 0x8B4B
  let max_varying_floats = 0x8B4B
  let max_vertex_attribs = 0x8869
  let max_vertex_output_components = 0x9122
  let max_vertex_texture_image_units = 0x8B4C
  let max_vertex_uniform_blocks = 0x8A2B
  let max_vertex_uniform_components = 0x8B4A
  let max_viewport_dims = 0xD3A
  let min = 0x8007
  let minor_version = 0x821C
  let min_program_texel_offset = 0x8904
  let mirrored_repeat = 0x8370
  let multisample = 0x809D
  let nand = 0x150E
  let nearest = 0x2600
  let nearest_mipmap_linear = 0x2702
  let nearest_mipmap_nearest = 0x2700
  let never = 0x200
  let nicest = 0x1102
  let none = 0x0
  let noop = 0x1505
  let nor = 0x1508
  let notequal = 0x205
  let no_error = 0x0
  let num_compressed_texture_formats = 0x86A2
  let num_extensions = 0x821D
  let object_type = 0x9112
  let one = 0x1
  let one_minus_constant_alpha = 0x8004
  let one_minus_constant_color = 0x8002
  let one_minus_dst_alpha = 0x305
  let one_minus_dst_color = 0x307
  let one_minus_src1_alpha = 0x88FB
  let one_minus_src1_color = 0x88FA
  let one_minus_src_alpha = 0x303
  let one_minus_src_color = 0x301
  let or_ = 0x1507
  let or_inverted = 0x150D
  let or_reverse = 0x150B
  let out_of_memory = 0x505
  let pack_alignment = 0xD05
  let pack_image_height = 0x806C
  let pack_lsb_first = 0xD01
  let pack_row_length = 0xD02
  let pack_skip_images = 0x806B
  let pack_skip_pixels = 0xD04
  let pack_skip_rows = 0xD03
  let pack_swap_bytes = 0xD00
  let pixel_pack_buffer = 0x88EB
  let pixel_pack_buffer_binding = 0x88ED
  let pixel_unpack_buffer = 0x88EC
  let pixel_unpack_buffer_binding = 0x88EF
  let point = 0x1B00
  let points = 0x0
  let point_fade_threshold_size = 0x8128
  let point_size_enum = 0xB11
  let point_size_granularity = 0xB13
  let point_size_range = 0xB12
  let point_sprite_coord_origin = 0x8CA0
  let polygon_mode_enum = 0xB40
  let polygon_offset_factor = 0x8038
  let polygon_offset_fill = 0x8037
  let polygon_offset_line = 0x2A02
  let polygon_offset_point = 0x2A01
  let polygon_offset_units = 0x2A00
  let polygon_smooth = 0xB41
  let polygon_smooth_hint = 0xC53
  let primitives_generated = 0x8C87
  let primitive_restart = 0x8F9D
  let primitive_restart_index_enum = 0x8F9E
  let program_point_size = 0x8642
  let provoking_vertex_enum = 0x8E4F
  let proxy_texture_1d = 0x8063
  let proxy_texture_1d_array = 0x8C19
  let proxy_texture_2d = 0x8064
  let proxy_texture_2d_array = 0x8C1B
  let proxy_texture_2d_multisample = 0x9101
  let proxy_texture_2d_multisample_array = 0x9103
  let proxy_texture_3d = 0x8070
  let proxy_texture_cube_map = 0x851B
  let proxy_texture_rectangle = 0x84F7
  let quads_follow_provoking_vertex_convention = 0x8E4C
  let query_by_region_no_wait = 0x8E16
  let query_by_region_wait = 0x8E15
  let query_counter_bits = 0x8864
  let query_no_wait = 0x8E14
  let query_result = 0x8866
  let query_result_available = 0x8867
  let query_wait = 0x8E13
  let r11f_g11f_b10f = 0x8C3A
  let r16 = 0x822A
  let r16f = 0x822D
  let r16i = 0x8233
  let r16ui = 0x8234
  let r16_snorm = 0x8F98
  let r32f = 0x822E
  let r32i = 0x8235
  let r32ui = 0x8236
  let r3_g3_b2 = 0x2A10
  let r8 = 0x8229
  let r8i = 0x8231
  let r8ui = 0x8232
  let r8_snorm = 0x8F94
  let rasterizer_discard = 0x8C89
  let read_buffer_enum = 0xC02
  let read_framebuffer = 0x8CA8
  let read_framebuffer_binding = 0x8CAA
  let read_only = 0x88B8
  let read_write = 0x88BA
  let red = 0x1903
  let red_integer = 0x8D94
  let renderbuffer = 0x8D41
  let renderbuffer_alpha_size = 0x8D53
  let renderbuffer_binding = 0x8CA7
  let renderbuffer_blue_size = 0x8D52
  let renderbuffer_depth_size = 0x8D54
  let renderbuffer_green_size = 0x8D51
  let renderbuffer_height = 0x8D43
  let renderbuffer_internal_format = 0x8D44
  let renderbuffer_red_size = 0x8D50
  let renderbuffer_samples = 0x8CAB
  let renderbuffer_stencil_size = 0x8D55
  let renderbuffer_width = 0x8D42
  let renderer = 0x1F01
  let repeat = 0x2901
  let replace = 0x1E01
  let rg = 0x8227
  let rg16 = 0x822C
  let rg16f = 0x822F
  let rg16i = 0x8239
  let rg16ui = 0x823A
  let rg16_snorm = 0x8F99
  let rg32f = 0x8230
  let rg32i = 0x823B
  let rg32ui = 0x823C
  let rg8 = 0x822B
  let rg8i = 0x8237
  let rg8ui = 0x8238
  let rg8_snorm = 0x8F95
  let rgb = 0x1907
  let rgb10 = 0x8052
  let rgb10_a2 = 0x8059
  let rgb10_a2ui = 0x906F
  let rgb12 = 0x8053
  let rgb16 = 0x8054
  let rgb16f = 0x881B
  let rgb16i = 0x8D89
  let rgb16ui = 0x8D77
  let rgb16_snorm = 0x8F9A
  let rgb32f = 0x8815
  let rgb32i = 0x8D83
  let rgb32ui = 0x8D71
  let rgb4 = 0x804F
  let rgb5 = 0x8050
  let rgb5_a1 = 0x8057
  let rgb8 = 0x8051
  let rgb8i = 0x8D8F
  let rgb8ui = 0x8D7D
  let rgb8_snorm = 0x8F96
  let rgb9_e5 = 0x8C3D
  let rgba = 0x1908
  let rgba12 = 0x805A
  let rgba16 = 0x805B
  let rgba16f = 0x881A
  let rgba16i = 0x8D88
  let rgba16ui = 0x8D76
  let rgba16_snorm = 0x8F9B
  let rgba2 = 0x8055
  let rgba32f = 0x8814
  let rgba32i = 0x8D82
  let rgba32ui = 0x8D70
  let rgba4 = 0x8056
  let rgba8 = 0x8058
  let rgba8i = 0x8D8E
  let rgba8ui = 0x8D7C
  let rgba8_snorm = 0x8F97
  let rgba_integer = 0x8D99
  let rgb_integer = 0x8D98
  let rg_integer = 0x8228
  let right = 0x407
  let sampler_1d = 0x8B5D
  let sampler_1d_array = 0x8DC0
  let sampler_1d_array_shadow = 0x8DC3
  let sampler_1d_shadow = 0x8B61
  let sampler_2d = 0x8B5E
  let sampler_2d_array = 0x8DC1
  let sampler_2d_array_shadow = 0x8DC4
  let sampler_2d_multisample = 0x9108
  let sampler_2d_multisample_array = 0x910B
  let sampler_2d_rect = 0x8B63
  let sampler_2d_rect_shadow = 0x8B64
  let sampler_2d_shadow = 0x8B62
  let sampler_3d = 0x8B5F
  let sampler_binding = 0x8919
  let sampler_buffer = 0x8DC2
  let sampler_cube = 0x8B60
  let sampler_cube_shadow = 0x8DC5
  let samples = 0x80A9
  let samples_passed = 0x8914
  let sample_alpha_to_coverage = 0x809E
  let sample_alpha_to_one = 0x809F
  let sample_buffers = 0x80A8
  let sample_coverage_enum = 0x80A0
  let sample_coverage_invert = 0x80AB
  let sample_coverage_value = 0x80AA
  let sample_mask = 0x8E51
  let sample_mask_value = 0x8E52
  let sample_position = 0x8E50
  let scissor_box = 0xC10
  let scissor_test = 0xC11
  let separate_attribs = 0x8C8D
  let set = 0x150F
  let shader_source_length = 0x8B88
  let shader_type = 0x8B4F
  let shading_language_version = 0x8B8C
  let short = 0x1402
  let signaled = 0x9119
  let signed_normalized = 0x8F9C
  let smooth_line_width_granularity = 0xB23
  let smooth_line_width_range = 0xB22
  let smooth_point_size_granularity = 0xB13
  let smooth_point_size_range = 0xB12
  let src1_alpha = 0x8589
  let src1_color = 0x88F9
  let src_alpha = 0x302
  let src_alpha_saturate = 0x308
  let src_color = 0x300
  let srgb = 0x8C40
  let srgb8 = 0x8C41
  let srgb8_alpha8 = 0x8C43
  let srgb_alpha = 0x8C42
  let static_copy = 0x88E6
  let static_draw = 0x88E4
  let static_read = 0x88E5
  let stencil = 0x1802
  let stencil_attachment = 0x8D20
  let stencil_back_fail = 0x8801
  let stencil_back_func = 0x8800
  let stencil_back_pass_depth_fail = 0x8802
  let stencil_back_pass_depth_pass = 0x8803
  let stencil_back_ref = 0x8CA3
  let stencil_back_value_mask = 0x8CA4
  let stencil_back_writemask = 0x8CA5
  let stencil_buffer_bit = 0x400
  let stencil_clear_value = 0xB91
  let stencil_fail = 0xB94
  let stencil_func_enum = 0xB92
  let stencil_index = 0x1901
  let stencil_index1 = 0x8D46
  let stencil_index16 = 0x8D49
  let stencil_index4 = 0x8D47
  let stencil_index8 = 0x8D48
  let stencil_pass_depth_fail = 0xB95
  let stencil_pass_depth_pass = 0xB96
  let stencil_ref = 0xB97
  let stencil_test = 0xB90
  let stencil_value_mask = 0xB93
  let stencil_writemask = 0xB98
  let stereo = 0xC33
  let stream_copy = 0x88E2
  let stream_draw = 0x88E0
  let stream_read = 0x88E1
  let subpixel_bits = 0xD50
  let sync_condition = 0x9113
  let sync_fence = 0x9116
  let sync_flags = 0x9115
  let sync_flush_commands_bit = 0x1
  let sync_gpu_commands_complete = 0x9117
  let sync_status = 0x9114
  let texture = 0x1702
  let texture0 = 0x84C0
  let texture1 = 0x84C1
  let texture10 = 0x84CA
  let texture11 = 0x84CB
  let texture12 = 0x84CC
  let texture13 = 0x84CD
  let texture14 = 0x84CE
  let texture15 = 0x84CF
  let texture16 = 0x84D0
  let texture17 = 0x84D1
  let texture18 = 0x84D2
  let texture19 = 0x84D3
  let texture2 = 0x84C2
  let texture20 = 0x84D4
  let texture21 = 0x84D5
  let texture22 = 0x84D6
  let texture23 = 0x84D7
  let texture24 = 0x84D8
  let texture25 = 0x84D9
  let texture26 = 0x84DA
  let texture27 = 0x84DB
  let texture28 = 0x84DC
  let texture29 = 0x84DD
  let texture3 = 0x84C3
  let texture30 = 0x84DE
  let texture31 = 0x84DF
  let texture4 = 0x84C4
  let texture5 = 0x84C5
  let texture6 = 0x84C6
  let texture7 = 0x84C7
  let texture8 = 0x84C8
  let texture9 = 0x84C9
  let texture_1d = 0xDE0
  let texture_1d_array = 0x8C18
  let texture_2d = 0xDE1
  let texture_2d_array = 0x8C1A
  let texture_2d_multisample = 0x9100
  let texture_2d_multisample_array = 0x9102
  let texture_3d = 0x806F
  let texture_alpha_size = 0x805F
  let texture_alpha_type = 0x8C13
  let texture_base_level = 0x813C
  let texture_binding_1d = 0x8068
  let texture_binding_1d_array = 0x8C1C
  let texture_binding_2d = 0x8069
  let texture_binding_2d_array = 0x8C1D
  let texture_binding_2d_multisample = 0x9104
  let texture_binding_2d_multisample_array = 0x9105
  let texture_binding_3d = 0x806A
  let texture_binding_buffer = 0x8C2C
  let texture_binding_cube_map = 0x8514
  let texture_binding_rectangle = 0x84F6
  let texture_blue_size = 0x805E
  let texture_blue_type = 0x8C12
  let texture_border_color = 0x1004
  let texture_buffer = 0x8C2A
  let texture_buffer_data_store_binding = 0x8C2D
  let texture_compare_func = 0x884D
  let texture_compare_mode = 0x884C
  let texture_compressed = 0x86A1
  let texture_compressed_image_size = 0x86A0
  let texture_compression_hint = 0x84EF
  let texture_cube_map = 0x8513
  let texture_cube_map_negative_x = 0x8516
  let texture_cube_map_negative_y = 0x8518
  let texture_cube_map_negative_z = 0x851A
  let texture_cube_map_positive_x = 0x8515
  let texture_cube_map_positive_y = 0x8517
  let texture_cube_map_positive_z = 0x8519
  let texture_cube_map_seamless = 0x884F
  let texture_depth = 0x8071
  let texture_depth_size = 0x884A
  let texture_depth_type = 0x8C16
  let texture_fixed_sample_locations = 0x9107
  let texture_green_size = 0x805D
  let texture_green_type = 0x8C11
  let texture_height = 0x1001
  let texture_internal_format = 0x1003
  let texture_lod_bias = 0x8501
  let texture_mag_filter = 0x2800
  let texture_max_level = 0x813D
  let texture_max_lod = 0x813B
  let texture_min_filter = 0x2801
  let texture_min_lod = 0x813A
  let texture_rectangle = 0x84F5
  let texture_red_size = 0x805C
  let texture_red_type = 0x8C10
  let texture_samples = 0x9106
  let texture_shared_size = 0x8C3F
  let texture_stencil_size = 0x88F1
  let texture_swizzle_a = 0x8E45
  let texture_swizzle_b = 0x8E44
  let texture_swizzle_g = 0x8E43
  let texture_swizzle_r = 0x8E42
  let texture_swizzle_rgba = 0x8E46
  let texture_width = 0x1000
  let texture_wrap_r = 0x8072
  let texture_wrap_s = 0x2802
  let texture_wrap_t = 0x2803
  let timeout_expired = 0x911B
  let timeout_ignored = 0xFFFFFFFFFFFFFFFFL
  let timestamp = 0x8E28
  let time_elapsed = 0x88BF
  let transform_feedback_buffer = 0x8C8E
  let transform_feedback_buffer_binding = 0x8C8F
  let transform_feedback_buffer_mode = 0x8C7F
  let transform_feedback_buffer_size = 0x8C85
  let transform_feedback_buffer_start = 0x8C84
  let transform_feedback_primitives_written = 0x8C88
  let transform_feedback_varyings_enum = 0x8C83
  let transform_feedback_varying_max_length = 0x8C76
  let triangles = 0x4
  let triangles_adjacency = 0xC
  let triangle_fan = 0x6
  let triangle_strip = 0x5
  let triangle_strip_adjacency = 0xD
  let true_ = 0x1
  let uniform_array_stride = 0x8A3C
  let uniform_block_active_uniforms = 0x8A42
  let uniform_block_active_uniform_indices = 0x8A43
  let uniform_block_binding_enum = 0x8A3F
  let uniform_block_data_size = 0x8A40
  let uniform_block_index = 0x8A3A
  let uniform_block_name_length = 0x8A41
  let uniform_block_referenced_by_fragment_shader = 0x8A46
  let uniform_block_referenced_by_geometry_shader = 0x8A45
  let uniform_block_referenced_by_vertex_shader = 0x8A44
  let uniform_buffer = 0x8A11
  let uniform_buffer_binding = 0x8A28
  let uniform_buffer_offset_alignment = 0x8A34
  let uniform_buffer_size = 0x8A2A
  let uniform_buffer_start = 0x8A29
  let uniform_is_row_major = 0x8A3E
  let uniform_matrix_stride = 0x8A3D
  let uniform_name_length = 0x8A39
  let uniform_offset = 0x8A3B
  let uniform_size = 0x8A38
  let uniform_type = 0x8A37
  let unpack_alignment = 0xCF5
  let unpack_image_height = 0x806E
  let unpack_lsb_first = 0xCF1
  let unpack_row_length = 0xCF2
  let unpack_skip_images = 0x806D
  let unpack_skip_pixels = 0xCF4
  let unpack_skip_rows = 0xCF3
  let unpack_swap_bytes = 0xCF0
  let unsignaled = 0x9118
  let unsigned_byte = 0x1401
  let unsigned_byte_2_3_3_rev = 0x8362
  let unsigned_byte_3_3_2 = 0x8032
  let unsigned_int = 0x1405
  let unsigned_int_10f_11f_11f_rev = 0x8C3B
  let unsigned_int_10_10_10_2 = 0x8036
  let unsigned_int_24_8 = 0x84FA
  let unsigned_int_2_10_10_10_rev = 0x8368
  let unsigned_int_5_9_9_9_rev = 0x8C3E
  let unsigned_int_8_8_8_8 = 0x8035
  let unsigned_int_8_8_8_8_rev = 0x8367
  let unsigned_int_sampler_1d = 0x8DD1
  let unsigned_int_sampler_1d_array = 0x8DD6
  let unsigned_int_sampler_2d = 0x8DD2
  let unsigned_int_sampler_2d_array = 0x8DD7
  let unsigned_int_sampler_2d_multisample = 0x910A
  let unsigned_int_sampler_2d_multisample_array = 0x910D
  let unsigned_int_sampler_2d_rect = 0x8DD5
  let unsigned_int_sampler_3d = 0x8DD3
  let unsigned_int_sampler_buffer = 0x8DD8
  let unsigned_int_sampler_cube = 0x8DD4
  let unsigned_int_vec2 = 0x8DC6
  let unsigned_int_vec3 = 0x8DC7
  let unsigned_int_vec4 = 0x8DC8
  let unsigned_normalized = 0x8C17
  let unsigned_short = 0x1403
  let unsigned_short_1_5_5_5_rev = 0x8366
  let unsigned_short_4_4_4_4 = 0x8033
  let unsigned_short_4_4_4_4_rev = 0x8365
  let unsigned_short_5_5_5_1 = 0x8034
  let unsigned_short_5_6_5 = 0x8363
  let unsigned_short_5_6_5_rev = 0x8364
  let upper_left = 0x8CA2
  let validate_status = 0x8B83
  let vendor = 0x1F00
  let version = 0x1F02
  let vertex_array_binding = 0x85B5
  let vertex_attrib_array_buffer_binding = 0x889F
  let vertex_attrib_array_divisor = 0x88FE
  let vertex_attrib_array_enabled = 0x8622
  let vertex_attrib_array_integer = 0x88FD
  let vertex_attrib_array_normalized = 0x886A
  let vertex_attrib_array_pointer = 0x8645
  let vertex_attrib_array_size = 0x8623
  let vertex_attrib_array_stride = 0x8624
  let vertex_attrib_array_type = 0x8625
  let vertex_program_point_size = 0x8642
  let vertex_shader = 0x8B31
  let viewport_enum = 0xBA2
  let wait_failed = 0x911D
  let write_only = 0x88B9
  let xor = 0x1506
  let zero = 0x0
end

(*---------------------------------------------------------------------------
   Copyright (c) 2013 Daniel C. Bünzli

   Permission to use, copy, modify, and/or distribute this software for any
   purpose with or without fee is hereby granted, provided that the above
   copyright notice and this permission notice appear in all copies.

   THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
   WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
   MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
   ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
   WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
   ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
   OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
  ---------------------------------------------------------------------------*)

end
