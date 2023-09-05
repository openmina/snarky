type 'v t = private 'v [@@deriving sexp_of]

module Unsafe : sig
  val create : 'v -> 'v t
end
