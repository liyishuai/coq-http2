From Coq Require Import Strings.String BinNat List.
From ExtLib Require Import Monad.

(* https://tools.ietf.org/html/rfc7541#section-1.3 *)
(* Header Field:  A name-value pair.  Both the name and value are
      treated as opaque sequences of octets. *)
Definition HeaderField := (string * string)%type.

(* Dynamic Table:  The dynamic table is a table that
      associates stored header fields with index values.  This table is
      dynamic and specific to an encoding or decoding context.

   Static Table:  The static table is a table that
      statically associates header fields that occur frequently with
      index values.  This table is ordered, read-only, always
      accessible, and it may be shared amongst all encoding or decoding
      contexts. *)
Definition Table := list HeaderField.

(* Dynamic Tables are a triple of a size, a maximum size and a table. 
   The maximum size is provided by the SETTINGS_HEADER_TABLE_SIZE, 
   https://tools.ietf.org/html/rfc7540#section-6.5.2
   The default value for the maximum size is 4096.
   The convention is that the table has size (as defined in 
   https://tools.ietf.org/html/rfc7541#section-4.1) less than or equal to the
   maximum size, which is enforced by the functions that add entries.  *)
Definition DTable := (N * N * Table)%type.

(* Header List:  A header list is an ordered collection of header fields
      that are encoded jointly and can contain duplicate header fields.
      A complete list of header fields contained in an HTTP/2 header
      block is a header list. *)
Definition HeaderList := list HeaderField.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
(* Header Field Representation:  A header field can be represented in
      encoded form either as a literal or as an index *)
Inductive HeaderFieldRepresentation :=
(* https://tools.ietf.org/html/rfc7541#section-6.1 *)
| IndexedHF : N -> HeaderFieldRepresentation
(* https://tools.ietf.org/html/rfc7541#section-6.2 *)
| LHFIncrementIndexedName : N -> string -> HeaderFieldRepresentation
| LHFIncrementNewName : string -> string -> HeaderFieldRepresentation
| LHFWithoutIndexIndexedName : N -> string -> HeaderFieldRepresentation
| LHFWithoutIndexNewName : string -> string -> HeaderFieldRepresentation
| LHFNeverIndexIndexedName : N -> string -> HeaderFieldRepresentation
| LHFNeverIndexNewName : string -> string -> HeaderFieldRepresentation
(* https://tools.ietf.org/html/rfc7541#section-6.3 *)
| DTableSizeUpdate : N -> HeaderFieldRepresentation.

(* Header Block:  An ordered list of header field representations,
      which, when decoded, yields a complete header list. *)
Definition HeaderBlock := list HeaderFieldRepresentation.

(* Error type for HPACK *)
Inductive HPACKError :=
| IndexOverrun : N -> HPACKError (* Index is out of range *)
| EosInTheMiddle : HPACKError (* Eos appears in the middle of huffman string *)
| IllegalEos : HPACKError (* Non-eos appears in the end of huffman string *)
| TooLongEos : HPACKError	(* Eos of huffman string is more than 7 bits *)
| EmptyEncodedString : HPACKError (* Encoded string has no length *)
| TooSmallTableSize : HPACKError (* A peer set the dynamic table size less than 32 *)
| TooLargeTableSize : HPACKError (* A peer tried to change the dynamic table size over the limit *)
| IllegalTableSizeUpdate : HPACKError (* Table size update at the non-beginning *)
| HeaderBlockTruncated : HPACKError	 
| IllegalHeaderName : HPACKError
| IntegerOverflow : HPACKError (* Integer is too large to encode *)
| HeaderBlockOverflow : HPACKError (* Too many headers in header block *).

Definition Err := sum HPACKError.

Instance monadErr : Monad Err :=
  {|
    ret := @inr HPACKError;
    bind _ _ x f := match x with
                | inl e => inl e
                | inr v => f v
                end |}.
                    
                      