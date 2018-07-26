From Coq Require Import String.
From HTTP2.HPACK Require Import HPACKTypes HPACKTables.
From HTTP2.Util Require Import OptionE.
From ExtLib Require Import Monads.
Import MonadNotation.

(* https://http2.github.io/http2-spec/compression.html#string.literal.representation *)
(* Decodes the huffman encoded string s *)
Definition decode_hstring (s:string) : string := "".