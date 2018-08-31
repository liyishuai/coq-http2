From HTTP2.HPACK Require Import HPACKTypes.
From HTTP2.Util Require Import OptionE.
Require Import String BinNat List.
From ExtLib Require Import Monad MonadExc.
Import ListNotations.
Open Scope N_scope.

Inductive CompressionAlgo :=
| Naive : CompressionAlgo (* No compression *)
| Static : CompressionAlgo (* Using indices in the static table only *)
| Linear : CompressionAlgo (* Using indices *).

Inductive EncodeStrategy :=
| encodeStrategy : CompressionAlgo (* Which compression algorithm is used. *)
                   -> bool (* Whether or not to use Huffman encoding for strings. *)
                   -> EncodeStrategy.

Definition defaultEncodeStrategy : EncodeStrategy := encodeStrategy Linear false.

(* The initial value for SETTINGS_HEADER_TABLE_SIZE is 4096:
   https://http2.github.io/http2-spec/#SettingValues *)
Definition defaultDTable : DTable := (4096, 4096, []).

Module Type HPACK.
  (* Encodes the header list using the given encoding strategy and encoding 
     dynamic table. Returns the encoded header list and a potentially modified
     encoding dynamic table. *)
  Parameter encodeHeader : EncodeStrategy -> DTable -> HeaderList 
                           -> Err (string * DTable).

  (* Decodes the string using the given decoding dynamic table. Returns the
     decoded header list and a potentially modified decoding dynamic table. *)
  Parameter decodeHeader : DTable -> string -> Err (HeaderList * DTable).

  (* Return a new dtable, with size and maximum size respectively taken in as 
     arguments. 
     Fails with TooLargeTableSize if the size is greater than the maximum size.
     Fails with TooSmallTableSize if the size is less than 32. *)
  Parameter newDTable : N -> N -> Err DTable.
End HPACK.
