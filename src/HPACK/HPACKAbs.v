From HTTP2.src Require Import HPACK.HPACKTypes Util.OptionE.
Require Import String BinNat.
From ExtLib Require Import Monad MonadExc.

Inductive CompressionAlgo :=
| Naive : CompressionAlgo (* No compression *)
| Static : CompressionAlgo (* Using indices in the static table only *)
| Linear : CompressionAlgo (* Using indices *).

Inductive EncodeStrategy :=
| encodeStrategy : CompressionAlgo (* Which compression algorithm is used. *)
                   -> bool (* Whether or not to use Huffman encoding for strings. *)
                   -> EncodeStrategy.

Definition defaultEncodeStrategy : EncodeStrategy := encodeStrategy Linear false.

Definition defaultDTableSize : N := 4096.  

Module Type HPACK.
  Parameter encodeHeader : Monad Err -> MonadExc HPACKError Err -> EncodeStrategy ->
                           DTable -> HeaderList -> Err (string * DTable).

  Parameter decodeHeader : Monad Err -> MonadExc HPACKError Err -> DTable -> string ->
                           Err (HeaderList * DTable).

  Parameter newDTable : Monad Err -> MonadExc HPACKError Err -> N -> N -> Err DTable.
End HPACK.