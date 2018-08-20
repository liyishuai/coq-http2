From HTTP2.src Require Import HPACK.HPACKTypes Util.OptionE.
Require Import String BinNat.
From ExtLib Require Import Monad MonadExc.

Module Type HPACK.
  Parameter encodeHeader : DTable -> HeaderList -> string.

  Definition Err := sum HPACKError.

  Parameter decodeHeader : string -> Monad Err -> MonadExc HPACKError Err
                           -> Err HeaderList.

  Definition defaultDTableSize : N := 4096.

  Parameter newDTable : N -> DTable.

  Inductive CompressionAlgo :=
  | Naive : CompressionAlgo (* No compression *)
  | Static : CompressionAlgo (* Using indices in the static table only *)
  | Linear : CompressionAlgo (* Using indices *).

  Inductive EncodeStrategy :=
  | encodeStrategy : CompressionAlgo (* Which compression algorithm is used. *)
                     -> bool (* Whether or not to use Huffman encoding for strings. *)
                     -> EncodeStrategy.

  Definition defaultEncodeStrategy : EncodeStrategy := encodeStrategy Linear false.
End HPACK.