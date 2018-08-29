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

Definition defaultDTable : DTable := (4096, 4096, []).

Module Type HPACK.
  Parameter encodeHeader : EncodeStrategy -> DTable -> HeaderList -> Err (string * DTable).

  Parameter decodeHeader : DTable -> string -> Err (HeaderList * DTable).

  Parameter newDTable : N -> N -> Err DTable.
End HPACK.
