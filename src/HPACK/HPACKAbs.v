From HTTP2.src Require Import HPACK.HPACKTypes Util.OptionE.
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
  Context {H1:Monad Err}.
  Context {H2:MonadExc HPACKError Err}.
  Parameter encodeHeader : EncodeStrategy -> DTable -> HeaderList -> Err (string * DTable).

  Parameter decodeHeader : DTable -> string -> Err (HeaderList * DTable).

  Parameter newDTable : N -> N -> Err DTable.
End HPACK.