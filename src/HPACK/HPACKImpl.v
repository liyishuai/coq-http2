Require Import String List BinNat.
From HTTP2.src.HPACK Require Import HPACKAbs HPACKDecode HPACKEncode
     HPACKTables HPACKTypes HPACKProcessor.
From HTTP2.src.Util Require Import Parser ParserInstances.
From ExtLib Require Import Monads StateMonad.
Import MonadNotation.
Import ListNotations.

Module HPACKImpl : HPACK.
  Definition encodeHeader (es:EncodeStrategy)
             (dtable:DTable) (hl:HeaderList) : Err (string * DTable) :=
    let f hf :=
        match es with
        | encodeStrategy ca H =>
          (match ca with
           | Naive => LHFWithoutIndexNewName (fst hf) (snd hf)
           | Static =>
             match find_table hf static_table with
             | None => LHFWithoutIndexNewName (fst hf) (snd hf)
             | Some i => IndexedHF i
             end
           | Linear =>
             match find_table hf static_table with
             | None =>
               match find_table hf (snd dtable) with
               | None => LHFIncrementNewName (fst hf) (snd hf)
               | Some i => IndexedHF (i + (N.of_nat (length static_table)))
               end
             | Some i => IndexedHF i
             end
           end, H)
        end in
    fold_left (fun acc hf =>
                 let (hfr, H) := f hf in
                 v <- acc;;
                 d <- process_HFR hfr (snd v);;
                 ret (fst v ++ encode_HFR H hfr, snd d)) hl (ret ("", dtable)).

  Definition decodeHeader (dtable:DTable) (s:string)
    : Err (HeaderList * DTable) :=
    match StateMonad.runStateT (run_HPACK_parser decode_HB) s with
    | inl e => inl e
    | inr (hb, _) =>
      fold_left (fun acc hf =>
                   v <- acc;;
                   d <- process_HFR hf (snd v);;
                   ret (match fst d with
                        | None => fst v
                        | Some h => h :: fst v
                        end, snd d)) hb (ret ([], dtable))
    end.

  Definition newDTable (size:N) (max:N) : Err DTable :=
    if negb (size <=? max) then raise TooLargeTableSize
    else if size <? 32 then raise TooSmallTableSize else ret (size, max, []).
End HPACKImpl.