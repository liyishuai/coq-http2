From HTTP2 Require Import Types.
From HTTP2.Util Require Import
     BitField BitVector VectorUtil StringUtil.
From Coq Require Import
     Basics Bvector String BinNat List Ascii Vector.

Import VectorNotations.
Open Scope N_scope.
Open Scope string_scope.
Open Scope program_scope.

Definition pretty_StreamId (i : StreamId) : string :=
  hex_of_Bvector i.

Definition pretty_PayloadLength (len : PayloadLength) : string :=
  hex_of_Bvector len.

Definition pretty_FrameFlagsField (fff : FrameFlagsField) : string :=
  hex_of_Bvector fff.

Definition pretty_FrameHeader (h : FrameHeader) : string :=
  "payload: " ++ pretty_PayloadLength (payloadLength h) ++ " bytes" ++ nl ++
  "flags: " ++ pretty_FrameFlagsField (flags h) ++ nl ++
  "streamId: " ++ pretty_StreamId (streamId h) ++ nl.

Definition pretty_Frame (f : Frame) : string :=
  pretty_FrameHeader (frameHeader f).

Definition pretty_HTTP2Error (e : HTTP2Error) : string :=
  match e with
  | ConnectionError code msg =>
    "Connection error (" ++
      hex_of_Bvector code ++ "): " ++
      msg ++ nl
  | StreamError code sid =>
    "Stream error (" ++
      hex_of_Bvector code ++ ") on stream " ++
      hex_of_Bvector sid ++ nl
  end.
