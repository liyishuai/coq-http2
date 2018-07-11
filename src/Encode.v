From HTTP2 Require Import Types.
From HTTP2.Util Require Import BitField ByteVector BitVector VectorUtil.
From Coq Require Import Bvector String BinNat List Ascii.
Open Scope N_scope.
Open Scope string_scope.

Definition pad_len (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    (* Pad Length? (8) *)
    to_string (@ByteVector_of_N 1 n)
  end.

Definition padding (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    N.peano_rect (fun _ => string) "" (fun n' s => String Ascii.zero s) n
  end.

Definition streamid_to_string (E:bool) (sid:StreamId) : string :=
  to_string (
      match Vector_uncons (@ByteVector_of_N 4 sid) with
      | (Ascii b0 b1 b2 b3 b4 b5 b6 _, v) =>
        Vector.cons ascii (Ascii b0 b1 b2 b3 b4 b5 b6 E) 3 v
      end).

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Program Definition encodeFrameHeader (f:Frame) : string :=
  let fh := frameHeader f in
  (* Length (24) *)
  let s_len := to_string (@ByteVector_of_N 3 (payloadLength fh)) in
  (* Type (8) *)
  let s_ft := to_string (@ByteVector_of_N 1 (toFrameTypeId (frameType f))) in
  (* Flags (8) *)
  let s_flgs := pack (flags fh) in
  (* R is a reserved 1-bit field, MUST remain unset when sending and MUST be
     ignored when receiving. *)
  (* Stream Identifier (31) *)
  let s_si := streamid_to_string false (streamId fh) in
  s_len ++ s_ft ++ s_flgs ++ s_si.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.1 *)
Definition buildData (p:option N) (s:string) :=
  (* Pad Length? (8) *)
  pad_len p ++
  (* Data ( * ) *)
  s ++
  (* Padding ( * ) *)
  padding p.


(* https://http2.github.io/http2-spec/index.html#rfc.section.6.2 *)
Definition buildHeaders (p:option N) (op:option Priority) (hbf:HeaderBlockFragment) :=
  (* Pad Length? (8) *)
  pad_len p ++
  match op with
  | None => ""
  | Some p =>
    (* E *)
    (* StreamDependency? (31) *)
    streamid_to_string (exclusive p) (streamDependency p) ++
    (* Weight? (8) *)
    to_string (@ByteVector_of_N 1 (weight p) )
  end
    (* Header Block Fragment ( * ) *)
    ++ hbf ++
    (* Padding ( * ) *)
    padding p.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.3 *)
Definition buildPriority (p:Priority) :=
  (* E *)
  (* StreamDependency? (31) *)
  streamid_to_string (exclusive p) (streamDependency p) ++
  (* Weight? (8) *)
  to_string (@ByteVector_of_N 1 (weight p)).

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.4 *)
Definition buildRSTStream (e:ErrorCode) :=
  (* Error Code (32) *)
  to_string (@ByteVector_of_N 4 (toErrorCodeId e)).

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.5 *)
Fixpoint buildSettings (sets:list Setting) :=
  match sets with
  | nil => ""
  | (sk, sv) :: tl =>
    (* Identifier (16) *)
    to_string (@ByteVector_of_N 2 (toSettingKeyId sk))
    (* Value (32) *)
    ++ to_string (@ByteVector_of_N 4 sv) ++ buildSettings tl
  end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.6 *)
Definition buildPushPromise (p:option N) (sid:StreamId)
           (hbf:HeaderBlockFragment) :=
  (* Pad Length? (8) *)
  pad_len p ++
  (* R: A single reserved bit *)
  (* Promised Stream ID (31) *)
  streamid_to_string false sid ++
  (* Header block Fragment ( * ) *)
  hbf ++
  (* Padding ( * ) *)
  padding p
.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.7 *)
Definition buildPing (v:ByteVector 8) :=
  (* Opaque Datra (64) *)
  to_string v.


(* https://http2.github.io/http2-spec/index.html#rfc.section.6.8 *)
Definition buildGoAway (sid:StreamId) (e:ErrorCode) (s:string) :=
  (* R *)
  (* Last-Stream-ID (31) *)
  streamid_to_string false sid ++
  (* Error Code (32) *)
  to_string (@ByteVector_of_N 4 (toErrorCodeId e)) ++
  (* Additional Debug Data ( * ) *)
  s.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.9 *)
Definition buildWindowUpdate (ws:WindowSize) :=
  (* R *)
  (* Window Size Increment (31) *)
  streamid_to_string false ws.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.10 *)
Definition buildContinuation (hbf:HeaderBlockFragment) :=
  (* Header Block Fragment ( * ) *) hbf.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6 *)
Definition encodePayload (padding:option N) (f:Frame) : string :=
  match framePayload f with
  | DataFrame s => buildData padding s
  | HeadersFrame op hbf => buildHeaders padding op hbf
  | PriorityFrame p => buildPriority p
  | RSTStreamFrame e => buildRSTStream e
  | SettingsFrame sets => buildSettings sets
  | PushPromiseFrame sid hbf => buildPushPromise padding sid hbf
  | PingFrame v => buildPing v
  | GoAwayFrame sid e s => buildGoAway sid e s
  | WindowUpdateFrame ws => buildWindowUpdate ws
  | ContinuationFrame hbf => buildContinuation hbf
  | UnknownFrame _ s => buildData padding s
  end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Definition encodeFrame (padding:option N) (f:Frame) : string :=
  encodeFrameHeader f ++ encodePayload padding f.
