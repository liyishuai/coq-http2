From HTTP2 Require Import Types Util.BitField Util.ByteVector Util.BitVector.
From Coq Require Import Bvector String BinNat List.
Open Scope N_scope.
Open Scope string_scope.

(* Converts binary nat i to an n bit vector. *)
Fixpoint binnat_to_bvector (i:N) (n:nat) : Bvector n :=
  let val := N.testbit_nat i n in
  match n with
  | O => Bnil
  | S n' => Bcons val n' (binnat_to_bvector i n')
  end.

Definition pad_len (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    (* Pad Length? (8) *)
    pack (binnat_to_bvector n 8)
  end.

Definition padding (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    N.peano_rect (fun _ => string) "" (fun n' s => String Ascii.zero s) n
  end.

Definition streamid_to_string (E:bool) (sid:StreamId) : string :=
  pack (Bcons E 31 (binnat_to_bvector sid 31)).

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
(* NOTE: header is the string between length and payload. *)
Definition encodeFrameHeader (f:Frame) : string :=
  let fh := frameHeader f in
  (* Length (24) *)
  let s_len := pack (binnat_to_bvector (payloadLength fh) 24) in
  (* Type (8) *)
  let s_ft := pack (binnat_to_bvector (toFrameTypeId (frameType f)) 8) in
  (* Flags (8) *)
  let s_flgs := pack (flags fh) in
  (* R is a reserved 1-bit field, MUST remain unset when sending and MUST be
     ignored when receiving. *)
  (* Stream Identifier (31) *)
  let s_si := streamid_to_string false (streamId fh) in
  s_ft ++ s_flgs ++ s_si.

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
    pack (binnat_to_bvector (weight p) 8)
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
  pack (binnat_to_bvector (weight p) 8).

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.4 *)
Definition buildRSTStream (e:ErrorCode) :=
  (* Error Code (32) *)
  pack (binnat_to_bvector (toErrorCodeId e) 32).

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.5 *)
Fixpoint buildSettings (sets:list Setting) :=
  match sets with
  | nil => ""
  | (sk, sv) :: tl =>
    (* Identifier (16) *)
    pack (binnat_to_bvector (toSettingKeyId sk) 16)
    (* Value (32) *)
    ++ pack (binnat_to_bvector sv 32) ++ buildSettings tl
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
  pack (binnat_to_bvector (toErrorCodeId e) 32) ++
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
