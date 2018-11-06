From HTTP2 Require Import Types.
From HTTP2.Util Require Import BitField BitVector VectorUtil.
From Coq Require Import
     Ascii
     Basics
     BinNat
     Bvector
     ByteVector
     Ndigits
     String
     List
     Vector.

Import VectorNotations.
Open Scope N_scope.
Open Scope string_scope.
Open Scope program_scope.

Definition pad_len (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    (* Pad Length? (8) *)
    to_string (N2ByteV_sized 1 n)
  end.

Definition padding (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    N.peano_rect (fun _ => string) "" (fun n' s => String Ascii.zero s) n
  end.

Program Definition streamid_to_vector (E:bool) (sid:StreamId) : ByteVector 4 :=
  of_Bvector (E :: sid).

Definition streamid_to_string (E:bool) : StreamId -> string :=
  to_string ∘ streamid_to_vector E.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Program Definition encodeFrameHeader (ft: FrameType) (fh: FrameHeader) : ByteVector 9 :=
  (* Length (24) *)
  let v_len := N2ByteV_sized 3 (payloadLength fh) in
  (* Type (8) *)
  let v_ft := N2ByteV_sized 1 (toFrameTypeId ft) in
  (* Flags (8) *)
  let v_flgs := @of_Bvector 1 (flags fh) in
  (* R is a reserved 1-bit field, MUST remain unset when sending and MUST be
     ignored when receiving. *)
  (* Stream Identifier (31) *)
  let v_si := streamid_to_vector false (streamId fh) in
  (append v_len (append v_ft (append v_flgs v_si))).

Definition with_padding (payload:string) (padding':option Padding) :=
  match padding' with
  | Some padding =>
    let pad_len_N := N.of_nat (String.length padding) in
    let pad_len := to_string (N2ByteV_sized 1 pad_len_N) in
    pad_len ++ payload ++ padding
  | None => payload
  end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.1 *)
Definition buildData (data:string) (padding':option Padding) :=
  with_padding data padding'.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.2 *)
Definition buildHeaders
           (op:option Priority) (hbf:HeaderBlockFragment)
           (padding':option Padding) :=
  with_padding
    (match op with
     | None => ""
     | Some p =>
       (* E *)
       (* StreamDependency? (31) *)
       streamid_to_string (exclusive p) (streamDependency p) ++
       (* Weight? (8) *)
       to_string (@of_Bvector 1 (weight p) )
     end
     (* Header Block Fragment ( * ) *)
     ++ hbf)
    (* Padding ( * ) *)
    padding'.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.3 *)
Definition buildPriority (p:Priority) :=
  (* E *)
  (* StreamDependency? (31) *)
  streamid_to_string (exclusive p) (streamDependency p) ++
  (* Weight? (8) *)
  to_string (@of_Bvector 1 (weight p)).

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.4 *)
Definition buildRSTStream (e:ErrorCode) :=
  (* Error Code (32) *)
  to_string (N2ByteV_sized 4 (toErrorCodeId e)).

Open Scope list_scope.
Open Scope string_scope.
(* https://http2.github.io/http2-spec/index.html#rfc.section.6.5 *)
Fixpoint buildSettings_ (sets:list Setting) :
  ByteVector (length sets * 6) :=
  match sets with
  | List.nil => []
  | (sk, sv) :: tl =>
    (* Identifier (16) *)
     append (@of_Bvector 2 sk)
    (* Value (32) *)
    (append (@of_Bvector 4 sv)
            (buildSettings_ tl))
  end.

Definition buildSettings (sets : list Setting) : string :=
  to_string (buildSettings_ sets).

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.6 *)
Definition buildPushPromise
           (sid:StreamId) (hbf:HeaderBlockFragment)
           (padding':option Padding) :=
  with_padding
    ((* R: A single reserved bit *)
     (* Promised Stream ID (31) *)
     streamid_to_string false sid ++
     (* Header block Fragment ( * ) *)
     hbf)
    padding'.

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
  to_string (N2ByteV_sized 4 (toErrorCodeId e)) ++
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

Definition mkPadding (padFlag:bool) (padding:Padding) :=
  if padFlag then Some padding else None.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6 *)
Definition encodePayload (f:Frame) : string :=
  let mkPad := mkPadding (testPadded (flags (frameHeader f))) in
  match framePayload f with
  | DataFrame s p => buildData s (mkPad p)
  | HeadersFrame op hbf p => buildHeaders op hbf (mkPad p)
  | PriorityFrame p => buildPriority p
  | RSTStreamFrame e => buildRSTStream e
  | SettingsFrame sets => buildSettings sets
  | PushPromiseFrame sid hbf p =>
    buildPushPromise sid hbf (mkPad p)
  | PingFrame v => buildPing v
  | GoAwayFrame sid e s => buildGoAway sid e s
  | WindowUpdateFrame ws => buildWindowUpdate ws
  | ContinuationFrame hbf => buildContinuation hbf
  | UnknownFrame _ s => s
  end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Definition encodeFrame (f:Frame) : string :=
  let ftype := frameType f in
  let fheader := frameHeader f in
  to_string (encodeFrameHeader ftype fheader) ++
  encodePayload f.
