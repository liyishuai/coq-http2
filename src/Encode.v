From HTTP2 Require Import Types.
From Coq Require Import BinNat.
From Coq Require Import String.
From Coq Require Import Bvector.
From Coq Require Import List.
Open Scope N_scope.
Open Scope list_scope.
Open Scope string_scope.

(* Converts bool to single bit string *)
Definition bool_to_string (b:bool) : string :=
  if b then "1" else "0".

(* Converts binary nat i to an n bit MSB binary string. *)
Fixpoint binnat_to_bin_string (i:N) (n:nat) : string :=
  let val := bool_to_string (N.testbit_nat i n) in
  match n with
  | O => ""
  | S n' => val ++ binnat_to_bin_string i n'
  end.

Definition pad_len (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    (* Pad Length? (8) *)
    binnat_to_bin_string n 8
  end.

Definition padding (p:option N) : string :=
  match p with
  | None => ""
  | Some n =>
    N.peano_rect (fun _ => string) "" (fun n' s => "0" ++ s) n
  end.

(* Converts boolean vector v of length n to an n bit MSB binary string.
   Note BVectors are LSB, https://coq.inria.fr/library/Coq.Bool.Bvector.html *)
Definition bvector_to_bin_string {n:nat} (v:Bvector n) : string :=
  Vector.fold_right (fun (val:bool) acc => acc ++ (bool_to_string val)) v "".

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
(* NOTE: header is the string between length and payload. *)
Definition encodeFrameHeader (f:Frame) : string :=
  let fh := frameHeader f in
  (* Length (24) *)
  let s_len := binnat_to_bin_string (payloadLength fh) 24 in
  (* Type (8) *)
  let s_ft := binnat_to_bin_string (toFrameTypeId (frameType f)) 8 in
  (* Flags (8) *)
  let s_flgs := bvector_to_bin_string (flags fh) in
  (* R is a reserved 1-bit field, MUST remain unset when sending and MUST be
     ignored when receiving. *)
  let R := "0" in
  (* Stream Identifier (31) *)
  let s_si := binnat_to_bin_string (streamId fh) 31 in
  s_ft ++ s_flgs ++ R ++ s_si.

(* TODO: add padding for all of these *)
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
    bool_to_string (exclusive p) ++
    (* StreamDependency? (31) *)
    binnat_to_bin_string (streamDependency p) 31 ++
    (* Weight? (8) *)
    binnat_to_bin_string (weight p) 8
  end
    (* Header Block Fragment ( * ) *)
    ++ hbf ++
    (* Padding ( * ) *)
    padding p.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.3 *)
Definition buildPriority (p:Priority) :=
  (* E *)
  bool_to_string (exclusive p) ++
  (* StreamDependency? (31) *)
  binnat_to_bin_string (streamDependency p) 31 ++
  (* Weight? (8) *)
  binnat_to_bin_string (weight p) 8.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.4 *)
Definition buildRSTStream (e:ErrorCode) :=
  (* Error Code (32) *)
  binnat_to_bin_string (toErrorCodeId e) 32.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.5 *)
Fixpoint buildSettings (sets:list Setting) :=
  match sets with
  | nil => ""
  | (sk, sv) :: tl =>
    (* Identifier (16) *)
    binnat_to_bin_string (toSettingKeyId sk) 16
    (* Value (32) *)
    ++ binnat_to_bin_string sv 32 ++ buildSettings tl
  end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.6 *)
Definition buildPushPromise (p:option N) (sid:StreamId)
           (hbf:HeaderBlockFragment) :=
  (* Pad Length? (8) *)
  pad_len p ++
  (* R: A single reserved bit *)
  "0" ++
  (* Promised Stream ID (31) *)
  binnat_to_bin_string sid 31 ++
  (* Header block Fragment ( * ) *)
  hbf ++
  (* Padding ( * ) *)
  padding p
.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.7 *)
Definition buildPing (v:Bvector 64) :=
  (* Opaque Datra (64) *)
  bvector_to_bin_string v.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.8 *)
Definition buildGoAway (sid:StreamId) (e:ErrorCode) (s:string) :=
  (* R *)
  "0" ++
  (* Last-Stream-ID (31) *)
  binnat_to_bin_string sid 31 ++
  (* Error Code (32) *)    
  binnat_to_bin_string (toErrorCodeId e) 32 ++
  (* Additional Debug Data ( * ) *)
  s.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.9 *)
Definition buildWindowUpdate (ws:WindowSize) :=
  (* R *)
  "0" ++
  (* Window Size Increment (31) *)    
  binnat_to_bin_string ws 31.

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