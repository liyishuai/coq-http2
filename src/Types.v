From Coq Require Import
     Bvector
     FMaps
     NArith
     OrderedTypeEx
     String
     Vector
     micromega.Psatz.
From HTTP2 Require Import
     Equiv
     Util.BitField
     Util.BitVector
     Util.ByteVector
     Util.VectorUtil.
Import ListNotations.
Open Scope N_scope.
Open Scope type_scope.

(* https://http2.github.io/http2-spec/index.html#rfc.section.5.1.1 *)
Definition StreamId := Bvector 31.
Definition isControl : StreamId -> bool := forallb negb.
Definition isRequest : StreamId -> bool := hd.
Definition isResponse (v : StreamId) : bool := existsb id v && negb (hd v).

(* https://http2.github.io/http2-spec/index.html#rfc.section.5.3.2 *)
Definition Weight := Bvector 8.
Coercion Weight2N := Bv2N       8 : Weight -> N.
Coercion N2Weight := N2Bv_sized 8 : N -> Weight.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.2 *)
Definition HeaderBlockFragment := string.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.3 *)
Inductive Priority :=
  { exclusive : bool;
    streamDependency : StreamId;
    weight : Weight
  }.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.5 *)
Definition SettingValue := Bvector 32.
Definition SettingKey   := Bvector 16.
Definition SettingKeyId := N.
Coercion SettingValue2N := Bv2N       32 : SettingValue -> N.
Coercion N2SettingValue := N2Bv_sized 32 : N -> SettingValue.
Coercion SettingKey2Id  := Bv2N       16 : SettingKey   -> SettingKeyId.
Coercion Id2SettingKey  := N2Bv_sized 16 : SettingKeyId -> SettingKey.
Definition SettingHeaderTableSize      : SettingKeyId := 1.
Definition SettingEnablePush           : SettingKeyId := 2.
Definition SettingMaxConcurrentStreams : SettingKeyId := 3.
Definition SettingInitialWindowSize    : SettingKeyId := 4.
Definition SettingMaxFrameSize         : SettingKeyId := 5.
Definition SettingMaxHeaderBlockSize   : SettingKeyId := 6.

(* Extensions are permitted to use new settings. (Section 5.5) *)
Definition Setting  := SettingKey * SettingValue.
Definition Settings := SettingKey -> SettingValue.

Definition defaultSettings (key : SettingKeyId) : SettingValue :=
    match key with
    | 1 =>       4096              (* SettingHeaderTableSize   *)
    | 2 =>          1              (* SettingEnablePush        *)
    | 4 =>      65535              (* SettingInitialWindowSize *)
    | 5 =>      16384              (* SettingMaxFrameSize      *)
    | _ => 4294967295
    end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.9 *)
Definition WindowSize := Bvector 31.

(* https://http2.github.io/http2-spec/index.html#rfc.section.7 *)
Definition ErrorCodeId := N.
Definition ErrorCode   := Bvector 32.
Coercion   toErrorCodeId := Bv2N 32       : ErrorCode -> ErrorCodeId.
Coercion fromErrorCodeId := N2Bv_sized 32 : ErrorCodeId -> ErrorCode.

Definition NoError            : ErrorCodeId :=  0.
Definition ProtocolError      : ErrorCodeId :=  1.
Definition InternalError      : ErrorCodeId :=  2.
Definition FlowControlError   : ErrorCodeId :=  3.
Definition SettingsTimeout    : ErrorCodeId :=  4.
Definition StreamClosed       : ErrorCodeId :=  5.
Definition FrameSizeError     : ErrorCodeId :=  6.
Definition RefusedStream      : ErrorCodeId :=  7.
Definition Cancel             : ErrorCodeId :=  8.
Definition CompressionError   : ErrorCodeId :=  9.
Definition EnhanceYourCalm    : ErrorCodeId := 10.
Definition InadequateSecurity : ErrorCodeId := 11.
Definition HTTP11Required     : ErrorCodeId := 12.

Inductive HTTP2Error :=
  ConnectionError : ErrorCode -> string   -> HTTP2Error
| StreamError     : ErrorCode -> StreamId -> HTTP2Error.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Definition PayloadLength   := Bvector 24.
Definition FrameFlagsField := Bvector 8.
Inductive  FrameHeader :=
  { payloadLength : PayloadLength;
    flags         : FrameFlagsField;
    streamId      : StreamId
  }.
Coercion PayloadLength2N := Bv2N 24       : PayloadLength -> N.
Coercion N2PayloadLength := N2Bv_sized 24 : N -> PayloadLength.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6 *)
Definition FrameTypeId   := N.
Definition FrameType     := Bvector 8.
Coercion   toFrameTypeId := Bv2N       8 : FrameType -> FrameTypeId.
Coercion fromFrameTypeId := N2Bv_sized 8 : FrameTypeId -> FrameType.

Definition DataType         : FrameTypeId := 0.
Definition HeadersType      : FrameTypeId := 1.
Definition PriorityType     : FrameTypeId := 2.
Definition RSTStreamType    : FrameTypeId := 3.
Definition SettingsType     : FrameTypeId := 4.
Definition PushPromiseType  : FrameTypeId := 5.
Definition PingType         : FrameTypeId := 6.
Definition GoAwayType       : FrameTypeId := 7.
Definition WindowUpdateType : FrameTypeId := 8.
Definition ContinuationType : FrameTypeId := 9.

(* Frames that can only be used in control frames (ID 0) *)
Definition zeroFrameType (typ : FrameTypeId) : bool :=
  List.existsb (N.eqb typ)
               [SettingsType; PingType; GoAwayType].

(* Frames that must be associated to a stream (ID <> 0).
   Equivalently, they cannot be used in control frames *)
Definition nonZeroFrameType (typ : FrameTypeId) : bool :=
  List.existsb (N.eqb typ)
               [ DataType
               ; HeadersType
               ; PriorityType
               ; RSTStreamType
               ; PushPromiseType
               ; ContinuationType
               ].

Inductive FrameFlags : FrameType -> Type :=
| DataFlags
    (END_STREAM : Bit 0)
    (PADDED     : Bit 3)
  : FrameFlags DataType
| HeadersFlags
    (END_STREAM  : Bit 0)
    (END_HEADERS : Bit 2)
    (PADDED      : Bit 3)
    (PRIORITY    : Bit 5)
  : FrameFlags HeadersType
| PriorityFlags  : FrameFlags PriorityType
| RSTStreamFlags : FrameFlags RSTStreamType
| SettingsFlags
    (ACK : Bit 0)
  : FrameFlags SettingsType
| PushPromiseFlags
    (END_HEADERS : Bit 2)
    (PADDED      : Bit 8)
  : FrameFlags PushPromiseType
| PingFlags
    (ACK : Bit 0)
  : FrameFlags PingType
| GoAwayFlags : FrameFlags GoAwayType
| WindowUpdateFlags : FrameFlags WindowUpdateType
| ContinuationFlags
    (END_HEADERS : Bit 2)
  : FrameFlags ContinuationType
| UnknownFlags type : FrameFlags type
.

Definition testEndStream  : FrameFlagsField -> bool := BVnth 0.
Definition testAck        : FrameFlagsField -> bool := BVnth 0.
Definition testEndHeaders : FrameFlagsField -> bool := BVnth 2.
Definition testPadded     : FrameFlagsField -> bool := BVnth 3.
Definition testPriority   : FrameFlagsField -> bool := BVnth 5.

Definition fromFrameFlagsField type (fff : FrameFlagsField) :
  FrameFlags type :=
  let b n := @toBit _ n fff in
  (* The position [n] of each bit is inferred. *)
  match type with
  | DataType => DataFlags (b _) (b _)
  | HeadersType => HeadersFlags (b _) (b _) (b _) (b _)
  | PriorityType => PriorityFlags
  | RSTStreamType => RSTStreamFlags
  | SettingsType => SettingsFlags (b _)
  | PushPromiseType => PushPromiseFlags (b _) (b _)
  | PingType => PingFlags (b _)
  | GoAwayType => GoAwayFlags
  | WindowUpdateType => WindowUpdateFlags
  | ContinuationType => ContinuationFlags (b _)
  | _ => UnknownFlags _
  end.

Definition toFrameFlagsField type (ff : FrameFlags type) :
  FrameFlagsField :=
  let bits := List.fold_right (BVor _) (Bvect_false 8) in
  let b {n} (_x : Bit n) := fromBit _x in
  bits
    match ff with
    | DataFlags _1 _2 => [b _1; b _2]
    | HeadersFlags _1 _2 _3 _4 => [b _1; b _2; b _3; b _4]
    | SettingsFlags _1 => [b _1]
    | PushPromiseFlags _1 _2 => [b _1; b _2]
    | PingFlags _1 => [b _1]
    | ContinuationFlags _1 => [b _1]
    | PriorityFlags | RSTStreamFlags
    | GoAwayFlags | WindowUpdateFlags
    | UnknownFlags _ => []
    end%list.

Instance EquivFrameFlags {typ} : Equiv (FrameFlags typ) :=
  { equiv := eq_equiv (toFrameFlagsField typ) }.

Inductive  FramePayload : FrameType -> Type :=
  DataFrame         : string                                -> FramePayload DataType
| HeadersFrame      : option Priority -> HeaderBlockFragment -> FramePayload HeadersType
| PriorityFrame     : Priority                              -> FramePayload PriorityType
| RSTStreamFrame    : ErrorCode                             -> FramePayload RSTStreamType
| SettingsFrame     : list Setting                          -> FramePayload SettingsType
| PushPromiseFrame  : StreamId        -> HeaderBlockFragment -> FramePayload PushPromiseType
| PingFrame         : ByteVector 8                          -> FramePayload PingType
| GoAwayFrame       : StreamId         -> ErrorCode -> string -> FramePayload GoAwayType
| WindowUpdateFrame : WindowSize                            -> FramePayload WindowUpdateType
| ContinuationFrame : HeaderBlockFragment                   -> FramePayload ContinuationType
| UnknownFrame type : string                                -> FramePayload type.

Inductive Frame :=
  { frameHeader  : FrameHeader;
    frameType    : FrameType;
    framePayload : FramePayload frameType
  }.
