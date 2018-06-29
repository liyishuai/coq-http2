From Coq Require Import List Bvector NArith String.
From HTTP2 Require Import Util.BitField.
Import ListNotations.
Open Scope N_scope.
Open Scope type_scope.

(* https://http2.github.io/http2-spec/index.html#rfc.section.5.1.1 *)
Definition StreamId := N.

(* https://http2.github.io/http2-spec/index.html#rfc.section.5.3.2 *)
Definition Weight := N.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.2 *)
Definition HeaderBlockFragment := string.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.3 *)
Inductive Priority :=
  { exclusive : bool;
    streamDependency : StreamId;
    weight : Weight
  }.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.5 *)
Definition SettingValue := N.
Definition SettingKeyId := N.
Inductive  SettingKey   :=
  SettingHeaderTableSize        (* 0x1 *)
| SettingEnablePush             (* 0x2 *)
| SettingMaxConcurrentStreams   (* 0x3 *)
| SettingInitialWindowSize      (* 0x4 *)
| SettingMaxFrameSize           (* 0x5 *)
| SettingMaxHeaderBlockSize.    (* 0x6 *)
| SettingUnknown : SettingKeyId -> SettingKey
(* Extensions are permitted to use new settings. (Section 5.5) *)
Definition Setting  := SettingKey * SettingValue.

Definition fromSettingKeyId (id : SettingKeyId) : SettingKey :=
  match id with
  | 1 => SettingHeaderTableSize
  | 2 => SettingEnablePush
  | 3 => SettingMaxConcurrentStreams
  | 4 => SettingInitialWindowSize
  | 5 => SettingMaxFrameSize
  | 6 => SettingMaxHeaderBlockSize
  | _ => SettingUnknown id
  end.

Definition toSettingKeyId (key : SettingKey) : SettingKeyId :=
  match key with
  | SettingHeaderTableSize      => 1
  | SettingEnablePush           => 2
  | SettingMaxConcurrentStreams => 3
  | SettingInitialWindowSize    => 4
  | SettingMaxFrameSize         => 5
  | SettingMaxHeaderBlockSize   => 6
  | SettingUnknown id           => id
  end.
Coercion toSettingKeyId : SettingKey >-> SettingKeyId.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.9 *)
Definition WindowSize := N.

(* https://http2.github.io/http2-spec/index.html#rfc.section.7 *)
Definition ErrorCodeId := N.
Inductive ErrorCode :=
  NoError                       (* 0x0 *)
| ProtocolError                 (* 0x1 *)
| InternalError                 (* 0x2 *)
| FlowControlError              (* 0x3 *)
| SettingsTimeout               (* 0x4 *)
| StreamClosed                  (* 0x5 *)
| FrameSizeError                (* 0x6 *)
| RefusedStream                 (* 0x7 *)
| Cancel                        (* 0x8 *)
| CompressionError              (* 0x9 *)
| ConnectError                  (* 0xa *)
| EnhanceYourCalm               (* 0xb *)
| InadequateSecurity            (* 0xc *)
| HTTP11Required                (* 0xd *)
| UnknownErrorCode : ErrorCodeId -> ErrorCode.
(* Extensions are permitted to use new error codes. (Section 5.5) *)

Definition fromErrorCodeId (e:ErrorCodeId) : ErrorCode :=
  match e with
  | 0 => NoError
  | 1 => ProtocolError
  | 2 => InternalError
  | 3 => FlowControlError
  | 4 => SettingsTimeout
  | 5 => StreamClosed
  | 6 => FrameSizeError
  | 7 => RefusedStream
  | 8 => Cancel
  | 9 => CompressionError
  | 10 => ConnectError
  | 11 => EnhanceYourCalm
  | 12 => InadequateSecurity
  | 13 => HTTP11Required
  | w   => UnknownErrorCode w
  end.
Coercion fromErrorCodeId : ErrorCodeId >-> ErrorCode.

Definition toErrorCodeId (e:ErrorCode) : ErrorCodeId :=
  match e with
  | NoError              => 0
  | ProtocolError        => 1
  | InternalError        => 2
  | FlowControlError     => 3
  | SettingsTimeout      => 4
  | StreamClosed         => 5
  | FrameSizeError       => 6
  | RefusedStream        => 7
  | Cancel               => 8
  | CompressionError     => 9
  | ConnectError         => 10
  | EnhanceYourCalm      => 11
  | InadequateSecurity   => 12
  | HTTP11Required       => 13
  | (UnknownErrorCode w) => w
  end.
Coercion toErrorCodeId : ErrorCode >-> ErrorCodeId.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Definition FrameFlagsField  := Bvector 8.
Inductive  FrameHeader :=
  { payloadLength : N;
    flags         : FrameFlagsField;
    streamId      : StreamId
  }.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6 *)
Definition FrameTypeId    := N.
Inductive FrameType :=
  DataType                      (* 0x0 *)
| HeadersType                   (* 0x1 *)
| PriorityType                  (* 0x2 *)
| RSTStreamType                 (* 0x3 *)
| SettingsType                  (* 0x4 *)
| PushPromiseType               (* 0x5 *)
| PingType                      (* 0x6 *)
| GoAwayType                    (* 0x7 *)
| WindowUpdateType              (* 0x8 *)
| ContinuationType              (* 0x9 *)
| UnknownType : FrameTypeId -> FrameType.
(* Extensions are permitted to define new frame types. (Section 5.5) *)

Definition fromFrameTypeId (id : FrameTypeId) : FrameType :=
  match id with
  | 0 => DataType
  | 1 => HeadersType
  | 2 => PriorityType
  | 3 => RSTStreamType
  | 4 => SettingsType
  | 5 => PushPromiseType
  | 6 => PingType
  | 7 => GoAwayType
  | 8 => WindowUpdateType
  | 9 => ContinuationType
  | _ => UnknownType id
  end.
Coercion fromFrameTypeId : FrameTypeId >-> FrameType.

Definition toFrameTypeId (type : FrameType) : FrameTypeId :=
  match type with
  | DataType         => 0
  | HeadersType      => 1
  | PriorityType     => 2
  | RSTStreamType    => 3
  | SettingsType     => 4
  | PushPromiseType  => 5
  | PingType         => 6
  | GoAwayType       => 7
  | WindowUpdateType => 8
  | ContinuationType => 9
  | UnknownType id   => id
  end.
Coercion toFrameTypeId : FrameType >-> FrameTypeId.

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
| UnknownFlags type : FrameFlags (UnknownType type)
.

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
  | UnknownType _ => UnknownFlags _
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

Inductive  FramePayload : FrameType -> Type :=
  DataFrame         : string                                -> FramePayload DataType
| HeadersFrame      : option Priority -> HeaderBlockFragment -> FramePayload HeadersType
| PriorityFrame     : Priority                              -> FramePayload PriorityType
| RSTStreamFrame    : ErrorCode                             -> FramePayload RSTStreamType
| SettingsFrame     : list Setting                          -> FramePayload SettingsType
| PushPromiseFrame  : StreamId        -> HeaderBlockFragment -> FramePayload PushPromiseType
| PingFrame         : Bvector 64                            -> FramePayload PingType
| GoAwayFrame       : StreamId         -> ErrorCode -> string -> FramePayload GoAwayType
| WindowUpdateFrame : WindowSize                            -> FramePayload WindowUpdateType
| ContinuationFrame : HeaderBlockFragment                   -> FramePayload ContinuationType
| UnknownFrame type : string                                -> FramePayload type.

Inductive Frame :=
  { frameHeader  : FrameHeader;
    frameType    : FrameType;
    framePayload : FramePayload frameType
  }.
