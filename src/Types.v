From Coq Require Vector.
From Coq Require Import NArith String.
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
Inductive  SettingKeyId :=
  SettingHeaderTableSize
| SettingEnablePush
| SettingMaxConcurrentStreams
| SettingInitialWindowSize
| SettingMaxFrameSize
| SettingMaxHeaderBlockSize.
Definition Setting := SettingValue * SettingKeyId.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6.9 *)
Definition WindowSize := N.

(* https://http2.github.io/http2-spec/index.html#rfc.section.7 *)
Definition ErrorCode := N.
Inductive ErrorCodeId :=
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
| UnknownErrorCode : ErrorCode -> ErrorCodeId.

Definition fromErrorCodeId (e:ErrorCodeId) : ErrorCode :=
  match e with
  | NoError              => 0x0
  | ProtocolError        => 0x1
  | InternalError        => 0x2
  | FlowControlError     => 0x3
  | SettingsTimeout      => 0x4
  | StreamClosed         => 0x5
  | FrameSizeError       => 0x6
  | RefusedStream        => 0x7
  | Cancel               => 0x8
  | CompressionError     => 0x9
  | ConnectError         => 0xa
  | EnhanceYourCalm      => 0xb
  | InadequateSecurity   => 0xc
  | HTTP11Required       => 0xd
  | (UnknownErrorCode w) => w
  end.

Definition toErrorCodeId (e:ErrorCode) : ErrorCodeId :=
  match e with
  | 0x0 => NoError
  | 0x1 => ProtocolError
  | 0x2 => InternalError
  | 0x3 => FlowControlError
  | 0x4 => SettingsTimeout
  | 0x5 => StreamClosed
  | 0x6 => FrameSizeError
  | 0x7 => RefusedStream
  | 0x8 => Cancel
  | 0x9 => CompressionError
  | 0xa => ConnectError
  | 0xb => EnhanceYourCalm
  | 0xc => InadequateSecurity
  | 0xd => HTTP11Required
  | w   => UnknownErrorCode w
  end.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Definition FrameFlags  := Vector.t bool 8.
Inductive  FrameHeader :=
  { payloadLength : nat;
    flags         : FrameFlags;
    streamId      : StreamId
  }.

(* https://http2.github.io/http2-spec/index.html#rfc.section.6 *)
Definition FrameType    := N.
Inductive  FramePayload : FrameType -> Type :=
  DataFrame         : string                                -> FramePayload 0
| HeadersFrame      : option Priority -> HeaderBlockFragment -> FramePayload 1
| PriorityFrame     : Priority                              -> FramePayload 2
| RSTStreamFrame    : ErrorCodeId                           -> FramePayload 3
| SettingsFrame     : list Setting                          -> FramePayload 4
| PushPromiseFrame  : StreamId        -> HeaderBlockFragment -> FramePayload 5
| PingFrame         : string                                -> FramePayload 6
| GoAwayFrame       : StreamId       -> ErrorCodeId -> string -> FramePayload 7
| WindowUpdateFrame : WindowSize                            -> FramePayload 8
| ContinuationFrame : HeaderBlockFragment                   -> FramePayload 9
| UnknownFrame type : string                                -> FramePayload type.

Inductive Frame :=
  { frameHeader  : FrameHeader;
    frameType    : FrameType;
    framePayload : FramePayload frameType
  }.
