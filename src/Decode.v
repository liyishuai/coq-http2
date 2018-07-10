From HTTP2 Require Import Types
                          Util.BitVector
                          Util.ByteVector
                          Util.VectorUtil
                          Util.StringUtil
                          Util.OptionE.
From Coq Require Import Ascii NArith Nat String.
From ExtLib Require Import Functor Monad.
Import FunctorNotation MonadNotation.

Open Scope bool_scope.
Open Scope N_scope.
Open Scope monad_scope.

Program Definition decodeFrameHeader (v : ByteVector 9) : FrameType * FrameHeader :=
  let (vlength, v3) := splitAt 3 v in
  let length := N_of_ByteVector vlength in
  let (vtype, v4) := splitAt 1 v3 in
  let frameType := fromFrameTypeId (N_of_ByteVector vtype) in
  let (vflags, v5) := splitAt 1 v4 in
  let flags := Bvector_of_ByteVector vflags in
  let r_streamId := Bvector_of_ByteVector v5 in
  let streamId := N_of_Bvector (snd (splitAt 1 r_streamId)) in
  (frameType, {| payloadLength := length;
                 flags         := flags;
                 streamId      := streamId |}).

Obligation 1.
apply ByteVector_upperbound.
Qed.

Program Definition checkFrameHeader (settings : Settings)
           (typfrm : FrameType * FrameHeader) :
  OptionE unit :=
  let (typ, header) := typfrm in
  let length := payloadLength header in
  let fff    := flags         header in
  let id     := streamId      header in
  if settings SettingMaxFrameSize <? payloadLength header
  then inl (ConnectionError FrameSizeError "exceeds maximum frame size")
  else
    if nonZeroFrameType typ && isControl id
    then inl (ConnectionError ProtocolError "cannot used in control stream")
    else
      if zeroFrameType typ && negb (isControl id)
      then inl (ConnectionError ProtocolError "cannot used in non-zero stream")
      else
        let checkPadded :=
            if testPadded fff && (length <? 1)
            then inl (ConnectionError FrameSizeError "insufficient payload for Pad Length")
            else ret tt in
        match typ with
        | DataType => checkPadded
        | HeadersType =>
          checkPadded;;
          if testPriority fff
          then
            if length <? 5
            then inl (ConnectionError FrameSizeError "insufficient payload for priority fields")
            else
              if testPadded fff && (length <? 6)
              then inl (ConnectionError FrameSizeError "insufficient payload for Pad Length and priority fields")
              else ret tt
          else ret tt
        | PriorityType =>
          if length =? 5 then ret tt
          else inl (StreamError FrameSizeError id)
        | RSTStreamType =>
          if length =? 4 then ret tt
          else inl (ConnectionError
                      FrameSizeError
                      "payload length is not 4 in rst stream frame")
        | SettingsType =>
          if length mod 6 =? 0 then
            if testAck fff && negb (length =? 0)
            then inl (ConnectionError FrameSizeError "payload length must be 0 if ack flag is set")
            else ret tt
          else inl (ConnectionError FrameSizeError "payload length is not multiple of 6 in settings frame")
        | PushPromiseType =>
          (* checkme: https://hackage.haskell.org/package/http2-1.6.3/docs/src/Network-HTTP2-Decode.html#line-102 *)
          if settings SettingEnablePush =? 0
          then inl (ConnectionError ProtocolError "push not enabled")
          else
            if isResponse id
            then checkPadded
            else inl (ConnectionError ProtocolError "push promise must be used with even stream identifier")
        | PingType =>
          if length =? 8
          then ret tt
          else inl (ConnectionError FrameSizeError "payload length is 8 in ping frame")
        | GoAwayType =>
          if length <? 8
          then inl (ConnectionError FrameSizeError "goaway body must be 8 bytes or larger")
          else ret tt
        | WindowUpdateType =>
          if length =? 4
          then ret tt
          else inl (ConnectionError FrameSizeError "payload length is 4 in window update frame")
        | _ => ret tt
        end.

Solve All Obligations with repeat constructor; intro H0; inversion H0.

Open Scope nat_scope.

(* Stronger constraints? *)
Definition decodeWithPadding
           (h : FrameHeader)
           (s : string) :
  HTTP2Error + string :=
  let fff := flags h in
  if testPadded fff
  then
    match s with
    | "" =>
      inl (ConnectionError FrameSizeError "empty payload")
    | String a s' =>
      let padlen := nat_of_ascii a in
      if padlen <? length s
      then inr (substring 0 padlen s')
      else inl (ConnectionError ProtocolError "padding is not enough")
    end
  else inr s.

Close Scope nat_scope.

Definition FramePayloadDecoder (frameType : FrameType) :=
  FrameHeader -> string -> OptionE (FramePayload frameType).

Definition decodeDataFrame : FramePayloadDecoder DataType :=
  fun h s => DataFrame <$> decodeWithPadding h s.

Definition priority (v : ByteVector 5) : Priority :=
  let (v0, v4) := splitAt 4 v in
  let (e, vid) := Vector_uncons (Bvector_of_ByteVector v0) in
  let id := N_of_Bvector vid in
  let weight := N_of_ByteVector v4 + 1 in
  {| exclusive := e;
     streamDependency := id;
     weight := weight |}.

Program Definition decodeHeadersFrame : FramePayloadDecoder HeadersType :=
  fun h s =>
    let fff := flags h in
    if testPriority fff
    then
      match String_splitAt 5 s with
      | Some (s0, s5) =>
        let p := priority (from_string s0) in
        ret (HeadersFrame (Some p) s5)
      | None => inl (ConnectionError ProtocolError "payload is not enough")
      end
    else ret (HeadersFrame None s).

Solve Obligations with intros; eapply String_splitAt_lengthFst; eauto.
