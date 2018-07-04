From HTTP2 Require Import Types Util.BitVector Util.ByteVector Util.VectorUtil.
From Coq Require Import NArith.
Open Scope bool_scope.
Open Scope N_scope.

Definition decodeFrameHeader (v : ByteVector 9) : FrameType * FrameHeader :=
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

Definition checkFrameHeader (settings : Settings)
           (typfrm : FrameType * FrameHeader) :
  HTTP2Error + FrameType * FrameHeader :=
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
        match typ with
        | PriorityType =>
          if length =? 5 then inr typfrm
          else inl (StreamError FrameSizeError id)
        | RSTStreamType =>
          if length =? 4 then inr typfrm
          else inl (ConnectionError
                      FrameSizeError
                      "payload length is not 4 in rst stream frame")
        | SettingsType =>
          if length mod 6 =? 0 then
            if testAck fff && negb (length =? 0)
            then inl (ConnectionError FrameSizeError "payload length must be 0 if ack flag is set")
            else inr typfrm
          else inl (ConnectionError FrameSizeError "payload length is not multiple of 6 in settings frame")
        | PushPromiseType =>
          (* checkme: https://hackage.haskell.org/package/http2-1.6.3/docs/src/Network-HTTP2-Decode.html#line-102 *)
          if settings SettingEnablePush =? 0
          then inl (ConnectionError ProtocolError "push not enabled")
          else
            if isResponse id
            then inr typfrm
            else inl (ConnectionError ProtocolError "push promise must be used with even stream identifier")
        | PingType =>
          if length =? 8
          then inr typfrm
          else inl (ConnectionError FrameSizeError "payload length is 8 in ping frame")
        | GoAwayType =>
          if length <? 8
          then inl (ConnectionError FrameSizeError "goaway body must be 8 bytes or larger")
          else inr typfrm
        | WindowUpdateType =>
          if length =? 4
          then inr typfrm
          else inl (ConnectionError FrameSizeError "payload length is 4 in window update frame")
        | _ => inr typfrm
        end.
