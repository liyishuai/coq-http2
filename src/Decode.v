From HTTP2 Require Import
     Equiv
     Encode
     Types
     Util.BitVector
     Util.ByteVector
     Util.Parser
     Util.VectorUtil
     Util.StringUtil.
From Coq Require Import NArith.
From ExtLib Require Import Functor Monad.
Import FunctorNotation MonadNotations.
Import IMonadNotations.

Open Scope bool_scope.
Open Scope N_scope.
Open Scope monad_scope.

Program Definition decodeFrameHeader {m : nat -> Tycon}
        `{IMonad_nat m} `{MParser byte (m 1%nat)} :
  m 9%nat (FrameType * FrameHeader)%type :=
  icast (
    let fromFrameTypeId' x := fromFrameTypeId (N_of_ByteVector x) in
    length     <-(N_of_ByteVector)       iget_vec 3;;
    frameType  <-(fromFrameTypeId')      iget_vec 1;;
    flags      <-(Bvector_of_ByteVector) iget_vec 1;;
    r_streamId <-(Bvector_of_ByteVector) iget_vec 4;;
    let streamId := N_of_Bvector (snd (splitAt 1 r_streamId)) in
    iret (frameType, {| payloadLength := length;
                        flags         := flags;
                        streamId      := streamId |}))%imonad.

Next Obligation.
apply ByteVector_upperbound.
Qed.

Program Definition checkFrameHeader {m : Tycon}
        `{Monad m} `{MError HTTP2Error m}
        (settings : Settings) (typfrm : FrameType * FrameHeader) :
  m unit :=
  let (typ, header) := typfrm in
  let length := payloadLength header in
  let fff    := flags         header in
  let id     := streamId      header in
  assert (payloadLength header <=? settings SettingMaxFrameSize)
         (ConnectionError FrameSizeError
                          "exceeds maximum frame size");;
  assert (negb (nonZeroFrameType typ && isControl id))
         (ConnectionError ProtocolError
                          "cannot used in control stream");;
  assert (negb (zeroFrameType typ && negb (isControl id)))
         (ConnectionError ProtocolError
                          "cannot used in non-zero stream");;
  let checkPadded :=
      assert (negb (testPadded fff && (length <? 1)))
             (ConnectionError
                FrameSizeError
                "insufficient payload for Pad Length") in
  match typ with
  | DataType => checkPadded
  | HeadersType =>
    checkPadded;;
    when (testPriority fff) (
      assert (5 <=? length)
             (ConnectionError
                FrameSizeError
                "insufficient payload for priority fields");;
      when (testPadded fff) (
        assert (6 <=? length)
               (ConnectionError
                  FrameSizeError
                  "insufficient payload for Pad Length and priority fields")
      )
    )
  | PriorityType =>
    assert (5 =? length)
           (StreamError FrameSizeError id)
  | RSTStreamType =>
    assert (4 =? length)
           (ConnectionError
              FrameSizeError
              "payload length is not 4 in rst stream frame")
  | SettingsType =>
    assert (0 =? length mod 6)
           (ConnectionError
              FrameSizeError
              "payload length is not multiple of 6 in settings frame");;
    when (testAck fff) (
      assert (0 =? length)
             (ConnectionError FrameSizeError
                              "payload length must be 0 if ack flag is set")
    )
  | PushPromiseType =>
    (* checkme: https://hackage.haskell.org/package/http2-1.6.3/docs/src/Network-HTTP2-Decode.html#line-102 *)
    assert (negb (0 =? settings SettingEnablePush))
           (ConnectionError ProtocolError "push not enabled");;
    assert (isResponse id)
           (ConnectionError
              ProtocolError
              "push promise must be used with even stream identifier");;
    checkPadded
  | PingType =>
    assert (8 =? length)
           (ConnectionError
              FrameSizeError
              "payload length must be 8 bytes in ping frame")
  | GoAwayType =>
    assert (8 <=? length)
           (ConnectionError
              FrameSizeError
              "goaway body must be 8 bytes or larger")
  | WindowUpdateType =>
    assert (4 =? length)
           (ConnectionError
              FrameSizeError
              "payload length must be 4 bytes in window update frame")
  | _ => ret tt
  end.

Solve All Obligations with repeat constructor; intro; discriminate.

Definition decodeWithPadding {m : Tycon}
           `{Monad m} `{MError HTTP2Error m} `{MParser byte m}
           (len : N) (h : FrameHeader) : m bytes :=
  let fff := flags h in
  if testPadded fff then (
    padlen <-(N_of_ascii) get_byte;;
    (* 1 byte for to parse padlen *)
    assert (padlen + 1 <=? len)
           (ConnectionError ProtocolError "too much padding");;
    bs <- get_bytes (N.to_nat (len - padlen - 1));;
    get_bytes (N.to_nat padlen);; (* Discard padding *)
    ret bs
  )%monad else
    get_bytes (N.to_nat len).

Close Scope nat_scope.

Definition FramePayloadDecoder (frameType : FrameType) :=
  forall m `{Monad m} `{MError HTTP2Error m} `{MParser byte m},
    N -> FrameHeader -> m (FramePayload frameType).

Definition decodeDataFrame : FramePayloadDecoder DataType :=
  fun _ _ _ _ n h => DataFrame <$> decodeWithPadding n h.

Program Definition priority {m : nat -> Tycon}
        `{IMonad_nat m} `{MParser byte (m 1%nat)} :
  m 5%nat Priority :=
  icast (
    (* Split a 32-bit field into 1+31. *)
    let uncons x : bit * _ :=
        Vector_uncons (@Bvector_of_ByteVector 4 x) in
    '(e, vid) <-(uncons) iget_vec 4;;
    let id := N_of_Bvector vid in
    w <-(N_of_ascii) get_byte;;
    let weight := w + 1 in
    iret {| exclusive := e;
            streamDependency := id;
            weight := weight |}
  )%imonad.

Program Definition decodeHeadersFrame :
  FramePayloadDecoder HeadersType :=
  fun _ _ _ _ n h =>
    let fff := flags h in
    if testPriority fff
    then
      p <- unindex priority;;
      s <- get_bytes (N.to_nat (n - 5));;
      ret (HeadersFrame (Some p) s)
    else
      s <- get_bytes (N.to_nat n);;
      ret (HeadersFrame None s).

Program Definition decodePriorityFrame :
  FramePayloadDecoder PriorityType :=
  fun _ _ _ _ n h =>
    (* n must be 5 *)
    p <- unindex priority;;
    ret (PriorityFrame p).
