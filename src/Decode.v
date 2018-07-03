From HTTP2 Require Import Types Util.BitVector Util.ByteVector Util.VectorUtil.

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
