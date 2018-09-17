From Coq Require Import
     NArith
     Bool.Bvector.

From SimpleIO Require Import
     IOMonad CoqPervasives.

From HTTP2 Require Import
     Decode
     Encode
     Pretty
     Types
     Util.BitVector
     Util.ByteVector
     Util.IO
     Util.Parser.

Require Extraction.

Definition test_file := "io_roundtrip.http2".

Import IONotations.

Definition example_ping_frame : Frame := {|
  frameHeader := {|
    payloadLength := Bvector_of_N 8;
    flags := Bvector_of_N 0;
    streamId := Bvector_of_N 0;
  |};
  frameType := PingType;
  framePayload := PingFrame (ByteVector_of_N _ 0);
|}.

Definition main : IO unit :=
  out <- open_out test_file;;
  output_string out (encodeFrame None example_ping_frame);;
  close_out out;;
  inp <- open_in test_file;;
  fh <- run_file_parser (unindex decodeFrameHeader) inp;;
  let '(ft, fh) := fh in
  print_endline (pretty_FrameHeader fh);;
  close_in inp.

Definition exe := unsafe_run main.

Extraction "io_roundtrip.ml" exe.
