From Coq Require Import
     NArith
     Bool.Bvector
     ByteVector
     String.

Import StringSyntax.

From ExtLib.Data Require Import Monads.EitherMonad.

From SimpleIO Require Import
     IOMonad CoqPervasives.

From HTTP2 Require Import
     Decode
     Encode
     Pretty
     Types
     Util.BitVector
     Util.IO
     Util.Parser.

Require Extraction.

Definition test_file := "io_roundtrip.http2".

Import IONotations.

Definition example_ping_frame : Frame := {|
  frameHeader := {|
    payloadLength := N2Bv_sized _ 8;
    flags := N2Bv_sized _ 0;
    streamId := N2Bv_sized _ 0;
  |};
  frameType := PingType;
  framePayload := PingFrame (N2ByteV_sized _ 0);
|}.

Definition main : IO unit :=
  out <- open_out test_file;;
  output_string out (encodeFrame example_ping_frame);;
  close_out out;;
  inp <- open_in test_file;;
  ef <- run_file_parser (unEitherT (decodeFrame defaultSettings)) inp;;
  let out := match ef with
             | inl e => pretty_HTTP2Error e
             | inr f => pretty_Frame f
             end
  in
  print_string out;;
  close_in inp.

Definition exe := unsafe_run main.

Extraction "io_roundtrip.ml" exe.
