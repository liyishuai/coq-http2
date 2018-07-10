From HTTP2 Require Import Encode Types Util.BitField Util.BitVector.
From Coq Require Import Bvector List String Strings.Ascii.
Open Scope list_scope.

(* Http2 sample dump:
   https://wiki.wireshark.org/HTTP2 *)

Program Definition f21 : Frame :=
  let fh := Build_FrameHeader 4 (Bvect_false 8) 3 in
  let fp := WindowUpdateFrame 32767 in
  Build_Frame fh WindowUpdateType fp.
Obligation 1. reflexivity. Qed.

Fixpoint string_to_ascii_list s : list ascii :=
  match s with
  | EmptyString => nil%list
  | String a tl => a :: string_to_ascii_list tl
  end.

Definition string_to_N_list s := List.map N_of_ascii (string_to_ascii_list s).

Compute encodeFrame None f21.

Program Definition f4 : Frame :=
  let fh := Build_FrameHeader 6 (Bvect_false 8) 0 in
  let fp := SettingsFrame ((SettingMaxConcurrentStreams, 100) :: nil) in
  Build_Frame fh SettingsType fp.
Obligation 1. reflexivity. Qed.

Compute encodeFrame None f4.

Program Definition f13S : Frame :=
  let fh := Build_FrameHeader 12 (Bvect_false 8) 0 in
  let fp := SettingsFrame ((SettingHeaderTableSize, 0) ::
                           (SettingHeaderTableSize, 4096) :: nil) in
  Build_Frame fh SettingsType fp.
Obligation 1. reflexivity. Qed.

Compute encodeFrame None f13S.

Check fold_left.

Program Definition f13H : Frame :=
  let fh := Build_FrameHeader 39 [false; false; true; false; false; true; false; true] 3 in
  let p := Build_Priority false 1 15 in
  let hbf := fold_left (fun acc n => String (ascii_of_N n) acc)
                       (192 :: 130 :: 4 :: 154 :: 98 :: 67 :: 145 :: 138 :: 71
                            :: 85 :: 163 :: 161 :: 137 :: 211 :: 77 :: 12 :: 68
                            :: 132 :: 14138 :: 35 :: 4 :: 66 :: 24 :: 76 :: 229
                            :: 164 :: 171 :: 145 :: 8 :: 134 :: 191 :: 144
                            :: 190 :: nil) "" in
  let fp := HeadersFrame (Some p) hbf in
  Build_Frame fh HeadersType fp.
Obligation 1. reflexivity. Qed.

Compute encodeFrame None f13H.
