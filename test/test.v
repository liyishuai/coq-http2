From HTTP2.HPACK Require Import HPACKDecode HPACKEncode HPACKTypes.
From HTTP2 Require Import
     Encode
     Equiv
     Types
     Util.BitVector
     Util.BitField
     Util.ByteVector
     Util.Parser
     Util.ParserInstances
     Util.VectorUtil
     Util.StringUtil. 
From Coq Require Import Peano List BinNat String Ascii NArith Basics Bvector.
From ExtLib Require Import Monads.
Import MonadNotation.
Import ListNotations.
Open Scope list_scope.
Open Scope monad_scope.

(** Hex interpretation for unit testing **)

(* Binary numbers. Most operations assume little-endianness,
   but this can also be used as a big-endian representation. *)
Inductive binary : Type :=
| b0 : binary -> binary
| b1 : binary -> binary
| b_ : binary (* End *)
.

Fixpoint zeroes (d : nat) : binary :=
  match d with
  | O => b_
  | S d => b0 (zeroes d)
  end.

Fixpoint rev' (y z : binary) : binary :=
  match z with
  | b0 z => rev' (b0 y) z
  | b1 z => rev' (b1 y) z
  | b_ => y
  end.

(* big-endian <-> little-endian *)
(* Eta-expand because this somehow ends up in the extracted
   code and we need to not evaluate it. *)
Definition rev (z : binary) : binary := rev' b_ z.

Notation bit := bool.
Notation zero := false.
Notation one := true.

Definition of_bit (a : bool) : binary -> binary :=
  match a with
  | false => b0
  | true => b1
  end.

Fixpoint hex' (acc : binary) (s : string) : binary :=
  match s with
  | EmptyString => acc
  | String x s =>
    let acc :=
        match x with
        (* Digit *)
        | Ascii a0 a1 a2 a3 _ _ false _ =>
          of_bit a0 (of_bit a1 (of_bit a2 (of_bit a3 acc)))
        | "a" => b0 (b1 (b0 (b1 acc)))
        | "b" => b1 (b1 (b0 (b1 acc)))
        | "c" => b0 (b0 (b1 (b1 acc)))
        | "d" => b1 (b0 (b1 (b1 acc)))
        | "e" => b0 (b1 (b1 (b1 acc)))
        | "f" => b1 (b1 (b1 (b1 acc)))
        | _ => b0 (b0 (b0 (b0 acc)))
        end%char in
    hex' acc s
  end.

Definition hex : string -> binary := hex' b_.

Fixpoint positive_to_binary (d : nat) (n : positive) : binary :=
  match n, d with
  | xI n, S d => b1 (positive_to_binary d n)
  | xO n, S d => b0 (positive_to_binary d n)
  | xH,   S d => b1 (zeroes d)
  | _, O => b_
  end.

Definition N_to_binary (d : nat) (n : N) : binary :=
  match n with
  | N0 => zeroes d
  | Npos n => positive_to_binary d n
  end.

Fixpoint binary_to_N (z : binary) :=
  match z with
  | b_ => 0%N
  | b1 z => N.succ_double (binary_to_N z)
  | b0 z => N.double (binary_to_N z)
  end.

(* Turn a string into a list of binary bytes *)
Fixpoint string_to_binary (s:string) : list binary :=
  match s with
  | EmptyString => []
  | String a s' =>
    (N_to_binary 8) (N_of_ascii a) :: string_to_binary s'
  end.

Fixpoint hex_bytes_to_binary (s:list string) : list binary := map hex s.
Fixpoint hex_bytes_to_string (s:list string) : string :=
  fold_right String EmptyString (map (ascii_of_N ∘ binary_to_N ∘ hex) s).

(** Hpack testing **)
(* https://tools.ietf.org/html/rfc7541#appendix-C.1.1 *)
(* The value 10 is to be encoded with a 5-bit prefix *)
Example C1_1 : (encode_N 10 5) = [false; true; false; true; false].
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.1.2 *)
(* The value I=1337 is to be encoded with a 5-bit prefix. *)
Example C1_2 : (encode_N 1337 5) = [true; true; true; true; true; true;
                                      false; false; true; true; false;
                                        true; false; false; false; false;
                                          false; true; false; true; false].
Proof. simpl. repeat (rewrite encode_N_help_rec_equation; simpl).
       reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.1.3 *)
(* The value 42 is to be encoded starting at an octet boundary.  This
   implies that a 8-bit prefix is used. *)
Example C1_3 : (encode_N 42 8) = [false; false; true; false; true;
                                    false; true; false].
Proof. reflexivity. Qed.


(* Https://tools.ietf.org/html/rfc7541#appendix-C.2.1 *)
(* Header list to encode:

   custom-key: custom-header *)
Example C2_1_encode :
  hex_bytes_to_binary ["40"; "0a"; "63"; "75"; "73"; "74"; "6f"; "6d";
                         "2d"; "6b"; "65"; "79"; "0d"; "63"; "75"; "73";
                           "74"; "6f"; "6d"; "2d"; "68"; "65"; "61";
                             "64"; "65"; "72"] =
  string_to_binary (pack_list_bool (encode_HFR false
                             (LHFIncrementNewName "custom-key"
                                                  "custom-header"))).
Proof. reflexivity. Qed.

Definition decode (s:string) :=
  StateMonad.runStateT (run_HPACK_parser decode_HFR) s.

Definition decode_mult (s:string) :=
  StateMonad.runStateT (run_HPACK_parser decode_HB) s.

Example C2_1_decode :
  decode (hex_bytes_to_string ["40"; "0a"; "63"; "75"; "73"; "74";
                                       "6f"; "6d"; "2d"; "6b"; "65"; "79";
                                         "0d"; "63"; "75"; "73"; "74"; "6f";
                                           "6d"; "2d"; "68"; "65"; "61";"64";
                                             "65"; "72"])
  = inr (LHFIncrementNewName "custom-key" "custom-header", "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.2.2 *)
(* 
  Header list to encode:

   :path: /sample/path
 *)
Example C2_2_encode :
  hex_bytes_to_binary ["04"; "0c"; "2f"; "73"; "61"; "6d"; "70"; "6c";
                         "65"; "2f"; "70"; "61"; "74"; "68"] =
  string_to_binary (pack_list_bool (encode_HFR false
                             (LHFWithoutIndexIndexedName 4
                                                  "/sample/path"))).
Proof. reflexivity. Qed.

Example C2_2_decode :
  decode (hex_bytes_to_string ["04"; "0c"; "2f"; "73"; "61"; "6d"; "70"; "6c";
                                 "65"; "2f"; "70"; "61"; "74"; "68"])
  = inr (LHFWithoutIndexIndexedName 4 "/sample/path", "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.2.3 *)
(* 
   Header list to encode:

   password: secret
 *)
Example C2_3_encode :
  hex_bytes_to_binary ["10"; "08"; "70"; "61"; "73"; "73"; "77";
                         "6f"; "72"; "64"; "06"; "73"; "65"; "63";
                           "72"; "65"; "74"] =
  string_to_binary (pack_list_bool (encode_HFR false
                             (LHFNeverIndexNewName "password"
                                                  "secret"))).
Proof. reflexivity. Qed.

Example C2_3_decode :
  decode (hex_bytes_to_string ["10"; "08"; "70"; "61"; "73"; "73"; "77";
                         "6f"; "72"; "64"; "06"; "73"; "65"; "63";
                           "72"; "65"; "74"])
  = inr (LHFNeverIndexNewName "password" "secret", "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.2.4 *)
(* Header list to encode:

   :method: GET *)
Example C2_4_encode :
  hex_bytes_to_binary ["82"] =
  string_to_binary (pack_list_bool (encode_HFR false
                             (IndexedHF 2))).
Proof. reflexivity. Qed.

Example C2_4_decode :
  decode (hex_bytes_to_string ["82"])
  = inr (IndexedHF 2, "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.3.1 *)
(* Header list to encode:

   :method: GET
   :scheme: http
   :path: /
   :authority: www.example.com*)
Example C3_1_encode :
  hex_bytes_to_binary ["82"; "86"; "84"; "41"; "0f"; "77"; "77"; "77";
                         "2e"; "65"; "78"; "61"; "6d"; "70"; "6c"; "65";
                           "2e"; "63"; "6f"; "6d"] =
  fold_left (fun acc b => acc ++ (string_to_binary b))
            (encode_HB false [IndexedHF 2; IndexedHF 6; IndexedHF 4;
               LHFIncrementIndexedName 1 "www.example.com"]) [].
Proof. reflexivity. Qed.

Example C3_1_decode :
  decode_mult (hex_bytes_to_string ["82"; "86"; "84"; "41"; "0f"; "77"; "77"; "77";
                         "2e"; "65"; "78"; "61"; "6d"; "70"; "6c"; "65";
                           "2e"; "63"; "6f"; "6d"]) =
  inr ([IndexedHF 2; IndexedHF 6; IndexedHF 4;
          LHFIncrementIndexedName 1 "www.example.com"], "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.3.2 *)
(* Header list to encode:

   :method: GET
   :scheme: http
   :path: /
   :authority: www.example.com
   cache-control: no-cache*)
Example C3_2_encode :
  hex_bytes_to_binary ["82"; "86"; "84"; "be"; "58"; "08"; "6e"; "6f"; "2d";
                         "63"; "61"; "63"; "68"; "65"] =
  fold_left (fun acc b => acc ++ (string_to_binary b))
            (encode_HB false [IndexedHF 2; IndexedHF 6; IndexedHF 4;
               IndexedHF 62; LHFIncrementIndexedName 24 "no-cache"]) [].
Proof. reflexivity. Qed.

Example C3_2_decode :
  decode_mult (hex_bytes_to_string ["82"; "86"; "84"; "be"; "58"; "08"; "6e";
                                      "6f"; "2d"; "63"; "61"; "63"; "68";
                                        "65"]) =
  inr ([IndexedHF 2; IndexedHF 6; IndexedHF 4;
               IndexedHF 62; LHFIncrementIndexedName 24 "no-cache"], "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.3.3 *)
(* Header list to encode:

   :method: GET
   :scheme: https
   :path: /index.html
   :authority: www.example.com
   custom-key: custom-value*)
Example C3_3_encode :
  hex_bytes_to_binary ["82"; "87"; "85"; "bf"; "40"; "0a"; "63"; "75"; "73";
                         "74"; "6f"; "6d"; "2d"; "6b"; "65"; "79"; "0c"; "63";
                           "75"; "73"; "74"; "6f"; "6d"; "2d"; "76"; "61";
                             "6c"; "75"; "65"] =
  fold_left (fun acc b => acc ++ (string_to_binary b))
            (encode_HB false [IndexedHF 2; IndexedHF 7; IndexedHF 5;
               IndexedHF 63; LHFIncrementNewName "custom-key" "custom-value"]) [].
Proof. reflexivity. Qed.

Example C3_3_decode :
  decode_mult (hex_bytes_to_string ["82"; "87"; "85"; "bf"; "40"; "0a"; "63";
                                      "75"; "73"; "74"; "6f"; "6d"; "2d"; "6b";
                                        "65"; "79"; "0c"; "63"; "75"; "73";
                                          "74"; "6f"; "6d"; "2d"; "76"; "61";
                                            "6c"; "75"; "65"]) =
  inr ([IndexedHF 2; IndexedHF 7; IndexedHF 5;
               IndexedHF 63; LHFIncrementNewName "custom-key" "custom-value"], "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.4.1 *)
(* Header list to encode:

   :method: GET
   :scheme: http
   :path: /
   :authority: www.example.com*)
Example C4_1_encode :
  hex_bytes_to_binary ["82"; "86"; "84"; "41"; "8c"; "f1"; "e3"; "c2"; "e5";
                         "f2"; "3a"; "6b"; "a0"; "ab"; "90"; "f4"; "ff"] =
  fold_left (fun acc b => acc ++ (string_to_binary b))
            (encode_HB true [IndexedHF 2; IndexedHF 6; IndexedHF 4;
               LHFIncrementIndexedName 1 "www.example.com"]) [].
Proof. reflexivity. Qed.

Example C4_1_decode :
  decode_mult (hex_bytes_to_string ["82"; "86"; "84"; "41"; "8c"; "f1"; "e3";
                                      "c2"; "e5"; "f2"; "3a"; "6b"; "a0";
                                        "ab"; "90"; "f4"; "ff"]) =
  inr ([IndexedHF 2; IndexedHF 6; IndexedHF 4;
               LHFIncrementIndexedName 1 "www.example.com"], "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.4.2 *)
(* Header list to encode:

   :method: GET
   :scheme: http
   :path: /
   :authority: www.example.com
   cache-control: no-cache*)
Example C4_2_encode :
  hex_bytes_to_binary ["82"; "86"; "84"; "be"; "58"; "86"; "a8";
                         "eb"; "10"; "64"; "9c"; "bf"] =
  fold_left (fun acc b => acc ++ (string_to_binary b))
            (encode_HB true [IndexedHF 2; IndexedHF 6; IndexedHF 4;
               IndexedHF 62; LHFIncrementIndexedName 24 "no-cache"]) [].
Proof. reflexivity. Qed.

Example C4_2_decode :
  decode_mult (hex_bytes_to_string ["82"; "86"; "84"; "be"; "58"; "86";
                                      "a8"; "eb"; "10"; "64"; "9c";
                                        "bf"]) =
  inr ([IndexedHF 2; IndexedHF 6; IndexedHF 4;
               IndexedHF 62; LHFIncrementIndexedName 24 "no-cache"], "").
Proof. reflexivity. Qed.

(* https://tools.ietf.org/html/rfc7541#appendix-C.4.3*)
(* Header list to encode:

   :method: GET
   :scheme: https
   :path: /index.html
   :authority: www.example.com
   custom-key: custom-value*)
Example C4_3_encode :
  hex_bytes_to_binary ["82"; "87"; "85"; "bf"; "40"; "88"; "25"; "a8";
                        "49"; "e9"; "5b"; "a9"; "7d"; "7f"; "89"; "25"; 
                         "a8"; "49"; "e9"; "5b"; "b8"; "e8"; "b4"; "bf"] =
  fold_left (fun acc b => acc ++ (string_to_binary b))
            (encode_HB true [IndexedHF 2; IndexedHF 7; IndexedHF 5;
               IndexedHF 63; LHFIncrementNewName "custom-key" "custom-value"]) [].
Proof. reflexivity. Qed.

Example C4_3_decode :
  decode_mult (hex_bytes_to_string ["82"; "87"; "85"; "bf"; "40"; "88"; "25"; "a8";
                        "49"; "e9"; "5b"; "a9"; "7d"; "7f"; "89"; "25"; 
                         "a8"; "49"; "e9"; "5b"; "b8"; "e8"; "b4"; "bf"]) =
  inr ([IndexedHF 2; IndexedHF 7; IndexedHF 5;
               IndexedHF 63; LHFIncrementNewName "custom-key" "custom-value"], "").
Proof. reflexivity. Qed.

(** Frame testing **)
(* Http2 sample dump:
   https://wiki.wireshark.org/HTTP2 *)

Print WindowSize.

Program Definition f21 : Frame :=
  let fh := Build_FrameHeader (N2Bv_gen 24 4) (Bvect_false 8) (N2Bv_gen 31 3) in
  let fp := WindowUpdateFrame (N2Bv_gen 31 32767) in
  Build_Frame fh WindowUpdateType fp.

Fixpoint string_to_ascii_list s : list ascii :=
  match s with
  | EmptyString => nil%list
  | String a tl => a :: string_to_ascii_list tl
  end.

Definition string_to_N_list s := List.map N_of_ascii (string_to_ascii_list s).

Example encode_f21 :
  string_to_binary (encodeFrame None f21) =
  hex_bytes_to_binary ["00"; "00"; "04"; "08"; "00"; "00"; "00"; "00"; "03"; "00";
                         "00"; "7f"; "ff"].
Proof.  
  
Program Definition f4 : Frame :=
  let fh := Build_FrameHeader 6 (Bvect_false 8) (N2Bv_gen 31 0) in
  let fp := SettingsFrame ((SettingMaxConcurrentStreams, (N2Bv_gen 32 100)) :: nil) in
  Build_Frame fh SettingsType fp.
Obligation 1. reflexivity. Qed.

Compute encodeFrame None f4.
(* "           d" *)

Program Definition f13S : Frame :=
  let fh := Build_FrameHeader 12 (Bvect_false 8) 0 in
  let fp := SettingsFrame ((SettingHeaderTableSize, 0) ::
                           (SettingHeaderTableSize, 4096) :: nil) in
  Build_Frame fh SettingsType fp.
Obligation 1. reflexivity. Qed.

Compute encodeFrame None f13S.
(* "                " *)

Program Definition f13H : Frame :=
  let fh := Build_FrameHeader 39 [true; false; true; false; false; true; false; false] 3 in
  let p := Build_Priority false 1 15 in
  let hbf := fold_left (fun acc n => String (ascii_of_N n) acc)
                       (192 :: 130 :: 4 :: 154 :: 98 :: 67 :: 145 :: 138 :: 71
                            :: 85 :: 163 :: 161 :: 137 :: 211 :: 77 :: 12 :: 68
                            :: 132 :: 141 :: 38 :: 35 :: 4 :: 66 :: 24 :: 76 :: 229
                            :: 164 :: 171 :: 145 :: 8 :: 134 :: 191 :: 144
                            :: 190 :: nil) "" in
  let fp := HeadersFrame (Some p) hbf in
  Build_Frame fh HeadersType fp.
Obligation 1. reflexivity. Qed.

Compute encodeFrame None f13H.
(* String "000"
         (String "000"
            (String "'"
               (String "001"
                  (String "%"
                     (String "000"
                        (String "000"
                           (String "000"
                              (String "003"
                                 (String "000"
                                    (String "000"
                                       (String "000"
                                          (String "001"
                                          (String "015"
                                          (String "190"
                                          (String "144"
                                          (String "191"
                                          (String "134"
                                          (String "008"
                                          (String "145"
                                          (String "171"
                                          (String "164"
                                          (String "229"
                                          (String "L" ...))))))))))))))))))))))) *)