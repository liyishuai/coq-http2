From QuickChick Require Import QuickChick.
From HTTP2.src.HPACK Require Import HPACKTypes.
Require Import HTTP2.src.Types.
From Coq Require Import String Ascii BinNat Bvector List Basics.
Import ListNotations.

(** General type generation **)
Derive (GenSized, Shrink) for ascii.
Open Scope nat_scope.
Derive (GenSized, Shrink) for string.

Instance showHeaderField : Show HeaderField := showPair.

Instance showNat : Show N :=
  {|
    show n := show (N.to_nat n)
  |}.
Derive (GenSized, Shrink) for positive.
Derive (GenSized, Shrink) for N.
Derive (GenSized, Shrink, Show) for bool.

Fixpoint Bvector_of_list n (l:list bool) : Bvector n :=
  match n, l with
  | O, _ => Bnil
  | S n', h :: tl => Bcons h n' (Bvector_of_list n' tl)
  | S n', [] => Bcons false n' (Bvector_of_list n' [])
  end.

Instance genBvector n : Gen (Bvector n) :=
  {|
    arbitrary :=
      bindGen (arbitrarySized n) (compose returnGen (Bvector_of_list n))
  |}.

Fixpoint Bvector_to_string {n} (v:Bvector n) : string :=
  match v with
  | Vector.nil => ")"
  | Vector.cons h _ tl => show h ++ ", " ++ (Bvector_to_string tl)
  end.

Instance showBvector n : Show (Bvector n) :=
  {|
    show v := ("(" ++ Bvector_to_string v)%string
  |}.

Instance shrinkBvector n : Shrink (Bvector n) :=
  {| shrink _ := [] |}.

(** HPACK type generation **)
Instance genSizedHeaderField : GenSized HeaderField := genPairSized.
Instance shrinkHeaderField : Shrink HeaderField := shrinkPair.

Instance showTable : Show Table := showList.
Instance genSizedTable : GenSized Table := genListSized.
Instance shrinkTable : Shrink Table := shrinkList.

Instance showDTable : Show DTable := @showPair (N * N) Table _ showTable.
Instance genSizedDTable : GenSized DTable := genPairSized.
Instance shrinkDTable : Shrink DTable := shrinkPair.

Instance showHeaderList : Show HeaderList := showList.
Instance genSizedHeaderList : GenSized HeaderList := genListSized.
Instance shrinkHeaderList : Shrink HeaderList := shrinkList.

Derive (GenSized, Shrink, Show) for HeaderFieldRepresentation.

Instance showHeaderBlock : Show HeaderBlock := showList.
Instance genSizedHeaderBlock : GenSized HeaderBlock := genListSized.
Instance shrinkHeaderBlock : Shrink HeaderBlock := shrinkList.

(** Frame Type generation **)
Instance showStreamId : Show StreamId := showBvector 31.
Instance genStreamId : Gen StreamId := genBvector 31.
Instance shrinkStreamId : Shrink StreamId := shrinkBvector 31.

Instance showWeight : Show Weight := showBvector 8.
Instance genWeight : Gen Weight := genBvector 8.
Instance shrinkWeight : Shrink Weight := shrinkBvector 8.

Derive (Show, GenSized, Shrink) for Priority.

Instance showSettingValue : Show SettingValue := showBvector 32.
Instance genSettingValue : Gen SettingValue := genBvector 32.
Instance shrinkSettingValue : Shrink SettingValue := shrinkBvector 32.

Instance showSettingKey : Show SettingKey := showBvector 16.
Instance genSettingKey : Gen SettingKey := genBvector 16.
Instance shrinkSettingKey : Shrink SettingKey := shrinkBvector 16.

Instance showSettingKeyId : Show SettingKeyId := showNat.
Instance genSettingKeyId : Gen SettingKeyId. typeclasses eauto.
Instance shrinkSettingKeyId : Shrink SettingKeyId. typeclasses eauto.

Instance showSetting : Show Setting. typeclasses eauto.
Instance GenSetting : Gen Setting. typeclasses eauto.
Instance shrinkSetting : Shrink Setting. typeclasses eauto.

Instance showWindowSize : Show WindowSize := showBvector 31.
Instance genWindowSize : Gen WindowSize := genBvector 31.
Instance shrinkWindowSize : Shrink WindowSize := shrinkBvector 31.

Instance showErrorCode : Show ErrorCode := showBvector 32.
Instance genErrorCode : Gen ErrorCode := genBvector 32.
Instance shrinkErrorCode : Shrink ErrorCode := shrinkBvector 32.

Instance showPayloadLength : Show PayloadLength := showBvector 24.
Instance genPayloadLength : Gen PayloadLength := genBvector 24.
Instance shrinkPayloadLength : Shrink PayloadLength := shrinkBvector 24.

Instance showFrameFlagsField : Show FrameFlagsField := showBvector 8.
Instance genFrameFlagsField : Gen FrameFlagsField := genBvector 8.
Instance shrinkFrameFlagsField : Shrink FrameFlagsField := shrinkBvector 8.

Derive (GenSized, Show, Shrink) for FrameHeader.

Instance showFrameTypeId : Show FrameTypeId := showNat.
Instance genFrameTypeId : Gen FrameTypeId. typeclasses eauto.
Instance shrinkFrameTypeId : Shrink FrameTypeId. typeclasses eauto.

Derive (GenSized, Show, Shrink) for FrameType.