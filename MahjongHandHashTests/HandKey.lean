module

import MahjongHandHash
meta import MahjongHandHash
meta import MahjongDomain.Parts
import Mathlib.Util.AssertNoSorry

open MahjongDomain

assert_no_sorry HandSnapshot.valid
assert_no_sorry MeldAwareHandKey.encode
assert_no_sorry MeldAwareHandKey.decode
assert_no_sorry TileCountsKey.encode
assert_no_sorry TileCountsKey.decode
assert_no_sorry countDigitsExactly_cons
assert_no_sorry countDigitsExactly_nil
assert_no_sorry countDigitsExactly_eq_digitVectors_length
assert_no_sorry digitVectors_mem
assert_no_sorry digitVectors_nodup
assert_no_sorry vectorRank_go_lt
assert_no_sorry vectorDigitsUnrank_go_rank
assert_no_sorry vectorRank_lt
assert_no_sorry vectorDigitsUnrank_rank
assert_no_sorry countsFromDigits_map
assert_no_sorry countsFromDigits_unrank_rank
assert_no_sorry vectorRank_unrank
assert_no_sorry TileCountsKey.keyMax_le_fixedKeyLimit
assert_no_sorry TileCountsKey.encode_valid
assert_no_sorry TileCountsKey.decode_encode_valid
assert_no_sorry TileCountsKey.encode_valid_injective
assert_no_sorry TileCountsKey.decode_success
assert_no_sorry TileCountsKey.encode_surjective
assert_no_sorry TileCountsKey.decode_outside
assert_no_sorry TileCountsKey.decode_success_iff
assert_no_sorry TileCountsKey.decode_valid
assert_no_sorry TileCountsKey.encode_range
assert_no_sorry TileCountsKey.decode_encode
assert_no_sorry TileCountsKey.encode_decode
assert_no_sorry TileCountsKey.encode_injective_on_success

example : TileCountsKey.decode ⟨-1⟩ = .error (.keyOutOfRange (-1)) := by
  rfl

example :
    TileCountsKey.keyMax ≤ fixedKeyLimit.toNat ∧
      MeldAwareHandKey.keyMax ≤ fixedKeyLimit.toNat := by
  native_decide

example :
    TileCountsKey.decode ⟨fixedKeyLimit + 1⟩ =
      .error (.keyOutOfRange (fixedKeyLimit + 1)) := by
  rfl

example :
    MeldAwareHandKey.decode ⟨fixedKeyLimit + 1⟩ =
      .error (.keyOutOfRange (fixedKeyLimit + 1)) := by
  rfl

example :
    (TileCountsKey.decode ⟨0⟩ |>.bind TileCountsKey.encode) = .ok ⟨0⟩ ∧
      (TileCountsKey.decode ⟨Int.ofNat (TileCountsKey.keyMax - 1)⟩ |>.bind
        TileCountsKey.encode) = .ok ⟨Int.ofNat (TileCountsKey.keyMax - 1)⟩ := by
  native_decide

example :
    ([14, 15, 16, 17, 18].all fun total =>
      let offset := collectionOffset total
      match TileCountsKey.decode ⟨Int.ofNat (offset - 1)⟩,
          TileCountsKey.decode ⟨Int.ofNat offset⟩ with
      | .ok previous, .ok next => previous.total == total - 1 && next.total == total
      | _, _ => false) = true := by
  native_decide

example :
    (match TileCountsKey.decode ⟨Int.ofNat TileCountsKey.keyMax⟩ with
    | .error (.keyOutOfRange _) => true
    | _ => false) = true := by
  native_decide

example :
    (match TileCountsKey.encode (TileCounts.ofList (Tile.all.take 12)) with
    | .error (.invalidTotal 12) => true
    | _ => false) = true ∧
    (match TileCountsKey.encode (TileCounts.ofList (Tile.all.take 19)) with
    | .error (.invalidTotal 19) => true
    | _ => false) = true := by
  native_decide

example :
    (match TileCountsKey.encode (TileCounts.ofList
      (List.replicate 5 (.suited .man 0) ++ (Tile.all.drop 1).take 8)) with
    | .error (.invalidCount _ 5) => true
    | _ => false) = true := by
  native_decide

example :
    (match TileCountsKey.encode (TileCounts.ofList
      (List.replicate 4 (.suited .man 0) ++ (Tile.all.drop 1).take 14)) with
    | .ok key =>
        match TileCountsKey.decode key with
        | .ok counts => counts (.suited .man 0) == 4 && counts.total == 18
        | .error _ => false
    | .error _ => false) = true := by
  native_decide

def collisionRegressionHand : TileCounts :=
  TileCounts.ofList
    [ Tile.suited .man ⟨3, by decide⟩
    , Tile.suited .man ⟨4, by decide⟩
    , Tile.suited .man ⟨5, by decide⟩
    , Tile.suited .man ⟨6, by decide⟩
    , Tile.suited .man ⟨7, by decide⟩
    , Tile.suited .man ⟨8, by decide⟩
    , Tile.suited .pin ⟨0, by decide⟩
    ]

def chi123 (calledOffset : Fin 3) : FixedMeld :=
  .chi ⟨.man, ⟨0, by decide⟩⟩ calledOffset

def repeatedChiInput : HandSnapshot :=
  { standing := collisionRegressionHand
    fixedMelds := [chi123 ⟨1, by decide⟩, chi123 ⟨1, by decide⟩] }

def chiAndAnkanInput : HandSnapshot :=
  { standing := collisionRegressionHand
    fixedMelds :=
      [ chi123 ⟨0, by decide⟩
      , .ankan (.honor Honor.red) ] }

example :
    (match MeldAwareHandKey.encode repeatedChiInput, MeldAwareHandKey.encode chiAndAnkanInput with
    | .ok repeatedChiKey, .ok chiAndAnkanKey => repeatedChiKey != chiAndAnkanKey
    | _, _ => false) = true := by
  native_decide

example :
    ((MeldAwareHandKey.encode repeatedChiInput).bind MeldAwareHandKey.decode).map
      (fun decoded =>
        Tile.all.all (fun tile => decoded.standing tile == repeatedChiInput.standing tile) &&
          decoded.fixedMelds == sortFixedMelds repeatedChiInput.fixedMelds) =
      .ok true := by
  native_decide

example :
    ((List.range 403).all fun index =>
      match FixedMeld.ofIndex index with
      | some meld => meld.index == index
      | none => false) = true := by
  native_decide

def roundTrips (input : HandSnapshot) : Bool :=
  match MeldAwareHandKey.encode input with
  | .error _ => false
  | .ok key =>
      match MeldAwareHandKey.decode key with
      | .error _ => false
      | .ok decoded =>
          HandSnapshot.same input decoded &&
            match MeldAwareHandKey.encode decoded with
            | .ok encoded => encoded == key
            | .error _ => false

def oneMeldStanding : TileCounts := TileCounts.ofList (Tile.all.take 10)

example :
    ((List.range 403).all fun index =>
      match FixedMeld.ofIndex index with
      | none => false
      | some meld =>
          let standing := TileCounts.ofList
            ((Tile.all.filter fun tile => meld.occupiedCounts tile == 0).take 10)
          roundTrips { standing := standing, fixedMelds := [meld] }) = true := by
  native_decide

def meldVariants : List FixedMeld :=
  [ chi123 ⟨0, by decide⟩, chi123 ⟨2, by decide⟩
  , .pon (.honor Honor.east) .shimocha, .pon (.honor Honor.east) .kamicha
  , .daiminkan (.honor Honor.east) .toimen
  , .kakan (.honor Honor.east) .toimen
  , .ankan (.honor Honor.east) ]

example :
    (meldVariants.all fun meld =>
      roundTrips { standing := oneMeldStanding, fixedMelds := [meld] }) = true := by
  native_decide

example :
    (match meldVariants.mapM (fun meld =>
      MeldAwareHandKey.encode { standing := oneMeldStanding, fixedMelds := [meld] }) with
    | .ok keys => keys.eraseDups.length == meldVariants.length
    | .error _ => false) = true := by
  native_decide

example :
    (let a : HandSnapshot := chiAndAnkanInput
     let b : HandSnapshot := { a with fixedMelds := a.fixedMelds.reverse }
     match MeldAwareHandKey.encode a, MeldAwareHandKey.encode b with
     | .ok left, .ok right => left == right && roundTrips b
     | _, _ => false) = true := by
  native_decide

example :
    (let a : HandSnapshot :=
      { standing := oneMeldStanding, fixedMelds := [.daiminkan (.honor Honor.east) .toimen] }
     let b : HandSnapshot :=
      { standing := oneMeldStanding, fixedMelds := [.kakan (.honor Honor.east) .toimen] }
     match TileCountsKey.encode a.occupiedCounts, TileCountsKey.encode b.occupiedCounts,
         MeldAwareHandKey.encode a, MeldAwareHandKey.encode b with
     | .ok countsA, .ok countsB, .ok meldA, .ok meldB =>
         countsA == countsB && meldA != meldB
     | _, _, _, _ => false) = true := by
  native_decide

def fourKans : List FixedMeld :=
  [ .ankan (.honor Honor.south), .ankan (.honor Honor.west)
  , .ankan (.honor Honor.north), .ankan (.honor Honor.red) ]

example :
    (roundTrips { standing := TileCounts.ofList (Tile.all.take 13), fixedMelds := [] } &&
     roundTrips { standing := TileCounts.ofList (Tile.all.take 14), fixedMelds := [] } &&
     roundTrips { standing := TileCounts.ofList [.honor Honor.east], fixedMelds := fourKans } &&
     roundTrips { standing := TileCounts.ofList [.honor Honor.east, .honor Honor.east]
                  fixedMelds := fourKans }) = true := by
  native_decide

example :
    (let input : HandSnapshot :=
      { standing := TileCounts.ofList
          (List.replicate 4 (.suited .man 0) ++ (Tile.all.drop 3).take 6)
        fixedMelds := [chi123 ⟨0, by decide⟩] }
     match MeldAwareHandKey.encode input with
     | .error (.invalidPhysicalCapacity tile 5) => tile == .suited .man 0
     | _ => false) = true := by
  native_decide

example :
    (match MeldAwareHandKey.encode
      { standing := TileCounts.ofList (Tile.all.take 12), fixedMelds := [] } with
    | .error (.invalidHandTotal 12) => true
    | _ => false) = true ∧
    (match MeldAwareHandKey.encode
      { standing := TileCounts.ofList [.honor Honor.east]
        fixedMelds := fourKans ++ [.ankan (.honor Honor.white)] } with
    | .error (.invalidMeldCount 5) => true
    | _ => false) = true ∧
    (match MeldAwareHandKey.decode ⟨-1⟩ with
    | .error (.keyOutOfRange (-1)) => true
    | _ => false) = true := by
  native_decide

example :
    (let hand := TileCounts.ofList
      (List.replicate 4 (.suited .man 0) ++ (Tile.all.drop 3).take 6)
     let meld := chi123 ⟨0, by decide⟩
     let key := meldKeyOffset 1 false +
       fixedComboRank [meld.index] * countDigitsExactly Tile.all 10 + vectorRank hand 10
     match MeldAwareHandKey.decode ⟨Int.ofNat key⟩ with
     | .error (.invalidPhysicalCapacity tile 5) => tile == .suited .man 0
     | _ => false) = true := by
  native_decide

/-- info: Except.ok 89285314363 -/
#guard_msgs in
#eval (TileCountsKey.encode (TileCounts.ofList (Tile.all.take 13))).map TileCountsKey.value

/-- info: Except.ok 425821417872 -/
#guard_msgs in
#eval
  let hand := TileCounts.ofList (Tile.all.drop 3 |>.take 10)
  let meld := FixedMeld.chi ⟨.man, ⟨0, by decide⟩⟩ ⟨0, by decide⟩
  (MeldAwareHandKey.encode { standing := hand, fixedMelds := [meld] }).map MeldAwareHandKey.value

/-- info: Except.ok true -/
#guard_msgs in
#eval
  let counts := TileCounts.ofList (Tile.all.take 13)
  ((TileCountsKey.encode counts).bind TileCountsKey.decode).map fun decoded =>
    Tile.all.all fun tile => decoded tile == counts tile

/-- info: Except.ok (true, true) -/
#guard_msgs in
#eval
  let hand := TileCounts.ofList (Tile.all.drop 3 |>.take 10)
  let meld := FixedMeld.chi ⟨.man, ⟨0, by decide⟩⟩ ⟨0, by decide⟩
  let input : HandSnapshot := { standing := hand, fixedMelds := [meld] }
  ((MeldAwareHandKey.encode input).bind MeldAwareHandKey.decode).map fun decoded =>
    (Tile.all.all (fun tile => decoded.standing tile == hand tile),
     decoded.fixedMelds == [meld])
