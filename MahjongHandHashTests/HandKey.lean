module

import MahjongHandHash
meta import MahjongHandHash
meta import MahjongDomain.Parts
import Mathlib.Util.AssertNoSorry

open MahjongDomain

assert_no_sorry MeldedHand.valid
assert_no_sorry MeldedHand.encode
assert_no_sorry MeldedHand.decode
assert_no_sorry TileCountsKey.encode
assert_no_sorry TileCountsKey.decode

example : TileCountsKey.decode ⟨-1⟩ = .error (.keyOutOfRange (-1)) := by
  rfl

example :
    TileCountsKey.keyMax ≤ fixedKeyLimit.toNat ∧
      MeldedHand.keyMax ≤ fixedKeyLimit.toNat := by
  native_decide

example :
    TileCountsKey.decode ⟨fixedKeyLimit + 1⟩ =
      .error (.keyOutOfRange (fixedKeyLimit + 1)) := by
  rfl

example :
    MeldedHand.decode (fixedKeyLimit + 1) =
      .error (.keyOutOfRange (fixedKeyLimit + 1)) := by
  rfl

example :
    (TileCountsKey.decode ⟨0⟩ |>.bind TileCountsKey.encode) = .ok ⟨0⟩ ∧
      (TileCountsKey.decode ⟨Int.ofNat (TileCountsKey.keyMax - 1)⟩ |>.bind
        TileCountsKey.encode) = .ok ⟨Int.ofNat (TileCountsKey.keyMax - 1)⟩ := by
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
  .chi .man ⟨0, by decide⟩ calledOffset

def repeatedChiInput : MeldedHand :=
  { hand := collisionRegressionHand
    fixedMelds := [chi123 ⟨1, by decide⟩, chi123 ⟨1, by decide⟩] }

def chiAndAnkanInput : MeldedHand :=
  { hand := collisionRegressionHand
    fixedMelds :=
      [ chi123 ⟨0, by decide⟩
      , .ankan (.honor Honor.red) ] }

example :
    (match MeldedHand.encode repeatedChiInput, MeldedHand.encode chiAndAnkanInput with
    | .ok repeatedChiKey, .ok chiAndAnkanKey => repeatedChiKey != chiAndAnkanKey
    | _, _ => false) = true := by
  native_decide

example :
    ((MeldedHand.encode repeatedChiInput).bind MeldedHand.decode).map
      (fun decoded =>
        Tile.all.all (fun tile => decoded.hand tile == repeatedChiInput.hand tile) &&
          decoded.fixedMelds == sortFixedMelds repeatedChiInput.fixedMelds) =
      .ok true := by
  native_decide

/-- info: Except.ok 89285314363 -/
#guard_msgs in
#eval (TileCountsKey.encode (TileCounts.ofList (Tile.all.take 13))).map TileCountsKey.value

/-- info: Except.ok 425821417872 -/
#guard_msgs in
#eval
  let hand := TileCounts.ofList (Tile.all.drop 3 |>.take 10)
  let meld := FixedMeld.chi .man ⟨0, by decide⟩ ⟨0, by decide⟩
  MeldedHand.encode { hand := hand, fixedMelds := [meld] }

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
  let meld := FixedMeld.chi .man ⟨0, by decide⟩ ⟨0, by decide⟩
  let input : MeldedHand := { hand := hand, fixedMelds := [meld] }
  ((MeldedHand.encode input).bind MeldedHand.decode).map fun decoded =>
    (Tile.all.all (fun tile => decoded.hand tile == hand tile),
     decoded.fixedMelds == [meld])
