module

import MahjongHandHash
meta import MahjongHandHash
meta import MahjongDomain.Parts
import Mathlib.Util.AssertNoSorry

open MahjongDomain

assert_no_sorry MeldedHand.valid
assert_no_sorry MeldedHand.encode
assert_no_sorry MeldedHand.decode
assert_no_sorry TileCollection.encode
assert_no_sorry TileCollection.decode

example : TileCollection.decode (-1) = .error (.keyOutOfRange (-1)) := by
  rfl

/-- info: Except.ok 89285314363 -/
#guard_msgs in
#eval TileCollection.encode (TileCounts.ofList (Tile.all.take 13))

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
  ((TileCollection.encode counts).bind TileCollection.decode).map fun decoded =>
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
