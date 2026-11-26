module

public import MahjongDomain.Tile
public import MahjongDomain.Hand
public import MahjongDomain.Parts
public meta import MahjongDomain.Tile

@[expose] public section

namespace MahjongDomain

structure TileCountsKey where
  value : Int
  deriving DecidableEq, Repr

abbrev MeldedHandKey := Int

abbrev fixedKeyLimit : Int := 9223372036854775807

inductive TileCountsKeyError
  | invalidTotal (total : Nat)
  | invalidCount (tile : Tile) (count : Nat)
  | keyOutOfRange (key : Int)
  | roundTripFailure (key : Int)
  deriving DecidableEq, Repr

inductive MeldedHandKeyError
  | invalidHandTotal (handTotal : Nat)
  | invalidMeldCount (meldCount : Nat)
  | invalidHandCount (tile : Tile) (count : Nat)
  | invalidPhysicalCapacity (tile : Tile) (count : Nat)
  | keyOutOfRange (key : Int)
  | roundTripFailure (key : Int)
  deriving DecidableEq, Repr

inductive RelativeCaller
  | shimocha
  | toimen
  | kamicha
  deriving DecidableEq, Repr, BEq

namespace RelativeCaller

def index : RelativeCaller -> Nat
  | .shimocha => 0
  | .toimen => 1
  | .kamicha => 2

def ofIndex (value : Nat) : Option RelativeCaller :=
  match value with
  | 0 => some .shimocha
  | 1 => some .toimen
  | 2 => some .kamicha
  | _ => none

end RelativeCaller

/-- A fixed meld that retains called-tile and relative-caller information. -/
inductive FixedMeld
  | chi (suit : Suit) (start : Fin 7) (calledOffset : Fin 3)
  | pon (tile : Tile) (caller : RelativeCaller)
  | daiminkan (tile : Tile) (caller : RelativeCaller)
  | kakan (tile : Tile) (caller : RelativeCaller)
  | ankan (tile : Tile)
  deriving DecidableEq, Repr, BEq

/-- Counts retained by a fixed meld and hand in a melded-hand key input. -/
structure MeldedHand where
  hand : TileCounts
  fixedMelds : List FixedMeld

def TileCounts.expandedList (tiles : List Tile) : TileCounts :=
  TileCounts.ofList tiles

def FixedMeld.occupiedTiles : FixedMeld -> List Tile
  | .chi suit start _ =>
      [ Tile.suited suit (ShuntsuStart.firstRank start)
      , Tile.suited suit (ShuntsuStart.middleRank start)
      , Tile.suited suit (ShuntsuStart.lastRank start) ]
  | .pon tile _ => [tile, tile, tile]
  | .daiminkan tile _ => [tile, tile, tile, tile]
  | .kakan tile _ => [tile, tile, tile, tile]
  | .ankan tile => [tile, tile, tile, tile]

def FixedMeld.occupiedCounts (meld : FixedMeld) : TileCounts :=
  TileCounts.ofList meld.occupiedTiles

def FixedMeld.tiles : FixedMeld -> List Tile
  | .chi suit start _ =>
      [ Tile.suited suit (ShuntsuStart.firstRank start)
      , Tile.suited suit (ShuntsuStart.middleRank start)
      , Tile.suited suit (ShuntsuStart.lastRank start) ]
  | .pon tile _ => [tile, tile, tile]
  | .daiminkan tile _ => [tile, tile, tile, tile]
  | .kakan tile _ => [tile, tile, tile, tile]
  | .ankan tile => [tile, tile, tile, tile]

def FixedMeld.occupiedCountsCorrect (meld : FixedMeld) : TileCounts :=
  TileCounts.ofList meld.tiles

def countDigitsExactly (tiles : List Tile) (remaining : Nat) : Nat :=
  let variableCount := tiles.length
  if variableCount = 0 then
    if remaining = 0 then 1 else 0
  else
    let signedCount : Int :=
      (List.range 5).foldl
        (fun total j =>
          let shifted := j * 5
          if shifted ≤ remaining then
            let term : Int :=
              Int.ofNat (Nat.choose variableCount j *
                Nat.choose (remaining - shifted + variableCount - 1) (variableCount - 1))
            if j % 2 = 0 then total + term else total - term
          else total)
        0
    signedCount.natAbs

def vectorRank (counts : TileCounts) (total : Nat) : Nat :=
  let rec go (tiles : List Tile) (remaining : Nat) : Nat :=
    match tiles with
    | [] => 0
    | tile :: rest =>
        let digit := counts tile
        (List.range digit).foldl
          (fun total earlier =>
            total + if earlier ≤ remaining
              then countDigitsExactly rest (remaining - earlier)
              else 0)
          0
          + go rest (remaining - digit)
  go Tile.all total

def vectorDigitsUnrank (remaining rank : Nat) : List Nat :=
  let rec go (tiles : List Tile) (remaining rank : Nat) : (List Nat × Nat) :=
    match tiles with
    | [] => ([], rank)
    | _ :: rest =>
        let rec choose (digit rank : Nat) : Nat × Nat :=
          if digit ≥ 5 then (0, rank)
          else
            let block :=
              if digit ≤ remaining
                then countDigitsExactly rest (remaining - digit)
                else 0
            if rank < block then (digit, rank)
            else choose (digit + 1) (rank - block)
        termination_by 5 - digit
        decreasing_by omega
        let (digit, restRank) := choose 0 rank
        let (suffix, finalRank) :=
          go rest (remaining - digit) restRank
        (digit :: suffix, finalRank)
  (go Tile.all remaining rank).1

def countsFromDigits (digits : List Nat) : TileCounts :=
  TileCounts.ofList
    ((Tile.all.zip digits).flatMap fun pair =>
      List.replicate pair.2 pair.1)

def collectionOffset (total : Nat) : Nat :=
  ((List.range (total)).foldl
    (fun offset n =>
      if 13 ≤ n ∧ n < total then offset + countDigitsExactly Tile.all n
      else offset)
    0)

def collectionKeyMax : Nat :=
  ((List.range (19)).foldl
    (fun total n => total + if 13 ≤ n then countDigitsExactly Tile.all n else 0)
    0)

def collectionEncodeNat (counts : TileCounts) : Except TileCountsKeyError Nat := do
  let total := counts.total
  if ¬ counts.HasFullHandSize then
    .error (.invalidTotal total)
  else if ¬ counts.Valid then
    let tile := Tile.all.find? (fun tile => 4 < counts tile) |>.getD (.suited .man 0)
    .error (.invalidCount tile (counts tile))
  else
    pure (collectionOffset total + vectorRank counts total)

def collectionDecodeNat (key : Nat) :
    Except TileCountsKeyError (TileCounts × Nat) := do
  if key ≥ collectionKeyMax then
    .error (.keyOutOfRange (Int.ofNat key))
  else
    let rec find (totals : List Nat) (offset : Nat) :
        Except TileCountsKeyError (TileCounts × Nat) :=
      match totals with
      | [] => .error (.keyOutOfRange (Int.ofNat key))
      | total :: rest =>
          let count := countDigitsExactly Tile.all total
          if key < offset + count then
            pure (countsFromDigits (vectorDigitsUnrank total (key - offset)), total)
          else
            find rest (offset + count)
    find [13, 14, 15, 16, 17, 18] 0

def collectionDecodeUnchecked (key : Int) :
    Except TileCountsKeyError TileCounts := do
  if key < 0 then
    .error (.keyOutOfRange key)
  else
    let (counts, _) ← collectionDecodeNat key.toNat
    pure counts

def TileCounts.same (left right : TileCounts) : Bool :=
  Tile.all.all fun tile => left tile == right tile

def TileCountsKey.encode (counts : TileCounts) :
    Except TileCountsKeyError TileCountsKey := do
  let key ← collectionEncodeNat counts
  if key > fixedKeyLimit.toNat then
    .error (.keyOutOfRange (Int.ofNat key))
  else
    match collectionDecodeUnchecked (Int.ofNat key) with
    | .error _ => .error (.roundTripFailure (Int.ofNat key))
    | .ok decoded =>
        if TileCounts.same decoded counts then
          pure ⟨Int.ofNat key⟩
        else
          .error (.roundTripFailure (Int.ofNat key))

def TileCountsKey.decode (input : TileCountsKey) :
    Except TileCountsKeyError TileCounts := do
  let key := input.value
  if key < 0 ∨ key > fixedKeyLimit then
    .error (.keyOutOfRange key)
  else
    let decoded ← collectionDecodeUnchecked key
    match collectionEncodeNat decoded with
    | .error _ => .error (.roundTripFailure key)
    | .ok encoded =>
        if encoded = key.toNat then pure decoded
        else .error (.roundTripFailure key)

def binom (n k : Nat) : Nat :=
  Nat.choose n k

def fixedWays (first remaining : Nat) : Nat :=
  if remaining = 0 then 1
  else if first ≥ 403 then 0
  else binom (403 - first + remaining - 1) remaining

def fixedComboCount (meldCount : Nat) : Nat :=
  fixedWays 0 meldCount

def FixedMeld.index : FixedMeld -> Nat
  | .chi suit start offset =>
      let suitIndex :=
        match suit with
        | .man => 0
        | .pin => 1
        | .sou => 2
      suitIndex * 21 + start.val * 3 + offset.val
  | .pon tile caller => 63 + tile.index.val * 3 + caller.index
  | .daiminkan tile caller => 165 + tile.index.val * 3 + caller.index
  | .kakan tile caller => 267 + tile.index.val * 3 + caller.index
  | .ankan tile => 369 + tile.index.val

def tileFromIndex (value : Nat) : Option Tile :=
  Tile.all[value]?

def FixedMeld.ofIndex (value : Nat) : Option FixedMeld :=
  if value < 63 then
    let suitIndex := value / 21
    let remainder := value % 21
    let suit : Suit :=
      match suitIndex with
      | 0 => .man
      | 1 => .pin
      | _ => .sou
    let startValue := remainder / 3
    let offsetValue := remainder % 3
    if hstart : startValue < 7 then
      if hoffset : offsetValue < 3 then
        some (.chi suit ⟨startValue, hstart⟩ ⟨offsetValue, hoffset⟩)
      else none
    else none
  else if value < 165 then
    let offset := value - 63
    match tileFromIndex (offset / 3) with
    | none => none
    | some tile =>
        match RelativeCaller.ofIndex (offset % 3) with
        | none => none
        | some caller => some (.pon tile caller)
  else if value < 267 then
    let offset := value - 165
    match tileFromIndex (offset / 3) with
    | none => none
    | some tile =>
        match RelativeCaller.ofIndex (offset % 3) with
        | none => none
        | some caller => some (.daiminkan tile caller)
  else if value < 369 then
    let offset := value - 267
    match tileFromIndex (offset / 3) with
    | none => none
    | some tile =>
        match RelativeCaller.ofIndex (offset % 3) with
        | none => none
        | some caller => some (.kakan tile caller)
  else if value < 403 then
    (tileFromIndex (value - 369)).map .ankan
  else
    none

def insertFixedMeld (meld : FixedMeld) : List FixedMeld -> List FixedMeld
  | [] => [meld]
  | first :: rest =>
      if meld.index ≤ first.index then meld :: first :: rest
      else first :: insertFixedMeld meld rest

def sortFixedMelds (melds : List FixedMeld) : List FixedMeld :=
  melds.foldl (fun result meld => insertFixedMeld meld result) []

def fixedComboRankFrom (minimum remaining : Nat) :
    List Nat -> Nat
  | [] => 0
  | head :: rest =>
      (if head ≤ minimum then 0
       else
        (List.range (head - minimum)).foldl
          (fun total offset =>
            total + fixedWays (minimum + offset) (remaining - 1))
          0)
      + fixedComboRankFrom head (remaining - 1) rest

def fixedComboRank (indices : List Nat) : Nat :=
  fixedComboRankFrom 0 indices.length indices

def fixedComboUnrank (meldCount rank : Nat) : Option (List Nat) :=
  let rec go (minimum remaining rank : Nat) : Option (List Nat) :=
    if remaining = 0 then
      if rank = 0 then some [] else none
    else
      let rec choose (head rank : Nat) : Option (Nat × Nat) :=
        if head ≥ 403 then none
        else
          let block := fixedWays head (remaining - 1)
          if rank < block then some (head, rank)
          else choose (head + 1) (rank - block)
      match choose minimum rank with
      | none => none
      | some (head, restRank) =>
          (go head (remaining - 1) restRank).map (fun rest => head :: rest)
  go 0 meldCount rank

def MeldedHand.fixedMeldCount (input : MeldedHand) : Nat :=
  input.fixedMelds.length

def MeldedHand.fixedKeySegment (input : MeldedHand) : Except MeldedHandKeyError Nat := do
  let meldCount := input.fixedMeldCount
  if meldCount > 4 then
    .error (.invalidMeldCount meldCount)
  else
    let handTotal := input.hand.total
    let expected13 : Nat := 13 - 3 * meldCount
    let expected14 : Nat := 14 - 3 * meldCount
    if handTotal ≠ expected13 ∧ handTotal ≠ expected14 then
      .error (.invalidHandTotal handTotal)
    else
      pure handTotal

def MeldedHand.valid (input : MeldedHand) : Except MeldedHandKeyError Unit := do
  let meldCount := input.fixedMeldCount
  if meldCount > 4 then
    .error (.invalidMeldCount meldCount)
  else
    let handTotal := input.hand.total
    let expected13 : Nat := 13 - 3 * meldCount
    let expected14 : Nat := 14 - 3 * meldCount
    if handTotal ≠ expected13 ∧ handTotal ≠ expected14 then
      .error (.invalidHandTotal handTotal)
    else if ¬ input.hand.Valid then
      let tile := Tile.all.find? (fun tile => 4 < input.hand tile) |>.getD (.suited .man 0)
      .error (.invalidHandCount tile (input.hand tile))
    else
      let occupied : TileCounts :=
        fun tile => input.hand tile +
          input.fixedMelds.foldl
            (fun count meld => count + meld.occupiedCountsCorrect tile)
            0
      match Tile.all.find? (fun tile => 4 < occupied tile) with
      | some tile => .error (.invalidPhysicalCapacity tile (occupied tile))
      | none => pure ()

def meldKeyOffset (meldCount : Nat) (base14 : Bool) : Nat :=
  let previous :=
    (List.range meldCount).foldl
      (fun offset m =>
      let h13 := 13 - 3 * m
      let h14 := 14 - 3 * m
      offset + countDigitsExactly Tile.all h13 * fixedComboCount m +
        countDigitsExactly Tile.all h14 * fixedComboCount m)
      0
  if base14 then
    previous + countDigitsExactly Tile.all (13 - 3 * meldCount) * fixedComboCount meldCount
  else previous

def meldKeyMax : Nat :=
  (List.range 5).foldl
    (fun total m =>
      let f := fixedComboCount m
      total + countDigitsExactly Tile.all (13 - 3 * m) * f +
        countDigitsExactly Tile.all (14 - 3 * m) * f)
    0

def meldedHandEncodeNat (input : MeldedHand) :
    Except MeldedHandKeyError Nat := do
  _ ← input.valid
  let meldCount := input.fixedMeldCount
  let handTotal := input.hand.total
  let base14 := handTotal = 14 - 3 * meldCount
  let handRank := vectorRank input.hand handTotal
  let sorted := sortFixedMelds input.fixedMelds
  let fixedRank := fixedComboRank (sorted.map FixedMeld.index)
  let handCount := countDigitsExactly Tile.all handTotal
  let keyNat :=
    meldKeyOffset meldCount base14 +
      fixedRank * handCount + handRank
  pure keyNat

def meldedHandDecodeUnchecked (key : MeldedHandKey) :
    Except MeldedHandKeyError MeldedHand :=
  if key < 0 then
    .error (.keyOutOfRange key)
  else
    let keyNat := key.toNat
    if keyNat ≥ meldKeyMax then
      .error (.keyOutOfRange key)
    else
      let rec find (m : Nat) (offset : Nat) :
          Except MeldedHandKeyError MeldedHand :=
        if m ≥ 5 then
          .error (.keyOutOfRange key)
        else
          let f := fixedComboCount m
          let h13 := 13 - 3 * m
          let c13 := countDigitsExactly Tile.all h13
          let seg13 := c13 * f
          if keyNat < offset + seg13 then
            decodeSegment m h13 c13 f (keyNat - offset)
          else
            let h14 := 14 - 3 * m
            let c14 := countDigitsExactly Tile.all h14
            let seg14 := c14 * f
            if keyNat < offset + seg13 + seg14 then
              decodeSegment m h14 c14 f (keyNat - offset - seg13)
            else
              find (m + 1) (offset + seg13 + seg14)
      find 0 0
where
  decodeSegment (meldCount handTotal handCount fixedCount segmentRank : Nat) :
      Except MeldedHandKeyError MeldedHand := do
    let fixedRank := segmentRank / handCount
    let handRank := segmentRank % handCount
    if fixedRank ≥ fixedCount then
      .error (.keyOutOfRange key)
    else
      let digits := vectorDigitsUnrank handTotal handRank
      let hand := countsFromDigits digits
      match fixedComboUnrank meldCount fixedRank with
      | none => .error (.keyOutOfRange key)
      | some indices =>
          let meldOptions := indices.map FixedMeld.ofIndex
          if meldOptions.any Option.isNone then
            .error (.keyOutOfRange key)
          else
            let melds := meldOptions.filterMap id
            let input : MeldedHand := { hand := hand, fixedMelds := melds }
            _ ← input.valid
            pure input

def MeldedHand.same (left right : MeldedHand) : Bool :=
  TileCounts.same left.hand right.hand &&
    sortFixedMelds left.fixedMelds == sortFixedMelds right.fixedMelds

def MeldedHand.encode (input : MeldedHand) :
    Except MeldedHandKeyError MeldedHandKey := do
  let key ← meldedHandEncodeNat input
  if key > fixedKeyLimit.toNat then
    .error (.keyOutOfRange (Int.ofNat key))
  else
    match meldedHandDecodeUnchecked (Int.ofNat key) with
    | .error _ => .error (.roundTripFailure (Int.ofNat key))
    | .ok decoded =>
        if MeldedHand.same decoded input then
          pure (Int.ofNat key)
        else
          .error (.roundTripFailure (Int.ofNat key))

def MeldedHand.decode (key : MeldedHandKey) :
    Except MeldedHandKeyError MeldedHand := do
  if key < 0 ∨ key > fixedKeyLimit then
    .error (.keyOutOfRange key)
  else
    let decoded ← meldedHandDecodeUnchecked key
    match meldedHandEncodeNat decoded with
    | .error _ => .error (.roundTripFailure key)
    | .ok encoded =>
        if encoded = key.toNat then pure decoded
        else .error (.roundTripFailure key)

namespace TileCountsKey

def keyMax : Nat := collectionKeyMax

end TileCountsKey

namespace MeldedHand

def keyMax : Nat := meldKeyMax

end MeldedHand

example : TileCountsKey.decode ⟨-1⟩ = .error (.keyOutOfRange (-1)) := by
  rfl

end MahjongDomain
