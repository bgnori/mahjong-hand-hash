module

public import MahjongHandHash.TileCountsKeyRank

@[expose] public section

namespace MahjongDomain

set_option maxHeartbeats 4000000 in
private theorem offset_decode (total rank : Nat) (hlo : 13 ≤ total) (hhi : total ≤ 18)
    (hrank : rank < countDigitsExactly Tile.all total) :
    collectionDecodeNat (collectionOffset total + rank) =
      .ok (countsFromDigits (vectorDigitsUnrank total rank), total) := by
  have ht : total = 13 ∨ total = 14 ∨ total = 15 ∨ total = 16 ∨ total = 17 ∨
      total = 18 := by omega
  have c13 : countDigitsExactly Tile.all 13 = 98521596000 := by decide
  have c14 : countDigitsExactly Tile.all 14 = 326520504500 := by decide
  have c15 : countDigitsExactly Tile.all 15 = 1028352280200 := by decide
  have c16 : countDigitsExactly Tile.all 16 = 3089181590550 := by decide
  have c17 : countDigitsExactly Tile.all 17 = 8879994128500 := by decide
  have c18 : countDigitsExactly Tile.all 18 = 24494416267750 := by decide
  have o13 : collectionOffset 13 = 0 := by decide
  have o14 : collectionOffset 14 = 98521596000 := by decide
  have o15 : collectionOffset 15 = 425042100500 := by decide
  have o16 : collectionOffset 16 = 1453394380700 := by decide
  have o17 : collectionOffset 17 = 4542575971250 := by decide
  have o18 : collectionOffset 18 = 13422570099750 := by decide
  have max : collectionKeyMax = 37916986367500 := by decide
  rcases ht with h | h | h | h | h | h <;> subst total
  all_goals
    simp only [collectionDecodeNat, collectionDecodeNat.find.eq_2,
      c13, c14, c15, c16, c17, c18, o13, o14, o15, o16, o17, o18, max] at *
    split_ifs <;> simp_all only [pure, Except.pure, Nat.reduceAdd, Nat.zero_add,
      Nat.add_sub_cancel_left, Nat.sub_zero] <;> try omega

set_option maxHeartbeats 4000000 in
private theorem offset_bound (total : Nat) (hlo : 13 ≤ total) (hhi : total ≤ 18) :
    collectionOffset total + countDigitsExactly Tile.all total ≤ collectionKeyMax := by
  have ht : total = 13 ∨ total = 14 ∨ total = 15 ∨ total = 16 ∨ total = 17 ∨
      total = 18 := by omega
  rcases ht with h | h | h | h | h | h <;> subst total <;> decide

set_option maxHeartbeats 4000000 in
theorem TileCountsKey.keyMax_le_fixedKeyLimit :
    TileCountsKey.keyMax ≤ fixedKeyLimit.toNat := by decide

/-- Every physically bounded tile-count vector with a full-hand size can be encoded. -/
theorem TileCountsKey.encode_valid (counts : TileCounts) (valid : counts.Valid)
    (size : counts.HasFullHandSize) :
    TileCountsKey.encode counts =
      .ok ⟨Int.ofNat (collectionOffset counts.total + vectorRank counts counts.total)⟩ := by
  have hr := vectorRank_lt counts valid size.2
  have ho := offset_bound counts.total size.1 size.2
  have hb : collectionOffset counts.total + vectorRank counts counts.total ≤
      fixedKeyLimit.toNat := by
    have hm := TileCountsKey.keyMax_le_fixedKeyLimit
    change collectionKeyMax ≤ fixedKeyLimit.toNat at hm
    omega
  have hdecode := offset_decode counts.total (vectorRank counts counts.total)
    size.1 size.2 hr
  have hcounts := countsFromDigits_unrank_rank counts valid size.2
  rw [hcounts] at hdecode
  have hraw : collectionEncodeNat counts =
      .ok (collectionOffset counts.total + vectorRank counts counts.total) := by
    simp [collectionEncodeNat, size, valid, pure, Except.pure]
  have hunchecked : collectionDecodeUnchecked
      (Int.ofNat (collectionOffset counts.total + vectorRank counts counts.total)) =
      .ok counts := by
    simp only [collectionDecodeUnchecked, Int.ofNat_eq_natCast,
      not_lt.mpr (Int.natCast_nonneg _), ite_false, Int.toNat_natCast, hdecode,
      bind, Except.bind, pure, Except.pure]
  simp only [TileCountsKey.encode, hraw, bind, Except.bind, Nat.not_lt.mpr hb,
    ite_false, hunchecked, (TileCounts.same_iff counts counts).mpr rfl,
    ite_true, pure, Except.pure]

/-- The encoded key of every valid full-sized vector decodes back to that vector. -/
theorem TileCountsKey.decode_encode_valid (counts : TileCounts) (valid : counts.Valid)
    (size : counts.HasFullHandSize) :
    TileCountsKey.decode
      ⟨Int.ofNat (collectionOffset counts.total + vectorRank counts counts.total)⟩ =
      .ok counts :=
  TileCountsKey.decode_encode counts _ (TileCountsKey.encode_valid counts valid size)

/-- Valid full-sized vectors have distinct encodings. -/
theorem TileCountsKey.encode_valid_injective (left right : TileCounts)
    (hleft : left.Valid) (hleftSize : left.HasFullHandSize)
    (hright : right.Valid) (hrightSize : right.HasFullHandSize)
    (heq : TileCountsKey.encode left = TileCountsKey.encode right) : left = right := by
  have hl := TileCountsKey.encode_valid left hleft hleftSize
  have hr := TileCountsKey.encode_valid right hright hrightSize
  rw [hl, hr] at heq
  have hk := Except.ok.inj heq
  rw [← hk] at hr
  exact TileCountsKey.encode_injective_on_success left right _ hl hr

end MahjongDomain
