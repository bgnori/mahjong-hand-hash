module

public import MahjongHandHash.TileCountsKeyDigits
public import MahjongHandHash.TileCountsKeyTotal

@[expose] public section

namespace MahjongDomain

private def digitCounts (digits : List Nat) : TileCounts :=
  fun tile => digits[Tile.all.idxOf tile]?.getD 0

private theorem digitCounts_map (digits : List Nat) (hlen : digits.length = Tile.all.length) :
    Tile.all.map (digitCounts digits) = digits := by
  apply List.ext_getElem
  · simpa using hlen.symm
  · intro i hi hd
    rw [List.getElem_map]
    simp only [digitCounts, Tile.all_nodup.idxOf_getElem i (by simpa using hi),
      List.getElem?_eq_getElem hd, Option.getD_some]

private theorem digitCounts_properties (total : Nat) (digits : List Nat)
    (hd : digits ∈ digitVectors Tile.all.length total) :
    (digitCounts digits).Valid ∧ (digitCounts digits).total = total ∧
      Tile.all.map (digitCounts digits) = digits := by
  obtain ⟨hlen, hsum, hbound⟩ := (digitVectors_mem _ _ _).mp hd
  have hm := digitCounts_map digits hlen
  refine ⟨?_, ?_, hm⟩
  · intro tile
    have hmem : digitCounts digits tile ∈ Tile.all.map (digitCounts digits) :=
      List.mem_map.mpr ⟨tile, Tile.mem_all tile, rfl⟩
    rw [hm] at hmem
    exact hbound _ hmem
  · rw [← TileCounts.sum_all, hm, hsum]

private theorem rank_surjective (total : Nat) (htotal : total ≤ 18) (rank : Nat)
    (hrank : rank < countDigitsExactly Tile.all total) :
    ∃ counts : TileCounts, counts.Valid ∧ counts.total = total ∧
      vectorRank counts total = rank := by
  let candidates := (digitVectors Tile.all.length total).toFinset
  let rankDigit := fun digits => vectorRank (digitCounts digits) total
  have hinj : Set.InjOn rankDigit ↑candidates := by
    intro a ha b hb heq
    have ha' := digitCounts_properties total a (List.mem_toFinset.mp ha)
    have hb' := digitCounts_properties total b (List.mem_toFinset.mp hb)
    have ar := vectorDigitsUnrank_rank (digitCounts a) ha'.1 (by rw [ha'.2.1]; exact htotal)
    have br := vectorDigitsUnrank_rank (digitCounts b) hb'.1 (by rw [hb'.2.1]; exact htotal)
    rw [ha'.2.1, ha'.2.2] at ar
    rw [hb'.2.1, hb'.2.2] at br
    change vectorRank (digitCounts a) total = vectorRank (digitCounts b) total at heq
    rw [heq] at ar
    exact ar.symm.trans br
  have hsub : candidates.image rankDigit ⊆ Finset.range (countDigitsExactly Tile.all total) := by
    intro k hk
    obtain ⟨digits, hd, rfl⟩ := Finset.mem_image.mp hk
    have h := digitCounts_properties total digits (List.mem_toFinset.mp hd)
    apply Finset.mem_range.mpr
    have hr := vectorRank_lt (digitCounts digits) h.1 (by rw [h.2.1]; exact htotal)
    simpa only [h.2.1, rankDigit] using hr
  have hcard : (Finset.range (countDigitsExactly Tile.all total)).card ≤
      (candidates.image rankDigit).card := by
    rw [Finset.card_range, Finset.card_image_of_injOn hinj]
    change countDigitsExactly Tile.all total ≤ (digitVectors Tile.all.length total).toFinset.card
    rw [List.toFinset_card_of_nodup (digitVectors_nodup _ _)]
    exact Nat.le_of_eq (countDigitsExactly_eq_digitVectors_length Tile.all total
      (by simp [Tile.all_length]) htotal)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : rank ∈ candidates.image rankDigit := by
    rw [heq]
    exact Finset.mem_range.mpr hrank
  obtain ⟨digits, hd, he⟩ := Finset.mem_image.mp hmem
  have hp := digitCounts_properties total digits (List.mem_toFinset.mp hd)
  exact ⟨digitCounts digits, hp.1, hp.2.1, he⟩

/-- Every rank in a bounded total's interval unpacks to a valid vector of that rank. -/
theorem vectorRank_unrank (total : Nat) (htotal : total ≤ 18) (rank : Nat)
    (hrank : rank < countDigitsExactly Tile.all total) :
    (countsFromDigits (vectorDigitsUnrank total rank)).Valid ∧
      (countsFromDigits (vectorDigitsUnrank total rank)).total = total ∧
      vectorRank (countsFromDigits (vectorDigitsUnrank total rank)) total = rank := by
  obtain ⟨counts, hv, ht, he⟩ := rank_surjective total htotal rank hrank
  have hr := countsFromDigits_unrank_rank counts hv (by rw [ht]; exact htotal)
  rw [ht, he] at hr
  rw [hr]
  exact ⟨hv, ht, he⟩

set_option maxHeartbeats 4000000 in
private theorem key_partition (key : Nat) (hkey : key < collectionKeyMax) :
    ∃ total rank : Nat, 13 ≤ total ∧ total ≤ 18 ∧
      rank < countDigitsExactly Tile.all total ∧ key = collectionOffset total + rank := by
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
  rw [max] at hkey
  by_cases h13 : key < 98521596000
  · refine ⟨13, key, by omega, by omega, ?_, ?_⟩
    · simpa only [c13] using h13
    · simp [o13]
  by_cases h14 : key < 425042100500
  · refine ⟨14, key - 98521596000, by omega, by omega, ?_, ?_⟩
    · rw [c14]; omega
    · rw [o14]; omega
  by_cases h15 : key < 1453394380700
  · refine ⟨15, key - 425042100500, by omega, by omega, ?_, ?_⟩
    · rw [c15]; omega
    · rw [o15]; omega
  by_cases h16 : key < 4542575971250
  · refine ⟨16, key - 1453394380700, by omega, by omega, ?_, ?_⟩
    · rw [c16]; omega
    · rw [o16]; omega
  by_cases h17 : key < 13422570099750
  · refine ⟨17, key - 4542575971250, by omega, by omega, ?_, ?_⟩
    · rw [c17]; omega
    · rw [o17]; omega
  · refine ⟨18, key - 13422570099750, by omega, by omega, ?_, ?_⟩
    · rw [c18]; omega
    · rw [o18]; omega

private theorem nat_encode_surjective (key : Nat) (hkey : key < TileCountsKey.keyMax) :
    ∃ counts : TileCounts, counts.Valid ∧ counts.HasFullHandSize ∧
      TileCountsKey.encode counts = .ok ⟨Int.ofNat key⟩ := by
  obtain ⟨total, rank, hlo, hhi, hr, hk⟩ := key_partition key hkey
  obtain ⟨counts, hv, ht, hvRank⟩ := rank_surjective total hhi rank hr
  have hs : counts.HasFullHandSize := by
    change 13 ≤ counts.total ∧ counts.total ≤ 18
    rw [ht]
    exact ⟨hlo, hhi⟩
  refine ⟨counts, hv, hs, ?_⟩
  have he := TileCountsKey.encode_valid counts hv hs
  rw [ht, hvRank, ← hk] at he
  exact he

private theorem nat_decode_success (key : Nat) (hkey : key < TileCountsKey.keyMax) :
    ∃ counts : TileCounts, counts.Valid ∧ counts.HasFullHandSize ∧
      TileCountsKey.decode ⟨Int.ofNat key⟩ = .ok counts := by
  obtain ⟨counts, hv, hs, he⟩ := nat_encode_surjective key hkey
  exact ⟨counts, hv, hs, TileCountsKey.decode_encode counts _ he⟩

/-- Every key in the assigned interval decodes to a valid full-sized vector. -/
theorem TileCountsKey.decode_success (key : TileCountsKey) (hnonneg : 0 ≤ key.value)
    (hkey : key.value < Int.ofNat TileCountsKey.keyMax) :
    ∃ counts : TileCounts, counts.Valid ∧ counts.HasFullHandSize ∧
      TileCountsKey.decode key = .ok counts := by
  have hnat : key.value.toNat < TileCountsKey.keyMax := (Int.toNat_lt hnonneg).mpr hkey
  obtain ⟨counts, hv, hs, hd⟩ := nat_decode_success key.value.toNat hnat
  have heq : (⟨Int.ofNat key.value.toNat⟩ : TileCountsKey) = key := by
    cases key with
    | mk value =>
        simp only at *
        simp only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg hnonneg]
  rw [heq] at hd
  exact ⟨counts, hv, hs, hd⟩

/-- Every key in the assigned interval is the encoding of a valid full-sized vector. -/
theorem TileCountsKey.encode_surjective (key : TileCountsKey) (hnonneg : 0 ≤ key.value)
    (hkey : key.value < Int.ofNat TileCountsKey.keyMax) :
    ∃ counts : TileCounts, counts.Valid ∧ counts.HasFullHandSize ∧
      TileCountsKey.encode counts = .ok key := by
  obtain ⟨counts, hv, hs, hd⟩ := TileCountsKey.decode_success key hnonneg hkey
  exact ⟨counts, hv, hs, TileCountsKey.encode_decode counts key hd⟩

/-- Negative keys and keys outside the assigned interval are rejected. -/
theorem TileCountsKey.decode_outside (key : TileCountsKey)
    (hout : key.value < 0 ∨ Int.ofNat TileCountsKey.keyMax ≤ key.value) :
    TileCountsKey.decode key = .error (.keyOutOfRange key.value) := by
  by_cases hn : key.value < 0
  · simp only [TileCountsKey.decode, hn, true_or, ite_true]
  by_cases hl : key.value > fixedKeyLimit
  · simp only [TileCountsKey.decode, hl, or_true, ite_true]
  have hn0 : 0 ≤ key.value := by omega
  have hm : Int.ofNat TileCountsKey.keyMax ≤ key.value := by omega
  have hnat : TileCountsKey.keyMax ≤ key.value.toNat := by
    by_contra h
    have hlt : key.value.toNat < TileCountsKey.keyMax := by omega
    have hi := (Int.toNat_lt hn0).mp hlt
    exact (not_lt_of_ge hm) (by simpa only [Int.ofNat_eq_natCast] using hi)
  have heq : Int.ofNat key.value.toNat = key.value := by
    simpa only [Int.ofNat_eq_natCast] using Int.toNat_of_nonneg hn0
  have hd : collectionDecodeUnchecked key.value = .error (.keyOutOfRange key.value) := by
    have hnat' : collectionKeyMax ≤ key.value.toNat := hnat
    simp only [collectionDecodeUnchecked, hn, ite_false, collectionDecodeNat, hnat',
      ite_true, bind, Except.bind, heq]
  simp only [TileCountsKey.decode, hn, hl, or_self, ite_false, hd, bind, Except.bind]

theorem TileCountsKey.decode_success_iff (key : TileCountsKey) :
    (∃ counts, TileCountsKey.decode key = .ok counts) ↔
      0 ≤ key.value ∧ key.value < Int.ofNat TileCountsKey.keyMax := by
  constructor
  · rintro ⟨counts, hd⟩
    by_contra hn
    have hout : key.value < 0 ∨ Int.ofNat TileCountsKey.keyMax ≤ key.value := by omega
    have herr := TileCountsKey.decode_outside key hout
    rw [hd] at herr
    cases herr
  · rintro ⟨hn, hu⟩
    obtain ⟨counts, _, _, hd⟩ := TileCountsKey.decode_success key hn hu
    exact ⟨counts, hd⟩

theorem TileCountsKey.decode_valid (key : TileCountsKey) (counts : TileCounts)
    (hd : TileCountsKey.decode key = .ok counts) :
    counts.Valid ∧ counts.HasFullHandSize := by
  have hrange := (TileCountsKey.decode_success_iff key).mp ⟨counts, hd⟩
  obtain ⟨decoded, hv, hs, hd'⟩ := TileCountsKey.decode_success key hrange.1 hrange.2
  rw [hd] at hd'
  have heq : counts = decoded := Except.ok.inj hd'
  rw [heq]
  exact ⟨hv, hs⟩

end MahjongDomain
