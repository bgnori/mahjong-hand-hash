module

public import MahjongHandHash.HandKey

@[expose] public section

namespace MahjongDomain

private def digitCountByLength (length total : Nat) : Nat :=
  countDigitsExactly (List.replicate length (.suited .man 0)) total

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem digitCountByLength_step :
    ∀ length : Fin 34, ∀ total : Fin 19,
      digitCountByLength (length.val + 1) total.val =
        (List.range 5).foldl (fun sum digit =>
          sum + if digit ≤ total.val then digitCountByLength length.val (total.val - digit)
            else 0) 0 := by
  decide

private theorem countDigitsExactly_length (tiles : List Tile) (total : Nat) :
    countDigitsExactly tiles total = digitCountByLength tiles.length total := by
  simp only [digitCountByLength, countDigitsExactly, List.length_replicate]

theorem countDigitsExactly_nil (total : Nat) :
    countDigitsExactly [] total = if total = 0 then 1 else 0 := by
  simp [countDigitsExactly]

/-- In the supported range, candidate counts partition by the first tile count. -/
theorem countDigitsExactly_cons (tile : Tile) (tiles : List Tile) (total : Nat)
    (hlen : tiles.length < 34) (htotal : total ≤ 18) :
    countDigitsExactly (tile :: tiles) total =
      (List.range 5).foldl (fun sum digit =>
        sum + if digit ≤ total then countDigitsExactly tiles (total - digit) else 0) 0 := by
  have h := digitCountByLength_step ⟨tiles.length, hlen⟩ ⟨total, by omega⟩
  simpa only [countDigitsExactly_length, List.length_cons, Nat.succ_eq_add_one] using h

theorem TileCounts.same_iff (left right : TileCounts) : left.same right = true ↔ left = right := by
  simp only [TileCounts.same, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h
    funext tile
    exact h tile (Tile.mem_all tile)
  · intro h tile _
    rw [h]

theorem TileCountsKey.encode_range (counts : TileCounts) (key : TileCountsKey)
    (h : TileCountsKey.encode counts = .ok key) :
    0 ≤ key.value ∧ key.value ≤ fixedKeyLimit := by
  unfold TileCountsKey.encode at h
  cases hraw : collectionEncodeNat counts with
  | error err => simp only [hraw, bind, Except.bind] at h; cases h
  | ok raw =>
      simp only [hraw, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i hbound
        split at h
        · cases h
        ·
          split at h
          · have hk : (⟨Int.ofNat raw⟩ : TileCountsKey) = key := Except.ok.inj h
            cases hk
            constructor
            · exact Int.natCast_nonneg raw
            · have hb : raw ≤ fixedKeyLimit.toNat := Nat.le_of_not_gt hbound
              have hi : Int.ofNat raw ≤ Int.ofNat fixedKeyLimit.toNat := Int.ofNat_le.mpr hb
              simpa [fixedKeyLimit] using hi
          · cases h

private theorem encode_unchecked (counts : TileCounts) (key : TileCountsKey)
    (h : TileCountsKey.encode counts = .ok key) :
    collectionDecodeUnchecked key.value = .ok counts := by
  unfold TileCountsKey.encode at h
  cases hraw : collectionEncodeNat counts with
  | error err => simp only [hraw, bind, Except.bind] at h; cases h
  | ok raw =>
      simp only [hraw, bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i decoded hdecoded
          split at h
          · rename_i hsame
            have hk : (⟨Int.ofNat raw⟩ : TileCountsKey) = key := Except.ok.inj h
            have hc : decoded = counts := (TileCounts.same_iff decoded counts).mp hsame
            cases hk
            cases hc
            exact hdecoded
          · cases h

private theorem encode_nat (counts : TileCounts) (key : TileCountsKey)
    (h : TileCountsKey.encode counts = .ok key) :
    collectionEncodeNat counts = .ok key.value.toNat := by
  unfold TileCountsKey.encode at h
  cases hraw : collectionEncodeNat counts with
  | error err => simp only [hraw, bind, Except.bind] at h; cases h
  | ok raw =>
      simp only [hraw, bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · have hk : (⟨Int.ofNat raw⟩ : TileCountsKey) = key := Except.ok.inj h
            cases hk
            rfl
          · cases h

/-- Every successful encoding decodes to its input; this does not assert encode succeeds. -/
theorem TileCountsKey.decode_encode (counts : TileCounts) (key : TileCountsKey)
    (h : TileCountsKey.encode counts = .ok key) :
    TileCountsKey.decode key = .ok counts := by
  have hrange := TileCountsKey.encode_range counts key h
  have hdecode := encode_unchecked counts key h
  have hencode := encode_nat counts key h
  have hn : ¬ (key.value < 0 ∨ key.value > fixedKeyLimit) := by omega
  simp [TileCountsKey.decode, hn, hdecode, hencode, bind, Except.bind, pure, Except.pure]

/-- Every successfully decoded key re-encodes to the same key. -/
theorem TileCountsKey.encode_decode (counts : TileCounts) (key : TileCountsKey)
    (h : TileCountsKey.decode key = .ok counts) :
    TileCountsKey.encode counts = .ok key := by
  unfold TileCountsKey.decode at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hrange
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i decoded hdecoded
      split at h
      · cases h
      · rename_i encoded hencoded
        split at h
        · rename_i heq
          have hc : decoded = counts := Except.ok.inj h
          cases hc
          have hn : 0 ≤ key.value := by omega
          have hl : key.value ≤ fixedKeyLimit := by omega
          have hi : Int.ofNat key.value.toNat = key.value := Int.toNat_of_nonneg hn
          have hb : key.value.toNat ≤ fixedKeyLimit.toNat := Int.toNat_le_toNat hl
          subst encoded
          simp only [TileCountsKey.encode, hencoded, bind, Except.bind, Nat.not_lt.mpr hb,
            ite_false, hi, hdecoded, (TileCounts.same_iff counts counts).mpr rfl, ite_true,
            pure, Except.pure]
        · cases h

theorem TileCountsKey.encode_injective_on_success (left right : TileCounts) (key : TileCountsKey)
    (hleft : TileCountsKey.encode left = .ok key)
    (hright : TileCountsKey.encode right = .ok key) : left = right := by
  have hl := TileCountsKey.decode_encode left key hleft
  have hr := TileCountsKey.decode_encode right key hright
  rw [hl] at hr
  exact Except.ok.inj hr

end MahjongDomain
