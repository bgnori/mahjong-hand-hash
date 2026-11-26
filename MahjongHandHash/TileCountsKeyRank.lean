module

public import MahjongHandHash.TileCountsKeyProof

@[expose] public section

namespace MahjongDomain

private theorem choose_digit (rest : List Tile) (remaining digit rank : Nat)
    (hdigit : digit < 5) (hremaining : digit ≤ remaining)
    (hrank : rank < countDigitsExactly rest (remaining - digit)) :
    vectorDigitsUnrank.go.choose remaining rest 0
      ((List.range digit).foldl
        (fun total earlier =>
          total + if earlier ≤ remaining
            then countDigitsExactly rest (remaining - earlier)
            else 0) 0 + rank) = (digit, rank) := by
  have hd : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨ digit = 3 ∨ digit = 4 := by omega
  have h0 : ¬ 0 ≥ 5 := by omega
  have h1 : ¬ 1 ≥ 5 := by omega
  have h2 : ¬ 2 ≥ 5 := by omega
  have h3 : ¬ 3 ≥ 5 := by omega
  have h4 : ¬ 4 ≥ 5 := by omega
  rcases hd with hd | hd | hd | hd | hd <;> subst digit <;>
    simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Nat.zero_le, Nat.zero_add, ite_true]
  all_goals
    simp only [Nat.sub_zero] at *
    repeat' (rw [vectorDigitsUnrank.go.choose.eq_1] <;>
      simp only [h0, h1, h2, h3, h4, Nat.reduceAdd, Nat.zero_le, ite_true,
        ite_false, Nat.sub_zero] <;>
      split_ifs <;> try omega)
    all_goals simp_all only [Prod.mk.injEq, true_and]
    all_goals omega

/-- Every bounded vector's rank lies within its total's candidate interval. -/
theorem vectorRank_go_lt (counts : TileCounts) (tiles : List Tile) (remaining : Nat)
    (hlen : tiles.length ≤ 34) (htotal : remaining ≤ 18)
    (hsum : (tiles.map counts).sum = remaining)
    (hbound : ∀ tile ∈ tiles, counts tile ≤ 4) :
    vectorRank.go counts tiles remaining < countDigitsExactly tiles remaining := by
  induction tiles generalizing remaining with
  | nil =>
      simp only [List.map_nil, List.sum_nil] at hsum
      subst remaining
      simp [vectorRank.go, countDigitsExactly_nil]
  | cons tile rest ih =>
      simp only [List.map_cons, List.sum_cons] at hsum
      have hd : counts tile ≤ 4 := hbound tile (by simp)
      have hle : counts tile ≤ remaining := by omega
      have htail : (rest.map counts).sum = remaining - counts tile := by omega
      have hi := ih (remaining - counts tile) (by simp only [List.length_cons] at hlen; omega)
        (by omega) htail (by
          intro t ht
          exact hbound t (by simp [ht]))
      rw [vectorRank.go.eq_2, countDigitsExactly_cons tile rest remaining
        (by simp only [List.length_cons] at hlen; omega) htotal]
      have hd' : counts tile = 0 ∨ counts tile = 1 ∨ counts tile = 2 ∨
          counts tile = 3 ∨ counts tile = 4 := by omega
      rcases hd' with h | h | h | h | h <;> rw [h] at hi hle ⊢
      all_goals
        simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
          List.foldl_nil, Nat.zero_le, Nat.zero_add, Nat.sub_zero, ite_true] at *
        split_ifs at * <;> omega

/-- Unranking a bounded vector's rank returns its digits and consumes the rank. -/
theorem vectorDigitsUnrank_go_rank (counts : TileCounts) (tiles : List Tile)
    (remaining : Nat) (hlen : tiles.length ≤ 34) (htotal : remaining ≤ 18)
    (hsum : (tiles.map counts).sum = remaining)
    (hbound : ∀ tile ∈ tiles, counts tile ≤ 4) :
    vectorDigitsUnrank.go tiles remaining (vectorRank.go counts tiles remaining) =
      (tiles.map counts, 0) := by
  induction tiles generalizing remaining with
  | nil => simp [vectorDigitsUnrank.go, vectorRank.go]
  | cons tile rest ih =>
      have hlen' : rest.length ≤ 34 := by simp only [List.length_cons] at hlen; omega
      have hbound' : ∀ t ∈ rest, counts t ≤ 4 := by
        intro t ht
        exact hbound t (by simp [ht])
      have hd : counts tile < 5 := by have := hbound tile (by simp); omega
      have hs : counts tile + (rest.map counts).sum = remaining := by simpa using hsum
      have hle : counts tile ≤ remaining := by omega
      have hs' : (rest.map counts).sum = remaining - counts tile := by omega
      have ht' : remaining - counts tile ≤ 18 := by omega
      have hr := vectorRank_go_lt counts rest (remaining - counts tile) hlen' ht' hs' hbound'
      have hrec := ih (remaining - counts tile) hlen' ht' hs' hbound'
      rw [vectorRank.go.eq_2, vectorDigitsUnrank.go.eq_2,
        choose_digit rest remaining (counts tile) _ hd hle hr]
      simpa only [List.map_cons] using congrArg (fun p : List Nat × Nat =>
        (counts tile :: p.1, p.2)) hrec

theorem Tile.all_nodup : Tile.all.Nodup := by decide

theorem TileCounts.sum_all (counts : TileCounts) : (Tile.all.map counts).sum = counts.total := by
  have hall : Tile.all.toFinset = Finset.univ := by
    apply Finset.ext
    intro tile
    simp [Tile.mem_all]
  rw [← List.sum_toFinset counts Tile.all_nodup, hall]
  rfl

theorem vectorRank_lt (counts : TileCounts) (valid : counts.Valid)
    (htotal : counts.total ≤ 18) :
    vectorRank counts counts.total < countDigitsExactly Tile.all counts.total := by
  exact vectorRank_go_lt counts Tile.all counts.total (by simp [Tile.all_length]) htotal
    (TileCounts.sum_all counts) (by intro tile _; exact valid tile)

theorem vectorDigitsUnrank_rank (counts : TileCounts) (valid : counts.Valid)
    (htotal : counts.total ≤ 18) :
    vectorDigitsUnrank counts.total (vectorRank counts counts.total) = Tile.all.map counts := by
  have h := vectorDigitsUnrank_go_rank counts Tile.all counts.total
    (by simp [Tile.all_length]) htotal (TileCounts.sum_all counts)
    (by intro tile _; exact valid tile)
  exact congrArg Prod.fst h

private theorem zip_map_self (tiles : List Tile) (counts : TileCounts) :
    tiles.zip (tiles.map counts) = tiles.map (fun x => (x, counts x)) := by
  induction tiles with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem reconstruct_list (tiles : List Tile) (counts : TileCounts) (tile : Tile)
    (hnodup : tiles.Nodup) (hmem : tile ∈ tiles) :
    ((tiles.zip (tiles.map counts)).flatMap fun pair =>
      List.replicate pair.2 pair.1).count tile = counts tile := by
  induction tiles with
  | nil => simp at hmem
  | cons head tail ih =>
      have hnot : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htail : tail.Nodup := (List.nodup_cons.mp hnodup).2
      simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, List.count_append,
        List.count_replicate]
      by_cases heq : head = tile
      · subst tile
        have hz : ((tail.zip (tail.map counts)).flatMap fun pair =>
            List.replicate pair.2 pair.1).count head = 0 := by
          rw [List.count_eq_zero]
          simp only [List.mem_flatMap, List.mem_replicate, not_exists]
          intro pair hp
          rw [zip_map_self, List.mem_map] at hp
          obtain ⟨⟨x, hx, heq⟩, _, heq'⟩ := hp
          have : pair.1 = x := congrArg Prod.fst heq.symm
          exact hnot (heq' ▸ this ▸ hx)
        simp [hz]
      · have hm : tile ∈ tail := by
          simp only [List.mem_cons] at hmem
          rcases hmem with h | h
          · exact (heq h.symm).elim
          · exact h
        have hi := ih htail hm
        simp [heq, hi]

theorem countsFromDigits_map (counts : TileCounts) :
    countsFromDigits (Tile.all.map counts) = counts := by
  funext tile
  rw [countsFromDigits, TileCounts.ofList_apply]
  exact reconstruct_list Tile.all counts tile Tile.all_nodup (Tile.mem_all tile)

/-- Every valid count vector of at most 18 tiles is recovered from its rank. -/
theorem countsFromDigits_unrank_rank (counts : TileCounts) (valid : counts.Valid)
    (htotal : counts.total ≤ 18) :
    countsFromDigits (vectorDigitsUnrank counts.total (vectorRank counts counts.total)) =
      counts := by
  rw [vectorDigitsUnrank_rank counts valid htotal, countsFromDigits_map]

end MahjongDomain
