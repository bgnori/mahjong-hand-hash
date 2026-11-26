module

public import MahjongHandHash.TileCountsKeyProof

@[expose] public section

namespace MahjongDomain

/-- Enumeration used to specify bounded tile-count vectors, not to encode them. -/
def digitVectors : Nat → Nat → List (List Nat)
  | 0, total => if total = 0 then [[]] else []
  | n + 1, total =>
      (List.range 5).flatMap fun digit =>
        if digit ≤ total then (digitVectors n (total - digit)).map (digit :: ·)
        else []

theorem digitVectors_count (n total : Nat) (hn : n ≤ 34) (ht : total ≤ 18) :
    countDigitsExactly (List.replicate n (.suited .man 0)) total =
      (digitVectors n total).length := by
  induction n generalizing total with
  | zero =>
      simp only [List.replicate_zero, countDigitsExactly_nil, digitVectors]
      split <;> simp_all
  | succ n ih =>
      rw [List.replicate_succ, countDigitsExactly_cons]
      · simp only [digitVectors, List.length_flatMap]
        simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
          List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        have hn' : n ≤ 34 := by omega
        have h0 := ih total hn' ht
        have h1 := ih (total - 1) hn' (by omega)
        have h2 := ih (total - 2) hn' (by omega)
        have h3 := ih (total - 3) hn' (by omega)
        have h4 := ih (total - 4) hn' (by omega)
        simp only [h1, h2, h3, h4]
        split_ifs <;> simp_all
      · simp only [List.length_replicate]; omega
      · exact ht

theorem countDigitsExactly_eq_digitVectors_length (tiles : List Tile) (total : Nat)
    (hlen : tiles.length ≤ 34) (htotal : total ≤ 18) :
    countDigitsExactly tiles total = (digitVectors tiles.length total).length := by
  have h : countDigitsExactly tiles total =
      countDigitsExactly (List.replicate tiles.length (.suited .man 0)) total := by
    simp only [countDigitsExactly, List.length_replicate]
  rw [h]
  exact digitVectors_count tiles.length total hlen htotal

theorem digitVectors_mem (n total : Nat) (digits : List Nat) :
    digits ∈ digitVectors n total ↔
      digits.length = n ∧ digits.sum = total ∧ ∀ digit ∈ digits, digit ≤ 4 := by
  induction n generalizing total digits with
  | zero =>
      cases digits with
      | nil => simp [digitVectors, eq_comm]
      | cons digit rest => simp [digitVectors]
  | succ n ih =>
      cases digits with
      | nil => simp [digitVectors]
      | cons digit rest =>
          simp only [digitVectors, List.mem_flatMap, List.mem_range, List.length_cons,
            List.sum_cons, Nat.succ.injEq, List.mem_cons]
          constructor
          · rintro ⟨d, hd, hx⟩
            split at hx
            · rename_i hle
              rw [List.mem_map] at hx
              obtain ⟨xs, hxs, heq⟩ := hx
              cases heq
              have hv := (ih (total - digit) rest).mp hxs
              refine ⟨hv.1, ?_, ?_⟩
              · omega
              · intro x hx
                rcases hx with rfl | hx
                · omega
                · exact hv.2.2 x hx
            · simp at hx
          · rintro ⟨hlen, hsum, hbound⟩
            have hd : digit < 5 := by
              have := hbound digit (Or.inl rfl)
              omega
            have hle : digit ≤ total := by omega
            refine ⟨digit, hd, ?_⟩
            simp only [hle, ite_true, List.mem_map]
            refine ⟨rest, (ih (total - digit) rest).mpr ?_, rfl⟩
            refine ⟨hlen, ?_, ?_⟩
            · omega
            · intro x hx
              exact hbound x (Or.inr hx)

theorem digitVectors_nodup (n total : Nat) : (digitVectors n total).Nodup := by
  induction n generalizing total with
  | zero =>
      simp only [digitVectors]
      split <;> simp
  | succ n ih =>
      simp only [digitVectors, List.nodup_flatMap]
      constructor
      · intro digit _
        split
        · apply List.Nodup.map
          · intro a b hab
            exact List.cons.inj hab |>.2
          · exact ih _
        · simp
      · apply List.Pairwise.imp _ List.nodup_range
        intro a b hab
        apply List.disjoint_left.mpr
        intro xs hxs hys
        dsimp only at hxs hys
        split_ifs at hxs hys <;> try simp_all only [List.not_mem_nil]
        rw [List.mem_map] at hxs hys
        obtain ⟨as, _, ha⟩ := hxs
        obtain ⟨bs, _, hb⟩ := hys
        have : a = b := by
          have h := ha.trans hb.symm
          exact (List.cons.inj h).1
        exact hab this

end MahjongDomain
