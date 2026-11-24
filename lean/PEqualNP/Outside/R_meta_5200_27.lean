import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Replace each AND-only segment by its set of earlier non-AND terminals.
-- The number of terminals is bounded even when two segments share a gate.
theorem PEqualNP.Outside.R_meta_5200_27
    (frontier : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
      ∀ a b : ℕ,
      (∀ j < C.size, (gateAt C j).op = .and →
        (∃ w ∈ (gateAt C j).inputs, 26 ≤ w ∧ (gateAt C (w-26)).op = .and) → j = a ∨ j = b) →
      ∀ j < C.size, (gateAt C j).op = .and → ∃ F : Finset ℕ, F.card ≤ (if j = a ∨ j = b then 6 else 2) ∧
        (∀ i ∈ F, i < 26+j ∧ (26 ≤ i → (gateAt C (i-26)).op ≠ .and)) ∧
        ∀ x : List Bool, x.length = 26 → (wireValue C x (26+j) = true ↔ ∀ i ∈ F, wireValue C x i = true))
    (count : ∀ (C : Circuit) (out : Bool → ℕ), Monotone2 C → ReadsBack 26 C →
      (∀ b, out b < 26+C.size) →
      let P := singerLines3
      let R := fun (Q T : Finset (Fin 13)) =>
        (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (i ∈ T)
      let W := wireValue C
      (∀ p l : Fin 13, p ∈ P l → ∃ b, W (R {p} {l}) (out b) = true) →
      (∀ Q, IsQuadrangle P Q → ∀ b, W (R Q (missLines P Q)) (out b) = false) →
      (∀ b, ∃ p l : Fin 13, p ∈ P l ∧ W (R {p} {l}) (out b) = true ∧
        W (R {p} {l}) (out (!b)) = false) →
      (∃ c d : ℕ, ∀ j < C.size, (gateAt C j).op = .and → ∃ F : Finset ℕ,
        F.card ≤ (if j = c ∨ j = d then 6 else 2) ∧
        (∀ i ∈ F, i < 26+j ∧ (26 ≤ i → (gateAt C (i-26)).op ≠ .and)) ∧
        ∀ x : List Bool, x.length = 26 → (W x (26+j) = true ↔ ∀ i ∈ F, W x i = true)) →
      63 ≤ C.size) :
have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∃ x18 ∈ Finset.range x7.size, ∃ x19 ∈ Finset.range x7.size, x18 ≠ x19 ∧ x6 x7 x18 ∧ x6 x7 x19 ∧ ∀ x20 ∈ Finset.range x7.size, x6 x7 x20 → x20 = x18 ∨ x20 = x19) → (63 : ℕ) ≤ x7.size
:= by
  dsimp only
  intro C a b mono back lowA lowB cover rejects onlyA onlyB nested
  let out : Bool → ℕ := fun bit => if bit then b else a
  apply count C out mono back
  · intro bit
    cases bit <;> assumption
  · intro p l inc
    rcases cover p l inc with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · intro Q quad bit
    cases bit
    · exact (rejects Q quad).1
    · exact (rejects Q quad).2
  · intro bit
    cases bit
    · exact onlyA
    · exact onlyB
  · obtain ⟨c,_,d,_,_,_,_,hd⟩ := nested
    exact ⟨c,d,frontier C mono back c d (fun j hj op pred => hd j (Finset.mem_range.mpr hj) ⟨op,pred⟩)⟩
