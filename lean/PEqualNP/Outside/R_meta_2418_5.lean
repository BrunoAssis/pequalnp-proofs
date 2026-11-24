import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

-- The local rewrite replaces a positive-degree AND with the value of a wire.
-- The remaining geometric step asks for a representative admitting that rewrite.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2418_5
    (rewrite : ∀ (n : ℕ) (M : Finset ℕ) (V : Set (Fin n → Bool)) (C : Circuit), Monotone2 C →
      (∀ i a b, C.gates[i]? = some ⟨GateOp.and, [a, b]⟩ →
        let P : Circuit := ⟨C.gates.take i, 0⟩
        let d := P.lineDegrees n M
        0 < d.getD a 0 → 0 < d.getD b 0 →
        ∃ j : ℕ, ∀ x ∈ V,
          let w := P.wires (List.ofFn x)
          (w.getD a false && w.getD b false) = w.getD j false) →
      ∃ D, Monotone2 D ∧ D.size ≤ C.size ∧ HasLineDegree n M D 1 ∧
        ∀ x ∈ V, circuitFun n D x = circuitFun n C x)
    (compatible : let n := 26
      let M := Finset.Ico 13 26
      let V : Set (Fin 26 → Bool) := {x | ∃ l : Fin 13, ∀ k : Fin 13, x (Fin.natAdd 13 k) = true → k = l}
      let S := fun l : Fin 13 => ({0, 1, 3, 9} : Finset (Fin 13)).image (fun d => l + d)
      let f := circuitFun n
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 → RightOnIncidentPairs S C →
        (∀ X Y, IsMaximalFalse S X Y → ¬ IsGeneric S 0 X Y →
          C.eval (incidenceInput X Y) = false) →
        ∃ E : Circuit, Monotone2 E ∧ E.size ≤ C.size ∧
          (∀ x ∈ V, f E x = f C x) ∧
          (∀ i a b, E.gates[i]? = some ⟨GateOp.and, [a, b]⟩ →
        let P : Circuit := ⟨E.gates.take i, 0⟩
        let d := P.lineDegrees n M
        0 < d.getD a 0 → 0 < d.getD b 0 →
        ∃ j : ℕ, ∀ x ∈ V,
          let w := P.wires (List.ofFn x)
          (w.getD a false && w.getD b false) = w.getD j false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  dsimp only
  intro C hC hsize hGood
  let S := fun l : Fin 13 => ({0, 1, 3, 9} : Finset (Fin 13)).image (fun d => l + d)
  have incidence (p l : Fin 13) : p ∈ S l ↔ ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d := by
    simp only [S, Finset.mem_image]
    exact exists_congr (fun d => and_congr_right (fun _ => eq_comm))
  have masks (X Y : Finset (Fin 13)) : incidenceInput X Y =
      List.ofFn (fun i : Fin 26 => decide ((∃ p ∈ X, i = Fin.castAdd 13 p) ∨
        ∃ l ∈ Y, i = Fin.natAdd 13 l)) := by
    change List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ Y)) = _
    rw [List.ofFn_add (n := 13) (m := 13)]
    congr 1 <;> congr 1 <;> funext i <;> congr 1
    · apply propext
      change i ∈ X ↔ (∃ p ∈ X, Fin.castAdd 13 i = Fin.castAdd 13 p) ∨
        ∃ l ∈ Y, Fin.castAdd 13 i = Fin.natAdd 13 l
      have hn : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide
      constructor
      · intro hi
        exact Or.inl ⟨i, hi, rfl⟩
      · rintro (⟨p, hp, hi⟩ | ⟨l, _, hi⟩)
        · have hv := congrArg (fun q : Fin 26 => q.val) hi
          change i.val = p.val at hv
          have h : i = p := Fin.ext hv
          exact h ▸ hp
        · exact (hn i l hi).elim
    · apply propext
      have hn : ∀ p l : Fin 13, Fin.natAdd 13 l ≠ Fin.castAdd 13 p := by decide
      constructor
      · intro hi
        exact Or.inr ⟨i, hi, rfl⟩
      · rintro (⟨p, _, hi⟩ | ⟨l, hl, hi⟩)
        · exact (hn p i hi).elim
        · have hv := congrArg (fun q : Fin 26 => q.val) hi
          change 13 + i.val = 13 + l.val at hv
          have h : i = l := Fin.ext (Nat.add_left_cancel hv)
          exact h ▸ hl
  have pos : RightOnIncidentPairs S C := by
    intro l p hpl
    have h := hGood.1 p l ((incidence p l).mp hpl)
    change C.eval (List.ofFn _) = true at h
    simpa only [masks, Finset.mem_singleton, exists_eq_left] using h
  have neg : ∀ X Y, IsMaximalFalse S X Y → ¬ IsGeneric S 0 X Y →
      C.eval (incidenceInput X Y) = false := by
    intro X Y hmax hdeg
    have Y_iff (l : Fin 13) : l ∈ Y ↔ ∀ p ∈ X, ¬ (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d) := by
      constructor
      · intro h p hp hinc
        exact Finset.disjoint_left.mp (hmax.1 l h) ((incidence p l).2 hinc) hp
      · intro hav
        by_contra hnY
        apply hmax.2.2 l hnY
        intro k hk
        rcases Finset.mem_insert.mp hk with he | he
        · subst k
          exact Finset.disjoint_left.mpr (fun p hS hX => hav p hX ((incidence p l).mp hS))
        · exact hmax.1 k he
    have maxX : ∀ v ∉ X, ∃ l, (∀ p ∈ X, ¬ (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d)) ∧
        (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = l + d) := by
      intro v hv
      by_contra hn
      apply hmax.2.1 v hv
      intro l hl
      apply Finset.disjoint_left.mpr
      intro p hpl hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hn ⟨l, (Y_iff l).mp hl, (incidence _ l).mp hpl⟩
      · exact Finset.disjoint_left.mp (hmax.1 l hl) hpl hx
    have deg : (∃ l, ∀ p ∈ X, ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d) ∨
        ∃ p, ∀ l, (∀ q ∈ X, ¬ (∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = l + d)) →
          ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d := by
      classical
      rcases not_and_or.mp (fun hp : InNoLine S X ∧ InNoPencil S Y =>
        hdeg ⟨Nat.zero_le _, Nat.zero_le _, hp⟩) with h | h
      · obtain ⟨l, hl⟩ := not_forall.mp h
        exact Or.inl ⟨l, fun p hp => (incidence p l).mp (not_not.mp hl hp)⟩
      · obtain ⟨p, hp⟩ := not_forall.mp h
        exact Or.inr ⟨p, fun l hl => (incidence p l).mp (not_not.mp hp l ((Y_iff l).mpr hl))⟩
    have hneg := hGood.2 X maxX deg
    rw [masks]
    change C.eval (List.ofFn _) = false at hneg
    convert hneg using 3
    funext k
    simp only [Y_iff]
    congr 1
    exact propext (or_congr Iff.rfl (exists_congr fun _ => and_comm))
  obtain ⟨E, hE, hEC, hECrows, hEc⟩ := compatible C hC hsize pos neg
  obtain ⟨D, hD, hDE, hd, hDErows⟩ := rewrite 26 (Finset.Ico 13 26)
    {x | ∃ l : Fin 13, ∀ k : Fin 13, x (Fin.natAdd 13 k) = true → k = l} E hE hEc
  exact ⟨D, hD, hDE.trans hEC, hd, fun x hx => (hDErows x hx).trans (hECrows x hx)⟩
