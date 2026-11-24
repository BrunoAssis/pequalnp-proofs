import Mathlib
import PEqualNP.Defs

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open scoped Classical

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_5220_19
    (geometric : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      N = q*q+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → ∀ E : Finset (Fin N × Fin N),
      (∀ e ∈ E, I e.1 e.2) → 44*((E.image Prod.fst).card+(E.image Prod.snd).card-1) < E.card →
      88 ≤ q ∨ (q = 87 ∧ E.image Prod.fst = univ ∧ E.image Prod.snd = univ ∧
        E.card ≤ 88*N ∧ 88*N ≤ E.card+43))
    (support : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      Monotone2 C →
      (∀ s : Finset (Fin N), s.card ≤ 1 → C.eval (List.ofFn (Fin.addCases
        (fun p => decide (¬∃ l ∈ s, I p l)) (fun l => decide (l ∈ s)))) = false) →
      let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)
      ∀ E : Finset (Fin N × Fin N), E.image Prod.fst = univ → E.image Prod.snd = univ →
        (∀ e ∈ E, C.eval (List.ofFn (pair e)) = true) →
        2*N-1 ≤ Fintype.card {j : Fin C.size //
          (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
          ∃ e ∈ E, gateVal (N+N) C j.val (pair e) = true})
    (near : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      N = 7657 → (∀ l, Fintype.card {p // I p l} = 88) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsMinimalMonoCircuit (N+N) C →
      (∀ s : Finset (Fin N), s.card ≤ 87 → C.eval (List.ofFn (Fin.addCases
        (fun p => decide (¬∃ l ∈ s, I p l)) (fun l => decide (l ∈ s)))) = false) →
      let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)
      ∀ E : Finset (Fin N × Fin N),
        (∀ e ∈ E, I e.1 e.2 ∧ C.eval (List.ofFn (pair e)) = true) →
        88*N ≤ E.card+43 → Fintype.card {j : Fin C.size //
          (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
          ∃ e ∈ E, gateVal (N+N) C j.val (pair e) = true} ≠ 2*N-1)
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      88 ≤ q → N = q*q+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsMinimalMonoCircuit (N+N) C →
      (∀ s : Finset (Fin N), s.card ≤ q → C.eval (List.ofFn (Fin.addCases
        (fun p => decide (¬∃ l ∈ s, I p l)) (fun l => decide (l ∈ s)))) = false) →
      let pair (e : Fin N × Fin N) := pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)
      let D : Circuit := ⟨C.gates.map (fun g =>
        if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          (g.inputs.all fun i => decide (0 < (C.lineDegrees (N+N) (Ico N (N+N))).getD i 0)) = true
        then ⟨.or,[]⟩ else g), C.output⟩
      ∀ E : Finset (Fin N × Fin N),
        (∀ e ∈ E, I e.1 e.2 ∧ C.eval (List.ofFn (pair e)) = true ∧ D.eval (List.ofFn (pair e)) = false) →
        44*((E.image Prod.fst).card+(E.image Prod.snd).card-1) < E.card → E.card ≤ 44 * Fintype.card {j : Fin C.size //
          (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
          ∃ e ∈ E, gateVal (N+N) C j.val (pair e) = true}) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 = x1 * x1 + x1 + (1 : ℕ) →     (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →       (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →         PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →           (∀ (x10 : Finset (Fin x2)), x10.card ≤ x1 → x5.eval (List.ofFn fun (x12 : Fin (x2 + x2)) => Fin.addCases (fun (x13 : Fin x2) => Decidable.decide ¬∃ x14 ∈ x10, x3 x13 x14) (fun (x13 : Fin x2) => Decidable.decide (x13 ∈ x10)) x12) = Bool.false) →             have x11 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x11 x12 : Fin x2) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x2 x11) (Fin.natAdd x2 x12);             have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };             ∀ (x13 : Fin x2 → Finset (Fin x2)), (∀ (x14 x15 : Fin x2), x15 ∈ x13 x14 → x3 x15 x14 ∧ x5.eval (List.ofFn (x11 x15 x14)) = Bool.true ∧ x12.eval (List.ofFn (x11 x15 x14)) = Bool.false) → (44 : ℕ) * (Fintype.card { x15 : Fin (x2 + x2) // ∃ (x16 : Fin x2), ∃ x17 ∈ x13 x16, x11 x17 x16 x15 = Bool.true } - (1 : ℕ)) < ∑ x15 : Fin x2, (x13 x15).card → ∑ x16 : Fin x2, (x13 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x13 x17, PEqualNP.EdgeOwnership.gateVal (x2 + x2) x5 (↑x16) (x11 x18 x17) = Bool.true } := by
  classical
  intro q N I inst C order lines unique minimal sound pair D T valid dense
  let E := univ.filter (fun e : Fin N × Fin N => e.1 ∈ T e.2)
  have memE (p l : Fin N) : (p,l) ∈ E ↔ p ∈ T l := by simp [E]
  have sizeE : E.card = ∑ l, (T l).card := by
    dsimp only [E]
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_boole]
    simp
  let P := (E.image Prod.fst).image (Fin.castAdd N)
  let L := (E.image Prod.snd).image (Fin.natAdd N)
  have inputCount : Fintype.card {j : Fin (N+N) // ∃ l, ∃ p ∈ T l, pair p l j = true} =
      (E.image Prod.fst).card + (E.image Prod.snd).card := by
    rw [Fintype.card_subtype]
    have split : (univ.filter fun j => ∃ l, ∃ p ∈ T l, pair p l j = true) = P ∪ L := by
      ext j
      simp only [mem_filter,mem_univ,true_and,mem_union,mem_image,P,L]
      constructor
      · rintro ⟨l,p,hp,on⟩
        rcases of_decide_eq_true on with eq|eq
        · exact Or.inl ⟨p,⟨(p,l),(memE p l).mpr hp,rfl⟩,eq.symm⟩
        · exact Or.inr ⟨l,⟨(p,l),(memE p l).mpr hp,rfl⟩,eq.symm⟩
      · rintro (⟨p,⟨⟨u,l⟩,he,rfl⟩,rfl⟩ | ⟨l,⟨⟨p,m⟩,he,rfl⟩,rfl⟩)
        · exact ⟨l,u,(memE u l).mp he,decide_eq_true (Or.inl rfl)⟩
        · exact ⟨m,p,(memE p m).mp he,decide_eq_true (Or.inr rfl)⟩
    have disj : Disjoint P L := by
      apply disjoint_left.mpr
      intro j hp hl
      obtain ⟨p,_,rfl⟩ := mem_image.mp hp
      obtain ⟨l,_,eq⟩ := mem_image.mp hl
      have h := congrArg Fin.val eq
      change N+l.val = p.val at h
      omega
    rw [split,card_union_of_disjoint disj]
    have inj : Function.Injective (Fin.natAdd N : Fin N → Fin (N+N)) := by
      intro a b h
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val h)
    exact congrArg₂ (· + ·) (card_image_of_injective _ (Fin.castAdd_injective N N)) (card_image_of_injective _ inj)
  have hD : 44*((E.image Prod.fst).card+(E.image Prod.snd).card-1) < E.card := by
    rw [← inputCount,sizeE]
    exact dense
  have tests : ∀ e ∈ E, I e.1 e.2 ∧ C.eval (List.ofFn (pair e.1 e.2)) = true ∧
      D.eval (List.ofFn (pair e.1 e.2)) = false := by
    rintro ⟨p,l⟩ he
    exact valid l p ((memE p l).mp he)
  have equalGateCount : Fintype.card {j : Fin C.size //
      (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      ∃ l, ∃ p ∈ T l, gateVal (N+N) C j.val (pair p l) = true} = Fintype.card {j : Fin C.size //
      (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      ∃ e ∈ E, gateVal (N+N) C j.val (pair e.1 e.2) = true} := by
    rw [Fintype.card_subtype,Fintype.card_subtype]
    congr 1
    ext j
    simp only [mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨off,l,p,hp,on⟩
      exact ⟨off,(p,l),(memE p l).mpr hp,on⟩
    · rintro ⟨off,⟨p,l⟩,he,on⟩
      exact ⟨off,l,p,(memE p l).mp he,on⟩
  rw [equalGateCount,← sizeE]
  rcases geometric q N I order lines unique E (fun e he => (tests e he).1) hD with h | ⟨rfl,allP,allL,cap,almost⟩
  · exact large q N I C h order lines unique minimal sound E tests hD
  · have exactOrder : N = 7657 := order
    have lower := support N I C minimal.1 (fun s hs => sound s (hs.trans (by decide))) E allP allL
      (fun e he => (tests e he).2.1)
    by_contra! excess
    let active := Fintype.card {j : Fin C.size //
      (C.wires (List.replicate (N+N) false)).getD (N+N+j.val) false = false ∧
      ∃ e ∈ E, gateVal (N+N) C j.val (pair e.1 e.2) = true}
    change 44*active < E.card at excess
    change 2*N-1 ≤ active at lower
    have saturated : active = 2*N-1 := by omega
    exact (near N I C exactOrder lines unique minimal sound E
      (fun e he => ⟨(tests e he).1,(tests e he).2.1⟩) almost) saturated
