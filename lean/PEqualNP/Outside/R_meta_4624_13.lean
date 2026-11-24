import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4624_13
    (hform : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ u v, G.Adj u v) → ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
        circuitFun n C = graphFun G ∅ ∧ IsAO2 n C ∧ TopForm G C)
    (hpivot : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j < C.size, ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
        circuitFun n (eraseGate n C j (n+C.size)) (pairInput u v) = false)
    (hblock : ∀ (n : ℕ) (C : Circuit), IsMinimalMonoCircuit n C →
      ∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ p ∈ (gateAt C j).inputs, p < n+j →
      ∃ x : Fin n → Bool, circuitFun n C x = false ∧ circuitFun n (eraseGate n C j p) x = true ∧
        (C.wires (List.ofFn x)).getD p false = true ∧ gateVal n C j x = false)
    (hrepair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∀ v, G.degree v ≠ 1) → ∀ C : Circuit, IsMinimalMonoCircuit n C →
      circuitFun n C = graphFun G ∅ → IsAO2 n C → TopForm G C →
      let bad := fun D : Circuit => ((Finset.range D.size).filter fun i =>
        (gateAt D i).op.eval [] = true ∧ ¬∃ a b, G.Adj a b ∧ Owns n D i a b).card
      ∀ j < C.size, (gateAt C j).op = GateOp.and →
      (∀ a b, G.Adj a b → ¬Owns n C j a b) →
      (∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
        circuitFun n (eraseGate n C j (n+C.size)) (pairInput u v) = false) →
      (∀ p ∈ (gateAt C j).inputs, ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
        circuitFun n (eraseGate n C j p) x = true) →
      ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
        IsAO2 n D ∧ TopForm G D ∧ bad D < bad C) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1), x2.degree x7 ≠ (1 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 ∧ PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x9 < x8.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ PEqualNP.EdgeOwnership.Owns x1 x8 x9 x12 x13 := by
  classical
  intro n G inst triangle noFour nonempty degrees
  let bad := fun D : Circuit => ((Finset.range D.size).filter fun i =>
    (gateAt D i).op.eval [] = true ∧ ¬∃ a b, G.Adj a b ∧ Owns n D i a b).card
  let candidate := fun k : ℕ => ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
    circuitFun n C = graphFun G ∅ ∧ IsAO2 n C ∧ TopForm G C ∧ bad C = k
  obtain ⟨C₀, least₀, correct₀, ao₀, top₀⟩ := hform n G nonempty
  have hasCandidate : ∃ k, candidate k := ⟨bad C₀,C₀,least₀,correct₀,ao₀,top₀,rfl⟩
  obtain ⟨C,least,correct,ao,top,cost⟩ := Nat.find_spec hasCandidate
  refine ⟨C,least,correct,?_⟩
  intro j hj hand
  by_contra missing
  have hno : ∀ a b, G.Adj a b → ¬Owns n C j a b := fun a b edge owns => missing ⟨a,b,edge,owns⟩
  have witness : ∀ p ∈ (gateAt C j).inputs, ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      circuitFun n (eraseGate n C j p) x = true := by
    intro p hp
    obtain ⟨x,reject,accept,_,_⟩ := hblock n C least j hj hand p hp (ao.2.1 j hj p hp)
    exact ⟨x,(congrFun correct x).symm.trans reject,accept⟩
  obtain ⟨D,leastD,correctD,aoD,topD,better⟩ := hrepair n G triangle noFour degrees C
    least correct ao top j hj hand hno (hpivot n G C least correct j hj) witness
  have minD := Nat.find_min' hasCandidate (show candidate (bad D) from ⟨D,leastD,correctD,aoD,topD,rfl⟩)
  exact (Nat.not_lt_of_ge (cost.le.trans minD)) better
