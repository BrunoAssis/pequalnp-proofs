import PEqualNP.Defs

namespace PEqualNP.Outside.Local10400

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A six-input sorting network with only the two middle outputs retained.
def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [1, 3]⟩,
    ⟨.and, [2, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [8, 10]⟩,
    ⟨.and, [9, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [6, 14]⟩, ⟨.or, [6, 14]⟩,
    ⟨.and, [13, 7]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [16, 12]⟩, ⟨.and, [18, 17]⟩,
    ⟨.or, [18, 17]⟩, ⟨.and, [15, 19]⟩, ⟨.or, [20, 21]⟩, ⟨.and, [22, 23]⟩,
    ⟨.not, [24]⟩, ⟨.and, [25, 26]⟩], 27⟩

lemma legal : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma gate_count : witness.size = 22 := by decide +kernel

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 10000 in
lemma correct : ∀ x : Fin 6 → Bool,
    witness.eval (List.ofFn x) = decide (((List.ofFn x).count true) = 3) := by
  decide +kernel

end PEqualNP.Outside.Local10400

open PEqualNP.Outside.Local10400 in
theorem PEqualNP.Outside.L_meta_10400 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide (((List.ofFn x).count true) = 3)) 23 :=
  ⟨witness, legal, by rw [gate_count]; decide, correct⟩
