import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two supplied values can be produced by two ordinary gates.
-- Two or more additional NOT gates leave at most twelve binary gates.
theorem PEqualNP.Outside.R_meta_4429_1
    (binaryLower : let target := fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x) →
        13 ≤ C.gates.countP (fun g => !(g.op.eval [false])))
    (zero : let target := fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ i : Fin 11, ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
        D.gates.countP (fun g => g.op.eval [false]) = 0 →
        (∀ j : Fin 9, i ≠ Fin.castAdd 2 j → ∃ g ∈ D.gates,
          (g.op = GateOp.not ∧ g.inputs.head? = some j.val) ∨
          (g.op ≠ GateOp.not ∧ j.val ∈ g.inputs)) →
        ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 2]
          D.eval (w ++ [!(w.getD i.val false)]) ≠ target x)
    (one : let target := fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
      ∀ i : Fin 11, ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
        D.gates.countP (fun g => g.op.eval [false]) = 1 →
        (∀ j : Fin 9, i ≠ Fin.castAdd 2 j → ∃ g ∈ D.gates,
          (g.op = GateOp.not ∧ g.inputs.head? = some j.val) ∨
          (g.op ≠ GateOp.not ∧ j.val ∈ g.inputs)) →
        ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 2]
          D.eval (w ++ [!(w.getD i.val false)]) ≠ target x) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : List (Fin (11 : ℕ))),   x2.length ≤ (2 : ℕ) →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (∀ (x7 : Fin (9 : ℕ)), x2.head? ≠ Option.some (Fin.castAdd (2 : ℕ) x7) → ∃ x9 ∈ x4.gates, x1 x9 ↑x7) →             ∃ (x8 : Fin (9 : ℕ) → Bool),               have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ))];               x4.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x10 : Fin (11 : ℕ)) => x9.getD (↑x10) Bool.false) x2)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  dsimp only
  intro pins hPins D hD hSize hReads
  let countNot := fun g : Gate => g.op.eval [false]
  let target := fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 2]
  let i : Fin 11 := pins.headD 10
  have raw_reads (j : Fin 9) (hj : i ≠ Fin.castAdd 2 j) :
      ∃ g ∈ D.gates, g.op = GateOp.not ∧ g.inputs.head? = some j.val ∨
        g.op ≠ GateOp.not ∧ j.val ∈ g.inputs := by
    apply hReads j
    cases pins with
    | nil => simp
    | cons p rest => simpa [i] using hj
  have hNot (x : Fin 9 → Bool) :
      GateOp.not.eval (pins.map (fun k : Fin 11 => (seed x).getD k.val false)) =
        !((seed x).getD i.val false) := by
    cases pins with
    | nil =>
      have hLen : (seed x).length = 10 := by simp [seed]
      have hFalse : (seed x).getD 10 false = false := List.getD_eq_default _ _ hLen.le
      change true = !((seed x).getD 10 false)
      rw [hFalse]
      rfl
    | cons p rest => rfl
  have hTarget (x : Fin 9 → Bool) :
      target x =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp [target,Bool.or_assoc]
  by_contra hw
  have exactEval (x : Fin 9 → Bool) :
      D.eval (seed x ++ [GateOp.not.eval (pins.map fun k : Fin 11 => (seed x).getD k.val false)]) =
        target x := by
    by_contra h
    apply hw
    refine ⟨x,?_⟩
    rw [hTarget x] at h
    exact h
  let ne := fun g : Gate => !countNot g
  by_cases hz : D.gates.countP countNot = 0
  · obtain ⟨x,hx⟩ := zero i D hD hSize hz raw_reads
    have actual := exactEval x
    rw [hNot x] at actual
    exact hx actual
  by_cases hOne : D.gates.countP countNot = 1
  · obtain ⟨x,hx⟩ := one i D hD hSize hOne raw_reads
    have actual := exactEval x
    rw [hNot x] at actual
    exact hx actual
  have atLeastTwo : 2 ≤ D.gates.countP countNot := by omega
  let gOr : Gate := ⟨.or,[0,2]⟩
  let gNot : Gate := ⟨.not,pins.map Fin.val⟩
  let C : Circuit := ⟨gOr :: gNot :: D.gates,D.output⟩
  have basis : FanInTwo C := by
    intro g hg
    change g ∈ gOr :: gNot :: D.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp [gOr]
    · simpa [gNot] using hPins
    · exact hD g hg
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x) = target x := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun n => w.getD n false)]
    have hFirst : step (List.ofFn x) gOr = seed x := by
      have v0 : (List.ofFn x).getD 0 false = x 0 := by
        simp [List.getD_eq_getElem?_getD]
      have v2 : (List.ofFn x).getD 2 false = x 2 := by
        simp [List.getD_eq_getElem?_getD]
      change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false,
        (List.ofFn x).getD 2 false]] = seed x
      rw [v0,v2]
      change List.ofFn x ++ [x 0 || (x 2 || false)] = List.ofFn x ++ [x 0 || x 2]
      rw [Bool.or_false]
    have hSecond : step (seed x) gNot =
        seed x ++ [GateOp.not.eval (pins.map fun k : Fin 11 => (seed x).getD k.val false)] := by
      simp only [step,gNot,List.map_map,Function.comp_def]
    change (D.gates.foldl step (step (step (List.ofFn x) gOr) gNot)).getD D.output false = _
    rw [hFirst,hSecond]
    exact exactEval x
  have hB := binaryLower C basis computes
  change 13 ≤ C.gates.countP ne at hB
  have hLen := List.length_eq_countP_add_countP countNot (l := D.gates)
  change D.gates.length = D.gates.countP countNot + D.gates.countP ne at hLen
  have split : C.gates.countP ne = D.gates.countP ne + 1 := by
    change (gOr :: gNot :: D.gates).countP ne = _
    rw [List.countP_cons,List.countP_cons]
    rfl
  rw [split] at hB
  change D.gates.length ≤ 13 at hSize
  omega
