import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Restrict the input whose complement and pairwise disjunction are both supplied.
-- The two-reader case loses at least two gates under that restriction.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3861_1
    (many : let readers := fun C : Circuit =>
        (C.gates.filter fun g => [0, 9].any
          (g.inputs.take (if g.op.eval [false] = true then 1 else 2)).contains).length
      let extend : (Fin 8 → Bool) → Fin 9 → Bool := fun y => Fin.cons false y
      ∀ (j : Fin 9), j ≠ 0 → ∀ D : Circuit, FanInTwo D → D.size ≤ 13 → 2 ≤ readers D →
        HasCircuitSize 8 (fun y : Fin 8 → Bool =>
          D.eval (List.ofFn (extend y) ++ [true, extend y j])) 11)
    (lower : let target := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ¬ HasCircuitSize 8 (fun y : Fin 8 → Bool => target (Fin.cons false y)) 11)
    (zero : let readers := fun C : Circuit =>
        (C.gates.filter fun g => [0, 9].any
          (g.inputs.take (if g.op.eval [false] = true then 1 else 2)).contains).length
      let row := fun (j : Fin 9) (x : Fin 9 → Bool) =>
        List.ofFn x ++ [!x 0, x 0 || x j]
      let target := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ j : Fin 9, j = 1 ∨ j = 4 → ∀ D : Circuit, FanInTwo D →
        D.size ≤ 13 → readers D = 0 → ∃ x, D.eval (row j x) ≠ target x)
    (one : let readers := fun C : Circuit =>
        (C.gates.filter fun g => [0, 9].any
          (g.inputs.take (if g.op.eval [false] = true then 1 else 2)).contains).length
      let row := fun (j : Fin 9) (x : Fin 9 → Bool) =>
        List.ofFn x ++ [!x 0, x 0 || x j]
      let target := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ j : Fin 9, j = 1 ∨ j = 4 → ∀ D : Circuit, FanInTwo D →
        D.size ≤ 13 → readers D = 1 → ∃ x, D.eval (row j x) ≠ target x) :
    ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (1 : ℕ)] ∨ x1 = [(0 : ℕ), (4 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hp D hf hs
  obtain ⟨j, hj, hpins⟩ : ∃ j : Fin 9, (j = 1 ∨ j = 4) ∧
      pins = [0,j.val] := by
    rcases hp with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨4, Or.inr rfl, h⟩
  subst pins
  let readers := fun C : Circuit =>
        (C.gates.filter fun g => [0, 9].any
          (g.inputs.take (if g.op.eval [false] = true then 1 else 2)).contains).length
  let row := fun (j : Fin 9) (x : Fin 9 → Bool) =>
        List.ofFn x ++ [!x 0, x 0 || x j]
  let target := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have word (x : Fin 9 → Bool) :
      (List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval
        ([0,j.val].map fun i => (List.ofFn x ++ [!x 0]).getD i false)] = row j x := by
    have readInput (i : Fin 9) : (List.ofFn x ++ [!x 0]).getD i.val false = x i := by
      have hil : i.val < (List.ofFn x).length := by simp
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hil,
        List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some, Fin.eta]
    rw [List.map_cons, List.map_cons, List.map_nil]
    change (List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval
      [(List.ofFn x ++ [!x 0]).getD (0 : Fin 9).val false,
        (List.ofFn x ++ [!x 0]).getD j.val false]] = row j x
    rw [readInput, readInput, List.append_assoc]
    change List.ofFn x ++ [!x 0, x 0 || (x j || false)] = _
    rw [Bool.or_false]
  by_contra hNone
  have correct : ∀ x, D.eval (row j x) = target x := by
    intro x
    by_contra h
    apply hNone
    refine ⟨x, ?_⟩
    change D.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval
      ([0,j.val].map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) ≠ target x
    rwa [word]
  by_cases hm : 2 ≤ readers D
  · have hn : j ≠ 0 := by rcases hj with h | h <;> simp [h]
    have small := many j hn D hf hs hm
    have he : (fun y : Fin 8 → Bool => D.eval
        ((List.ofFn (Fin.cons false y)) ++ [true, (Fin.cons false y : Fin 9 → Bool) j])) =
        (fun y : Fin 8 → Bool => target (Fin.cons false y)) := by
      funext y
      exact correct (Fin.cons false y)
    exact lower (he ▸ small)
  · by_cases hz : readers D = 0
    · obtain ⟨x,hx⟩ := zero j hj D hf hs hz
      exact hx (correct x)
    · have hOne : readers D = 1 := by omega
      obtain ⟨x,hx⟩ := one j hj D hf hs hOne
      exact hx (correct x)
