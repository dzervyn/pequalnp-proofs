import Mathlib.Data.Finset.Empty
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_561 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n),
    C.Computes G →
      C.outVars = ∅ ∧ ∀ j ∈ C.outGates, ∀ v : Fin n, C.gateVal {v} j = false := by
  intro n G C hC
  have hsingle : ∀ v : Fin n, C.eval {v} ≠ true := by
    intro v hv
    have hedge := (hC {v}).mp hv
    simp at hedge
  constructor
  · apply Finset.eq_empty_of_forall_notMem
    intro v hv
    apply hsingle v
    simp only [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq]
    exact Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩
  · intro j hj v
    cases hgate : C.gateVal {v} j with
    | false => rfl
    | true =>
      exfalso
      apply hsingle v
      simp only [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq]
      exact Or.inr ⟨j, hj, hgate⟩
