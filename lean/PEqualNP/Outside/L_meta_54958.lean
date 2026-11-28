import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54958 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100009 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.and, [6, 7]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [0, 5]⟩,
      ⟨.and, [1, 10]⟩,
      ⟨.or, [4, 11]⟩,
      ⟨.or, [2, 12]⟩,
      ⟨.not, [13]⟩,
      ⟨.and, [9, 14]⟩,
      ⟨.or, [8, 15]⟩], 16⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro gate hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  · decide +kernel
  · decide +kernel
