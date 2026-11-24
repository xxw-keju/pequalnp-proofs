import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1695 : (∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k) → ∀ (n m k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (y : Fin m → Bool), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x y) = decide (∃ j : Fin m, ∃ p ∈ L j, x p = true ∧ y j = true)) → (∑ j : Fin m, (L j).card) ≤ (6 * k + 6) * C.size + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  intro H n m k L C hpair hmono hread hk hfun
  have h := H n m C.size k L C hpair hmono hread (le_refl _) hk
    (by
      intro x Y _ hY
      rw [hfun] at hY
      obtain ⟨j, p, hp, hx, hj⟩ := of_decide_eq_true hY
      exact ⟨j, of_decide_eq_true hj, p, hp, hx⟩)
  refine le_trans ?_ h
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e : Fin n × Fin m => e.2) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.card_le_card_of_injOn (fun p => (p, j))
  · intro p hp
    have hp' : p ∈ L j := by simpa using hp
    have hacc : PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true := by
      rw [hfun]
      exact decide_eq_true ⟨j, p, hp', by simp, by simp⟩
    simp [hp', hacc]
  · intro a _ b _ hab
    exact (Prod.mk.inj hab).1
