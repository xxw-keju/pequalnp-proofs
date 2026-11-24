import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1694 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : Fin N → ℕ), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p l : Fin N, (C.wires (List.ofFn (fun m : Fin N => decide (m = l)))).getD (c p) false = true ↔ I p l) → (∀ (p : Fin N) (y : Fin N → Bool), (Finset.univ.filter (fun m : Fin N => y m = true)).card ≤ q → (∀ l : Fin N, I p l → y l = false) → (C.wires (List.ofFn y)).getD (c p) false = false) → N * q ≤ C.size := by
  intro H q N I _ C c hq hN hdeg huniq hgates hacc hsound
  have h := H N N q (fun p => Finset.univ.filter (fun l : Fin N => I p l)) C c (fun _ => q)
    (by
      intro i j hij
      obtain ⟨l0, _, hl0⟩ := huniq i j hij
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact (hl0 a ha).trans (hl0 b hb).symm)
    (by
      intro i
      have := hdeg i
      show 2 ≤ (Finset.univ.filter (fun l : Fin N => I i l)).card
      omega)
    hgates
    (by
      intro i p
      exact (hacc i p).trans (by simp))
    (by
      intro i x hx hz
      exact hsound i x hx (fun l hl => hz l (by simp [hl])))
    (fun _ => le_refl q)
    (by
      intro i
      have := hdeg i
      show q + 1 ≤ (Finset.univ.filter (fun l : Fin N => I i l)).card
      omega)
  simpa using h
