import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1697

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_def (w : List Bool) (g : Gate) :
    step w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

def V (n : ℕ) (gs : List Gate) (k : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl step (List.ofFn x)).getD k false

lemma len (n : ℕ) (gs : List Gate) (x : Fin n → Bool) :
    (gs.foldl step (List.ofFn x)).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append]
    show (step (gs.foldl step (List.ofFn x)) g).length = _
    rw [step_def, List.length_append, ih]
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] <;>
      omega

lemma V_snoc (n : ℕ) (gs : List Gate) (g : Gate) (k : ℕ) (x : Fin n → Bool) :
    V n (gs ++ [g]) k x =
      if k = n + gs.length then g.op.eval (g.inputs.map fun i => V n gs i x) else V n gs k x := by
  unfold V
  rw [List.foldl_append]
  show (step (gs.foldl step (List.ofFn x)) g).getD k false = _
  rw [step_def]
  have hl := len n gs x
  rcases lt_trichotomy k (n + gs.length) with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi), if_neg hi.ne]
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, if_pos hi]
    subst hi
    simp
  · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, if_neg (by omega)]
    obtain ⟨k', hk⟩ : ∃ k', k - (n + gs.length) = k' + 1 := ⟨k - (n + gs.length) - 1, by omega⟩
    have e : (gs.foldl step (List.ofFn x)).getD k false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hl]; omega)]
      rfl
    rw [hk, e]
    rfl

lemma V_input (n : ℕ) (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    V n gs i.val x = x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    show (List.ofFn x).getD i.val false = x i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [i.isLt]
  | append_singleton gs g ih =>
    rw [V_snoc, if_neg (by have := i.isLt; omega), ih]

lemma V_ge (n : ℕ) (gs : List Gate) (k : ℕ) (h : n + gs.length ≤ k) (x : Fin n → Bool) :
    V n gs k x = false := by
  unfold V
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [len]; exact h)]
  rfl

lemma V_prefix (n : ℕ) (gs hs : List Gate) (k : ℕ) (x : Fin n → Bool) (h : k < n + gs.length) :
    V n (gs ++ hs) k x = V n gs k x := by
  induction hs using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton hs g ih =>
    rw [← List.append_assoc, V_snoc, if_neg (by rw [List.length_append]; omega), ih]

def U (x : Fin 9 → Bool) (i : ℕ) : Bool := (List.ofFn x).getD i false

lemma U_lt (x : Fin 9 → Bool) (i : Fin 9) : U x i.val = x i := V_input 9 [] i x

lemma U_ge (x : Fin 9 → Bool) (k : ℕ) (h : 9 ≤ k) : U x k = false :=
  V_ge 9 [] k (by simpa using h) x

def F (u : ℕ → Bool) : Bool := (u 0 && u 1) || (u 1 && u 2) || (u 2 && u 3) || (u 3 && u 4) || (u 4 && u 0) || (u 0 && u 5) || (u 1 && u 6) || (u 2 && u 7) || (u 3 && u 8) || (u 5 && u 7) || (u 6 && u 8) || (u 8 && u 5)

def auts : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 5, 8, 3, 4, 1, 7, 6, 2], [1, 0, 5, 8, 6, 2, 4, 7, 3], [1, 2, 3, 8, 6, 0, 7, 4, 5], [2, 1, 0, 5, 7, 3, 6, 4, 8], [2, 3, 8, 5, 7, 1, 4, 6, 0], [3, 2, 1, 0, 4, 8, 7, 6, 5], [3, 8, 5, 0, 4, 2, 6, 7, 1], [5, 0, 1, 2, 7, 8, 4, 6, 3], [5, 8, 3, 2, 7, 0, 6, 4, 1], [8, 3, 2, 1, 6, 5, 4, 7, 0], [8, 5, 0, 1, 6, 3, 7, 4, 2]]

def pairs : List (ℕ × ℕ) := [(0, 1), (1, 0), (0, 2), (2, 0), (0, 3), (3, 0), (0, 4), (4, 0), (0, 6), (6, 0), (4, 6), (6, 4)]

def pull (t : List ℕ) (x : Fin 9 → Bool) : Fin 9 → Bool := fun i => U x (t.getD i.val i.val)

def rel (t : List ℕ) (gs : List Gate) : List Gate :=
  gs.map fun g => ⟨g.op, g.inputs.map fun i => t.getD i i⟩

def Case (gfun : (Fin 9 → Bool) → Bool) : Prop :=
  ∀ C : Circuit, FanInTwo C →
    (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = gfun y) →
    circuitFun 9 C = (fun x : Fin 9 → Bool => F (U x)) → 16 ≤ C.size

lemma auts_len : ∀ t ∈ auts, t.length = 9 := by decide

lemma auts_lt : ∀ t ∈ auts, ∀ k : Fin 9, t.getD k.val k.val < 9 := by decide

lemma notrep : ∀ a : Fin 9, ∃ t ∈ auts, t.getD a.val a.val = 0 ∨ t.getD a.val a.val = 4 := by
  decide

lemma pairrep : ∀ a b : Fin 9, a ≠ b →
    ∃ t ∈ auts, (t.getD a.val a.val, t.getD b.val b.val) ∈ pairs := by
  decide

lemma inv : ∀ t ∈ auts, ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
    F (fun k => [a0, a1, a2, a3, a4, a5, a6, a7, a8].getD (t.getD k k) false) =
      F (fun k => [a0, a1, a2, a3, a4, a5, a6, a7, a8].getD k false) := by
  decide +kernel

lemma tfix (t : List ℕ) (hlen : t.length = 9) (k : ℕ) (hk : 9 ≤ k) : t.getD k k = k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma U_pull (t : List ℕ) (hlen : t.length = 9) (hlt : ∀ k : Fin 9, t.getD k.val k.val < 9)
    (x : Fin 9 → Bool) (k : ℕ) : U (pull t x) k = U x (t.getD k k) := by
  by_cases hk : k < 9
  · exact U_lt (pull t x) ⟨k, hk⟩
  · rw [U_ge _ k (by omega), tfix t hlen k (by omega), U_ge _ k (by omega)]

lemma F_pull (t : List ℕ) (ht : t ∈ auts) (y : Fin 9 → Bool) : F (U (pull t y)) = F (U y) := by
  have e : ∀ k, U (pull t y) k = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8].getD (t.getD k k) false :=
    fun k => U_pull t (auts_len t ht) (auts_lt t ht) y k
  calc F (U (pull t y)) = F (fun k => [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8].getD (t.getD k k) false) := by
        simp only [F, e]
    _ = F (fun k => [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8].getD k false) := inv t ht (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    _ = F (U y) := rfl

lemma V_rel (t : List ℕ) (hlen : t.length = 9) (hlt : ∀ k : Fin 9, t.getD k.val k.val < 9)
    (gs : List Gate) (x : Fin 9 → Bool) (k : ℕ) :
    V 9 (rel t gs) (t.getD k k) x = V 9 gs k (pull t x) := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => exact (U_pull t hlen hlt x k).symm
  | append_singleton gs g ih =>
    have e : rel t (gs ++ [g]) = rel t gs ++ [⟨g.op, g.inputs.map fun i => t.getD i i⟩] := by
      simp [rel]
    have hl : (rel t gs).length = gs.length := by simp [rel]
    rw [e, V_snoc, V_snoc, hl]
    by_cases hk : k = 9 + gs.length
    · rw [tfix t hlen k (by omega), if_pos hk, if_pos hk]
      show g.op.eval ((g.inputs.map fun i => t.getD i i).map fun i => V 9 (rel t gs) i x) = _
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact ih i
    · have hne : t.getD k k ≠ 9 + gs.length := by
        by_cases h9 : k < 9
        · have h := hlt ⟨k, h9⟩
          have h' : t.getD k k < 9 := h
          omega
        · rw [tfix t hlen k (by omega)]
          exact hk
      rw [if_neg hne, if_neg hk]
      exact ih k

lemma V_first (g : Gate) (gs : List Gate) (x : Fin 9 → Bool) :
    V 9 (g :: gs) 9 x = g.op.eval (g.inputs.map (U x)) := by
  have h1 : V 9 ([g] ++ gs) 9 x = V 9 [g] 9 x := V_prefix 9 [g] gs 9 x (by simp)
  have h2 : V 9 ([] ++ [g]) 9 x = g.op.eval (g.inputs.map fun i => V 9 [] i x) := by
    rw [V_snoc]
    exact if_pos rfl
  exact h1.trans h2

lemma rel_fan (t : List ℕ) (o : ℕ) (C : Circuit) (hF : FanInTwo C) :
    FanInTwo ⟨rel t C.gates, o⟩ := by
  intro g hg
  simp only [rel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have h := hF g0 hg0
  exact ⟨h.1, by simpa using h.2⟩

lemma relabel_case (C : Circuit) (hF : FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = F (U x))
    (t : List ℕ) (ht : t ∈ auts) (gfun : (Fin 9 → Bool) → Bool) (hcase : Case gfun)
    (hw9 : ∀ y, V 9 C.gates 9 (pull t y) = gfun y) : 16 ≤ C.size := by
  have hlen := auts_len t ht
  have hlt := auts_lt t ht
  have h16 := hcase ⟨rel t C.gates, t.getD C.output C.output⟩ (rel_fan t _ C hF)
    (fun y => by
      have h := V_rel t hlen hlt C.gates y 9
      rw [tfix t hlen 9 (le_refl 9)] at h
      exact h.trans (hw9 y))
    (by
      funext y
      show V 9 (rel t C.gates) (t.getD C.output C.output) y = F (U y)
      rw [V_rel t hlen hlt C.gates y C.output]
      exact (he (pull t y)).trans (F_pull t ht y))
  have hs : (⟨rel t C.gates, t.getD C.output C.output⟩ : Circuit).size = C.size := by
    show (rel t C.gates).length = C.gates.length
    simp [rel]
  omega

lemma shape (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (l : List ℕ) (hl : l.length ≤ 2)
    (hnc : ¬ ∃ c : Bool, ∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = c)
    (hni : ∀ i, i < 9 → ¬ ∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = U x i) :
    (∃ a, a < 9 ∧ ∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = !(U x a)) ∨
    (∃ a, a < 9 ∧ ∃ b, b < 9 ∧ a ≠ b ∧
      ∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = (U x a && U x b)) ∨
    (∃ a, a < 9 ∧ ∃ b, b < 9 ∧ a ≠ b ∧
      ∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = (U x a || U x b)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have cst : ∀ c : Bool, (∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = c) → False :=
    fun c h => hnc ⟨c, h⟩
  have cpy : ∀ i, (∀ x : Fin 9 → Bool, op.eval (l.map (U x)) = U x i) → False := by
    intro i h
    by_cases hi : i < 9
    · exact hni i hi h
    · exact cst false (fun x => (h x).trans (U_ge x i (by omega)))
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l'⟩⟩⟩
  · exfalso
    rcases hop with rfl | rfl | rfl
    · exact cst true (fun x => rfl)
    · exact cst false (fun x => rfl)
    · exact cst true (fun x => rfl)
  · rcases hop with rfl | rfl | rfl
    · exact (cpy a (fun x => by simp [GateOp.eval])).elim
    · exact (cpy a (fun x => by simp [GateOp.eval])).elim
    · by_cases ha : a < 9
      · exact Or.inl ⟨a, ha, fun x => rfl⟩
      · exact (cst true (fun x => by
          show (!(U x a)) = true
          rw [U_ge x a (by omega)]
          rfl)).elim
  · rcases hop with rfl | rfl | rfl
    · have e : ∀ x : Fin 9 → Bool, GateOp.and.eval ([a, b].map (U x)) = (U x a && U x b) :=
        fun x => by simp [GateOp.eval]
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · by_cases hab : a = b
          · exact (cpy a (fun x => by rw [e, hab, Bool.and_self])).elim
          · exact Or.inr (Or.inl ⟨a, ha, b, hb, hab, e⟩)
        · exact (cst false (fun x => by rw [e, U_ge x b (by omega), Bool.and_false])).elim
      · exact (cst false (fun x => by rw [e, U_ge x a (by omega), Bool.false_and])).elim
    · have e : ∀ x : Fin 9 → Bool, GateOp.or.eval ([a, b].map (U x)) = (U x a || U x b) :=
        fun x => by simp [GateOp.eval]
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · by_cases hab : a = b
          · exact (cpy a (fun x => by rw [e, hab, Bool.or_self])).elim
          · exact Or.inr (Or.inr ⟨a, ha, b, hb, hab, e⟩)
        · exact (cpy a (fun x => by rw [e, U_ge x b (by omega), Bool.or_false])).elim
      · exact (cpy b (fun x => by rw [e, U_ge x a (by omega), Bool.false_or])).elim
    · by_cases ha : a < 9
      · exact Or.inl ⟨a, ha, fun x => rfl⟩
      · exact (cst true (fun x => by
          show (!(U x a)) = true
          rw [U_ge x a (by omega)]
          rfl)).elim
  · exfalso
    simp only [List.length_cons] at hl
    omega

lemma single : ∀ o : Fin 9,
    U (fun i => decide (i = o)) o.val ≠ F (U (fun i => decide (i = o))) := by
  decide

lemma core
    (H0 : ∀ C : Circuit, IsMinimalCircuit 9 C →
      (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) →
      (∀ j : ℕ, j < C.gates.length →
        ∃ x y : Fin 9 → Bool, V 9 C.gates (9 + j) x ≠ V 9 C.gates (9 + j) y) ∧
      (∀ i j : ℕ, i < 9 + j → j < C.gates.length →
        ∃ x : Fin 9 → Bool, V 9 C.gates i x ≠ V 9 C.gates (9 + j) x))
    (HN : ∀ r, r = 0 ∨ r = 4 → Case (fun y => !(U y r)))
    (HA : ∀ p q, (p, q) ∈ pairs → Case (fun y => U y p && U y q))
    (HO : ∀ p q, (p, q) ∈ pairs → Case (fun y => U y p || U y q))
    (hcs : HasCircuitSize 9 (fun x : Fin 9 → Bool => F (U x)) 15) : False := by
  classical
  obtain ⟨C0, hF0, hs0, he0⟩ := hcs
  have hP : ∃ s, ∃ C : Circuit, FanInTwo C ∧ C.size = s ∧
      ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = F (U x) := ⟨C0.size, C0, hF0, rfl, he0⟩
  obtain ⟨C, hF, hsz, he⟩ := Nat.find_spec hP
  have hmin_le : Nat.find hP ≤ C0.size := Nat.find_min' hP ⟨C0, hF0, rfl, he0⟩
  have hsize : C.size ≤ 15 := by rw [hsz]; exact le_trans hmin_le hs0
  have hmin : IsMinimalCircuit 9 C := ⟨hF, fun D hD hDf => by
    rw [hsz]
    exact Nat.find_min' hP ⟨D, hD, rfl, fun x => (congrFun hDf x).trans (he x)⟩⟩
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y :=
    ⟨fun _ => true, fun _ => false, by
      show C.eval (List.ofFn fun _ => true) ≠ C.eval (List.ofFn fun _ => false)
      rw [he, he]
      decide⟩
  obtain ⟨h1, h2⟩ := H0 C hmin hnc
  obtain ⟨g, gs, hg⟩ : ∃ g gs, C.gates = g :: gs := by
    cases hgs : C.gates with
    | nil =>
      exfalso
      have e : ∀ x : Fin 9 → Bool, U x C.output = F (U x) := fun x => by
        have h := he x
        unfold Circuit.eval Circuit.wires at h
        rw [hgs] at h
        exact h
      by_cases ho : C.output < 9
      · exact single ⟨C.output, ho⟩ (e _)
      · have h := e (fun _ => true)
        rw [U_ge _ _ (by omega)] at h
        exact absurd h (by decide)
    | cons g gs => exact ⟨g, gs, rfl⟩
  have hgm : g ∈ C.gates := by rw [hg]; exact List.mem_cons_self
  have hlen0 : 0 < C.gates.length := by rw [hg]; simp
  have hw : ∀ x, V 9 C.gates 9 x = g.op.eval (g.inputs.map (U x)) := fun x => by
    rw [hg]
    exact V_first g gs x
  have hgF := hF g hgm
  have hnc1 : ¬ ∃ c : Bool, ∀ x : Fin 9 → Bool, g.op.eval (g.inputs.map (U x)) = c := by
    rintro ⟨c, hc⟩
    obtain ⟨x, y, hxy⟩ := h1 0 hlen0
    have hxy' : V 9 C.gates 9 x ≠ V 9 C.gates 9 y := hxy
    exact hxy' (by rw [hw x, hw y, hc x, hc y])
  have hni : ∀ i, i < 9 → ¬ ∀ x : Fin 9 → Bool, g.op.eval (g.inputs.map (U x)) = U x i := by
    intro i hi hall
    obtain ⟨x, hx⟩ := h2 i 0 (by omega) hlen0
    have hx' : V 9 C.gates i x ≠ V 9 C.gates 9 x := hx
    apply hx'
    rw [hw x, hall x]
    exact (V_input 9 C.gates ⟨i, hi⟩ x).trans (U_lt x ⟨i, hi⟩).symm
  rcases shape g.op hgF.1 g.inputs hgF.2 hnc1 hni with
    ⟨a, ha, hfa⟩ | ⟨a, ha, b, hb, hab, hfa⟩ | ⟨a, ha, b, hb, hab, hfa⟩
  · obtain ⟨t, ht, hr⟩ := notrep ⟨a, ha⟩
    have hr' : t.getD a a = 0 ∨ t.getD a a = 4 := hr
    have h16 := relabel_case C hF he t ht (fun y => !(U y (t.getD a a))) (HN _ hr')
      (fun y => by
        show V 9 C.gates 9 (pull t y) = !(U y (t.getD a a))
        rw [hw, hfa, U_pull t (auts_len t ht) (auts_lt t ht)])
    omega
  · obtain ⟨t, ht, hm⟩ := pairrep ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hab (congrArg Fin.val h))
    have hm' : (t.getD a a, t.getD b b) ∈ pairs := hm
    have h16 := relabel_case C hF he t ht (fun y => U y (t.getD a a) && U y (t.getD b b))
      (HA _ _ hm')
      (fun y => by
        show V 9 C.gates 9 (pull t y) = (U y (t.getD a a) && U y (t.getD b b))
        rw [hw, hfa, U_pull t (auts_len t ht) (auts_lt t ht),
          U_pull t (auts_len t ht) (auts_lt t ht)])
    omega
  · obtain ⟨t, ht, hm⟩ := pairrep ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hab (congrArg Fin.val h))
    have hm' : (t.getD a a, t.getD b b) ∈ pairs := hm
    have h16 := relabel_case C hF he t ht (fun y => U y (t.getD a a) || U y (t.getD b b))
      (HO _ _ hm')
      (fun y => by
        show V 9 C.gates 9 (pull t y) = (U y (t.getD a a) || U y (t.getD b b))
        rw [hw, hfa, U_pull t (auts_len t ht) (auts_lt t ht),
          U_pull t (auts_len t ht) (auts_lt t ht)])
    omega

end PEqualNP.Outside.L_meta_1697

open PEqualNP.Outside.L_meta_1697 in
theorem PEqualNP.Outside.L_meta_1697 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) → ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  intro H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 hcs
  refine core (fun C hm hn => ⟨(H0 9 C hm hn).1, (H0 9 C hm hn).2.1⟩) ?_ ?_ ?_ hcs
  · intro r hr
    rcases hr with rfl | rfl
    · exact H1
    · exact H2
  · intro p q h
    simp only [pairs, List.mem_cons, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact H3
    · exact fun C hF hw hfun => H3 C hF (fun y => (hw y).trans (Bool.and_comm _ _)) hfun
    · exact H4
    · exact fun C hF hw hfun => H4 C hF (fun y => (hw y).trans (Bool.and_comm _ _)) hfun
    · exact H5
    · exact fun C hF hw hfun => H5 C hF (fun y => (hw y).trans (Bool.and_comm _ _)) hfun
    · exact H6
    · exact fun C hF hw hfun => H6 C hF (fun y => (hw y).trans (Bool.and_comm _ _)) hfun
    · exact H7
    · exact fun C hF hw hfun => H7 C hF (fun y => (hw y).trans (Bool.and_comm _ _)) hfun
    · exact H8
    · exact fun C hF hw hfun => H8 C hF (fun y => (hw y).trans (Bool.and_comm _ _)) hfun
    · cases h
  · intro p q h
    simp only [pairs, List.mem_cons, List.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
    · exact H9
    · exact fun C hF hw hfun => H9 C hF (fun y => (hw y).trans (Bool.or_comm _ _)) hfun
    · exact H10
    · exact fun C hF hw hfun => H10 C hF (fun y => (hw y).trans (Bool.or_comm _ _)) hfun
    · exact H11
    · exact fun C hF hw hfun => H11 C hF (fun y => (hw y).trans (Bool.or_comm _ _)) hfun
    · exact H12
    · exact fun C hF hw hfun => H12 C hF (fun y => (hw y).trans (Bool.or_comm _ _)) hfun
    · exact H13
    · exact fun C hF hw hfun => H13 C hF (fun y => (hw y).trans (Bool.or_comm _ _)) hfun
    · exact H14
    · exact fun C hF hw hfun => H14 C hF (fun y => (hw y).trans (Bool.or_comm _ _)) hfun
    · cases h
