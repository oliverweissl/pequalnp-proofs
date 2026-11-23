import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_595

open PEqualNP.CircuitLowerBounds

/-- truth table of g restricted to the point list ps; bit k = g (ps[k]) -/
def encL (g : (Fin 7 → Bool) → Bool) : List (Fin 7 → Bool) → ℕ
  | [] => 0
  | p :: ps => Nat.bit (g p) (encL g ps)

/-- gate value on encoded tables; A = encL (fun _ => true) ps is the all-ones table.
  o = 0: AND, 1: OR, 2: NOT of the first, 3: NOT of the second -/
def opv (A : ℕ) (o : Fin 4) (a b : ℕ) : ℕ :=
  match o with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => A ^^^ a
  | 3 => A ^^^ b

def kept (k : Bool) (x : ℕ) (xs : List ℕ) : List ℕ := if k then x :: xs else xs

/-- Run T A s L: from the live multiset L, s more gates suffice to reach [T] (forward direction). -/
inductive Run (T A : ℕ) : ℕ → List ℕ → Prop
  | done (s : ℕ) : Run T A s [T]
  | perm {s : ℕ} {L₁ L₂ : List ℕ} : L₁.Perm L₂ → Run T A s L₁ → Run T A s L₂
  | mono {s : ℕ} {L : List ℕ} : Run T A s L → Run T A (s + 1) L
  | two {s a b : ℕ} {r : List ℕ} (o : Fin 4) (ka kb : Bool) :
      Run T A s (opv A o a b :: kept ka a (kept kb b r)) → Run T A (s + 1) (a :: b :: r)
  | one {s a w : ℕ} {r : List ℕ} (ka : Bool) : (w = a ∨ w = A ^^^ a ∨ w = 0 ∨ w = A) →
      Run T A s (w :: kept ka a r) → Run T A (s + 1) (a :: r)
  | const {s w : ℕ} {r : List ℕ} : (w = 0 ∨ w = A) → Run T A s (w :: r) → Run T A (s + 1) r

/-- encoded input variable i -/
def Xv (ps : List (Fin 7 → Bool)) (i : ℕ) : ℕ :=
  encL (fun x => if h : i < 7 then x ⟨i, h⟩ else false) ps


theorem encL_and (g h : (Fin 7 → Bool) → Bool) : ∀ l : List (Fin 7 → Bool),
    encL (fun x => g x && h x) l = encL g l &&& encL h l
  | [] => by simp [encL]
  | p :: ps => by simp only [encL, Nat.land_bit, encL_and g h ps]

theorem encL_or (g h : (Fin 7 → Bool) → Bool) : ∀ l : List (Fin 7 → Bool),
    encL (fun x => g x || h x) l = encL g l ||| encL h l
  | [] => by simp [encL]
  | p :: ps => by simp only [encL, Nat.lor_bit, encL_or g h ps]

theorem encL_false : ∀ l : List (Fin 7 → Bool), encL (fun _ => false) l = 0
  | [] => rfl
  | p :: ps => by simp only [encL, encL_false ps]; rfl

theorem encL_not (g : (Fin 7 → Bool) → Bool) : ∀ l : List (Fin 7 → Bool),
    encL (fun x => !g x) l = encL (fun _ => true) l ^^^ encL g l
  | [] => by simp [encL]
  | p :: ps => by
    simp only [encL, Nat.xor_bit, encL_not g ps]
    congr 1
    cases g p <;> rfl

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_pre : ∀ (gs : List Gate) (x : List Bool), ∃ ys,
    gs.foldl stp x = x ++ ys ∧ ys.length = gs.length
  | [], x => ⟨[], by simp⟩
  | g :: gs, x => by
    obtain ⟨ys, h1, h2⟩ := foldl_pre gs (stp x g)
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: ys, ?_, by simp [h2]⟩
    rw [List.foldl_cons, h1]
    simp [stp]

theorem foldl_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (gs.foldl stp x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < x.length + j then (gs.foldl stp x).getD i false
        else false) := by
  have hj : j < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
    rw [List.getElem?_eq_getElem hj] at hg
    cases hg
    rfl
  obtain ⟨ys, h1, h2⟩ := foldl_pre (gs.take j) x
  have hlen : (x ++ ys).length = x.length + j := by
    simp [h2, List.length_take]
    omega
  generalize hw : x ++ ys = w at h1 hlen
  obtain ⟨zs, h3, _⟩ := foldl_pre (gs.drop (j + 1)) (stp w g)
  generalize hv : g.op.eval (g.inputs.map fun i => w.getD i false) = v
  have hfin : gs.foldl stp x = w ++ ([v] ++ zs) := by
    rw [hsplit, List.foldl_append, h1, List.foldl_cons, h3, ← hv]
    simp [stp]
  rw [hfin, ← hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  show v = _
  rw [← hv]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length
  · rw [if_pos hi, List.getD_append _ _ _ _ hi]
  · rw [if_neg hi]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨ys, h1, h2⟩ := foldl_pre C.gates x
  rw [wires_eq, h1]
  simp [h2]

def W (C : Circuit) (i : ℕ) (x : Fin 7 → Bool) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (C : Circuit) (i : ℕ) (hi : i < 7) (x : Fin 7 → Bool) : W C i x = x ⟨i, hi⟩ := by
  obtain ⟨ys, h1, _⟩ := foldl_pre C.gates (List.ofFn x)
  rw [W, wires_eq, h1, List.getD_append _ _ _ _ (by simp [hi])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

theorem W_gate (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (x : Fin 7 → Bool) :
    W C (7 + j) x = g.op.eval (g.inputs.map fun i => if i < 7 + j then W C i x else false) := by
  have := foldl_gate C.gates (List.ofFn x) j g hg
  simp only [List.length_ofFn] at this
  simp only [W, wires_eq]
  exact this

def val (ps : List (Fin 7 → Bool)) (C : Circuit) (i : ℕ) : ℕ := encL (W C i) ps

theorem val_input (ps : List (Fin 7 → Bool)) (C : Circuit) (i : ℕ) (hi : i < 7) :
    val ps C i = Xv ps i := by
  unfold val Xv
  congr 1
  funext x
  rw [W_input C i hi, dif_pos hi]

theorem enc_rd (ps : List (Fin 7 → Bool)) (C : Circuit) (t i : ℕ) :
    encL (fun x => if i < 7 + t then W C i x else false) ps = if i < 7 + t then val ps C i else 0 := by
  by_cases h : i < 7 + t
  · simp only [h, if_true]; rfl
  · simp only [h, if_false]; exact encL_false _

theorem val_gate (ps : List (Fin 7 → Bool)) (C : Circuit) (t : ℕ) (g : Gate)
    (hg : C.gates[t]? = some g) :
    val ps C (7 + t) = encL (fun x => g.op.eval
      (g.inputs.map fun i => if i < 7 + t then W C i x else false)) ps := by
  unfold val
  congr 1
  funext x
  exact W_gate C t g hg x

def gIn (C : Circuit) (t : ℕ) : Finset ℕ :=
  match C.gates[t]? with
  | some g => (g.inputs.filter (fun i => decide (i < 7 + t))).toFinset
  | none => ∅

theorem mem_gIn {C : Circuit} {t : ℕ} {g : Gate} (hg : C.gates[t]? = some g) (w : ℕ) :
    w ∈ gIn C t ↔ w ∈ g.inputs ∧ w < 7 + t := by
  unfold gIn
  rw [hg]
  simp

def need (C : Circuit) : ℕ → Finset ℕ
  | 0 => {C.output}
  | d + 1 =>
    if 7 + (C.gates.length - (d + 1)) ∈ need C d then
      (need C d).erase (7 + (C.gates.length - (d + 1))) ∪ gIn C (C.gates.length - (d + 1))
    else need C d

noncomputable def St (ps : List (Fin 7 → Bool)) (C : Circuit) (d : ℕ) : List ℕ :=
  (need C d).toList.map (val ps C)

theorem need_bound (C : Circuit) (ho : C.output < 7 + C.gates.length) :
    ∀ d, d ≤ C.gates.length → ∀ w ∈ need C d, w < 7 + (C.gates.length - d)
  | 0, _, w, hw => by
    simp only [need, Finset.mem_singleton] at hw
    omega
  | d + 1, hd, w, hw => by
    have ih := need_bound C ho d (by omega)
    unfold need at hw
    split at hw
    · rw [Finset.mem_union, Finset.mem_erase] at hw
      rcases hw with ⟨h1, h2⟩ | h
      · have := ih w h2
        omega
      · unfold gIn at h
        split at h
        · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h
          omega
        · simp at h
    · rename_i hn
      have := ih w hw
      have : w ≠ 7 + (C.gates.length - (d + 1)) := fun e => hn (e ▸ hw)
      omega

theorem mem_kept {k : Bool} {x v : ℕ} {xs : List ℕ} (h : v ∈ kept k x xs) : v = x ∨ v ∈ xs := by
  cases k
  · exact Or.inr h
  · simpa [kept] using h

theorem mem_kept_iff {k : Bool} {x v : ℕ} {xs : List ℕ} :
    v ∈ kept k x xs ↔ (k = true ∧ v = x) ∨ v ∈ xs := by
  cases k <;> simp [kept]

theorem map_kept (f : ℕ → ℕ) (k : Bool) (x : ℕ) (xs : List ℕ) :
    (kept k x xs).map f = kept k (f x) (xs.map f) := by
  cases k <;> rfl

theorem toL_perm {A : Finset ℕ} {L : List ℕ} (hL : L.Nodup) (h : ∀ w, w ∈ A ↔ w ∈ L) :
    A.toList.Perm L :=
  (List.perm_ext_iff_of_nodup (Finset.nodup_toList A) hL).2
    (fun w => by rw [Finset.mem_toList]; exact h w)

theorem H0 {T AA d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {w : ℕ} (hI : ∀ x, x ∉ I)
    (hw : w = 0 ∨ w = AA) (h : Run T AA d (w :: A.toList.map f)) :
    Run T AA (d + 1) ((A ∪ I).toList.map f) := by
  have e : A ∪ I = A := by
    ext x
    simp [hI x]
  rw [e]
  exact Run.const hw h

theorem H1 {T AA d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {a w : ℕ} (hI : ∀ x, x ∈ I ↔ x = a)
    (hw : w = f a ∨ w = AA ^^^ f a ∨ w = 0 ∨ w = AA) (h : Run T AA d (w :: A.toList.map f)) :
    Run T AA (d + 1) ((A ∪ I).toList.map f) := by
  by_cases ha : a ∈ A
  · have p1 : A.toList.Perm (a :: (A.erase a).toList) := by
      apply toL_perm (List.nodup_cons.2 ⟨by simp, Finset.nodup_toList _⟩)
      intro x
      simp only [List.mem_cons, Finset.mem_toList, Finset.mem_erase]
      constructor
      · intro hx
        by_cases e : x = a
        · exact Or.inl e
        · exact Or.inr ⟨e, hx⟩
      · rintro (rfl | ⟨_, hx⟩)
        · exact ha
        · exact hx
    have p2 : (A ∪ I).toList.Perm (a :: (A.erase a).toList) := by
      refine List.Perm.trans ?_ p1
      have e : A ∪ I = A := by
        ext x
        rw [Finset.mem_union, hI]
        constructor
        · rintro (h | rfl)
          · exact h
          · exact ha
        · exact Or.inl
      rw [e]
    have q : Run T AA d (w :: kept true (f a) ((A.erase a).toList.map f)) := by
      refine Run.perm ?_ h
      have := (p1.map f).cons w
      simpa [kept] using this
    have r := Run.one (r := (A.erase a).toList.map f) true hw q
    exact Run.perm ((p2.map f).symm) (by simpa using r)
  · have p2 : (A ∪ I).toList.Perm (a :: A.toList) := by
      apply toL_perm (List.nodup_cons.2 ⟨by simp [ha], Finset.nodup_toList _⟩)
      intro x
      rw [Finset.mem_union, hI, List.mem_cons, Finset.mem_toList]
      tauto
    have r := Run.one (r := A.toList.map f) false hw (by simpa [kept] using h)
    exact Run.perm ((p2.map f).symm) (by simpa using r)

theorem H2 {T AA d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (o : Fin 4) (hab : a ≠ b)
    (hI : ∀ x, x ∈ I ↔ x = a ∨ x = b)
    (h : Run T AA d (opv AA o (f a) (f b) :: A.toList.map f)) :
    Run T AA (d + 1) ((A ∪ I).toList.map f) := by
  let Rs := (A.erase a).erase b
  have hR : ∀ x, x ∈ Rs ↔ x ∈ A ∧ x ≠ a ∧ x ≠ b := by
    intro x
    simp only [Rs, Finset.mem_erase]
    tauto
  have nR : Rs.toList.Nodup := Finset.nodup_toList _
  have p1 : A.toList.Perm (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b Rs.toList)) := by
    have n1 : (kept (decide (b ∈ A)) b Rs.toList).Nodup := by
      cases hb : decide (b ∈ A)
      · exact nR
      · exact List.nodup_cons.2 ⟨by rw [Finset.mem_toList, hR]; tauto, nR⟩
    have n2 : (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b Rs.toList)).Nodup := by
      cases ha : decide (a ∈ A)
      · exact n1
      · refine List.nodup_cons.2 ⟨?_, n1⟩
        intro hm
        rcases mem_kept hm with e | hm
        · exact hab e
        · rw [Finset.mem_toList, hR] at hm
          exact hm.2.1 rfl
    apply toL_perm n2
    intro x
    simp only [mem_kept_iff, decide_eq_true_eq, Finset.mem_toList, hR]
    constructor
    · intro hx
      by_cases e1 : x = a
      · exact Or.inl ⟨e1 ▸ hx, e1⟩
      by_cases e2 : x = b
      · exact Or.inr (Or.inl ⟨e2 ▸ hx, e2⟩)
      exact Or.inr (Or.inr ⟨hx, e1, e2⟩)
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, _⟩) <;> exact h1
  have p2 : (A ∪ I).toList.Perm (a :: b :: Rs.toList) := by
    have hn : (a :: b :: Rs.toList).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, nR⟩⟩
      · simp only [List.mem_cons, Finset.mem_toList, hR]
        tauto
      · simp only [Finset.mem_toList, hR]
        tauto
    apply toL_perm hn
    intro x
    simp only [Finset.mem_union, hI, List.mem_cons, Finset.mem_toList, hR]
    tauto
  have q : Run T AA d (opv AA o (f a) (f b) :: kept (decide (a ∈ A)) (f a)
      (kept (decide (b ∈ A)) (f b) (Rs.toList.map f))) := by
    refine Run.perm ?_ h
    have := (p1.map f).cons (opv AA o (f a) (f b))
    simpa [map_kept] using this
  have r := Run.two o _ _ q
  exact Run.perm ((p2.map f).symm) (by simpa using r)

theorem eval_and2 (b1 b2 : Bool) : GateOp.eval GateOp.and [b1, b2] = (b1 && b2) := by
  cases b1 <;> cases b2 <;> rfl
theorem eval_or2 (b1 b2 : Bool) : GateOp.eval GateOp.or [b1, b2] = (b1 || b2) := by
  cases b1 <;> cases b2 <;> rfl
theorem eval_and1 (b : Bool) : GateOp.eval GateOp.and [b] = b := by cases b <;> rfl
theorem eval_or1 (b : Bool) : GateOp.eval GateOp.or [b] = b := by cases b <;> rfl
theorem eval_not_cons (b : Bool) (l : List Bool) : GateOp.eval GateOp.not (b :: l) = !b := rfl

theorem rd_enc (ps : List (Fin 7 → Bool)) (C : Circuit) (t i : ℕ) (hi : i < 7 + t) :
    encL (fun x => if i < 7 + t then W C i x else false) ps = val ps C i := by
  rw [enc_rd, if_pos hi]

theorem rd_enc0 (ps : List (Fin 7 → Bool)) (C : Circuit) (t i : ℕ) (hi : ¬ i < 7 + t) :
    encL (fun x => if i < 7 + t then W C i x else false) ps = 0 := by
  rw [enc_rd, if_neg hi]

theorem opv_aa (AA a : ℕ) (o : Fin 4) :
    opv AA o a a = a ∨ opv AA o a a = AA ^^^ a ∨ opv AA o a a = 0 ∨ opv AA o a a = AA := by
  fin_cases o <;> simp [opv]

theorem opv_a0 (AA a : ℕ) (o : Fin 4) :
    opv AA o a 0 = a ∨ opv AA o a 0 = AA ^^^ a ∨ opv AA o a 0 = 0 ∨ opv AA o a 0 = AA := by
  fin_cases o <;> simp [opv]

theorem opv_0b (AA b : ℕ) (o : Fin 4) :
    opv AA o 0 b = b ∨ opv AA o 0 b = AA ^^^ b ∨ opv AA o 0 b = 0 ∨ opv AA o 0 b = AA := by
  fin_cases o <;> simp [opv]

theorem opv_00 (AA : ℕ) (o : Fin 4) : opv AA o 0 0 = 0 ∨ opv AA o 0 0 = AA := by
  fin_cases o <;> simp [opv]

theorem fin2 (ps : List (Fin 7 → Bool)) (T : ℕ) (C : Circuit) {t d : ℕ} {A : Finset ℕ}
    {i i2 : ℕ} (o : Fin 4)
    (hI : ∀ x, x ∈ gIn C t ↔ (x = i ∨ x = i2) ∧ x < 7 + t)
    (ho : val ps C (7 + t) = opv (encL (fun _ => true) ps) o
      (encL (fun x => if i < 7 + t then W C i x else false) ps)
      (encL (fun x => if i2 < 7 + t then W C i2 x else false) ps))
    (h : Run T (encL (fun _ => true) ps) d (val ps C (7 + t) :: A.toList.map (val ps C))) :
    Run T (encL (fun _ => true) ps) (d + 1) ((A ∪ gIn C t).toList.map (val ps C)) := by
  by_cases h1 : i < 7 + t <;> by_cases h2 : i2 < 7 + t
  · rw [rd_enc ps C t i h1, rd_enc ps C t i2 h2] at ho
    by_cases h12 : i = i2
    · subst h12
      refine H1 (a := i) (fun x => ?_) ?_ h
      · rw [hI]
        constructor
        · rintro ⟨rfl | rfl, _⟩ <;> rfl
        · rintro rfl
          exact ⟨Or.inl rfl, h1⟩
      · rw [ho]
        exact opv_aa _ _ o
    · refine H2 o h12 (fun x => ?_) (by rw [← ho]; exact h)
      rw [hI]
      constructor
      · exact fun h' => h'.1
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, h1⟩
        · exact ⟨Or.inr rfl, h2⟩
  · rw [rd_enc ps C t i h1, rd_enc0 ps C t i2 h2] at ho
    refine H1 (a := i) (fun x => ?_) ?_ h
    · rw [hI]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd hx h2
      · rintro rfl
        exact ⟨Or.inl rfl, h1⟩
    · rw [ho]
      exact opv_a0 _ _ o
  · rw [rd_enc0 ps C t i h1, rd_enc ps C t i2 h2] at ho
    refine H1 (a := i2) (fun x => ?_) ?_ h
    · rw [hI]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact absurd hx h1
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h2⟩
    · rw [ho]
      exact opv_0b _ _ o
  · rw [rd_enc0 ps C t i h1, rd_enc0 ps C t i2 h2] at ho
    refine H0 (fun x hx => ?_) ?_ h
    · rw [hI] at hx
      rcases hx with ⟨rfl | rfl, hx⟩
      · exact h1 hx
      · exact h2 hx
    · rw [ho]
      exact opv_00 _ o

theorem gate_step (ps : List (Fin 7 → Bool)) (T : ℕ) (C : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) {t d : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) {A : Finset ℕ}
    (h : Run T (encL (fun _ => true) ps) d (val ps C (7 + t) :: A.toList.map (val ps C))) :
    Run T (encL (fun _ => true) ps) (d + 1) ((A ∪ gIn C t).toList.map (val ps C)) := by
  have hmem : g ∈ C.gates := List.mem_of_getElem? hg
  obtain ⟨hop, hlen⟩ := hF g hmem
  have hop3 : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using hop
  have hv := val_gate ps C t g hg
  have hI := mem_gIn hg
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
  · rw [hin] at hv hI
    refine H0 (fun x hx => by simp [hI] at hx) ?_ h
    rw [hv]
    rcases hop3 with e | e | e <;> rw [e]
    · right; rfl
    · left; exact encL_false ps
    · right; rfl
  · rw [hin] at hv hI
    simp only [List.map_cons, List.map_nil] at hv
    have hI2 : ∀ x, x ∈ gIn C t ↔ (x = i ∨ x = i) ∧ x < 7 + t := by
      intro x
      rw [hI]
      simp
    rcases hop3 with e | e | e
    · refine fin2 ps T C (i := i) (i2 := i) 0 hI2 ?_ h
      rw [hv, e]
      simp only [eval_and1]
      simp [opv]
    · refine fin2 ps T C (i := i) (i2 := i) 1 hI2 ?_ h
      rw [hv, e]
      simp only [eval_or1]
      simp [opv]
    · refine fin2 ps T C (i := i) (i2 := i) 2 hI2 ?_ h
      rw [hv, e]
      simp only [eval_not_cons]
      exact encL_not _ ps
  · rw [hin] at hv hI
    simp only [List.map_cons, List.map_nil] at hv
    have hI2 : ∀ x, x ∈ gIn C t ↔ (x = i ∨ x = i2) ∧ x < 7 + t := by
      intro x
      rw [hI]
      simp
    rcases hop3 with e | e | e
    · refine fin2 ps T C 0 hI2 ?_ h
      rw [hv, e]
      simp only [eval_and2]
      exact encL_and _ _ ps
    · refine fin2 ps T C 1 hI2 ?_ h
      rw [hv, e]
      simp only [eval_or2]
      exact encL_or _ _ ps
    · refine fin2 ps T C 2 hI2 ?_ h
      rw [hv, e]
      simp only [eval_not_cons]
      exact encL_not _ ps
  · rw [hin] at hlen
    simp at hlen

theorem run_need (ps : List (Fin 7 → Bool)) (T : ℕ) (C : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo C) (hT : val ps C C.output = T) :
    ∀ d, d ≤ C.gates.length → Run T (encL (fun _ => true) ps) d (St ps C d)
  | 0, _ => by
    have : St ps C 0 = [T] := by
      simp [St, need, hT]
    rw [this]
    exact Run.done 0
  | d + 1, hd => by
    have ih := run_need ps T C hF hT d (by omega)
    have ht : C.gates.length - (d + 1) < C.gates.length := by omega
    have hg := List.getElem?_eq_getElem ht
    unfold St need
    split
    · rename_i hin
      set t := C.gates.length - (d + 1)
      have p : (need C d).toList.Perm ((7 + t) :: ((need C d).erase (7 + t)).toList) := by
        conv_lhs => rw [← Finset.insert_erase hin]
        exact Finset.toList_insert (Finset.notMem_erase _ _)
      have h1 : Run T (encL (fun _ => true) ps) d
          (val ps C (7 + t) :: ((need C d).erase (7 + t)).toList.map (val ps C)) := by
        have := Run.perm (p.map (val ps C)) ih
        simpa using this
      exact gate_step ps T C hF hg h1
    · exact Run.mono ih

theorem reduce (ps : List (Fin 7 → Bool)) (f : (Fin 7 → Bool) → Bool) (x0 : Fin 7 → Bool)
    (hx0 : f x0 = true) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hf : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ S : List ℕ, S.Sublist ((List.range 7).map (Xv ps)) ∧
      Run (encL f ps) (encL (fun _ => true) ps) C.gates.length S := by
  have hev : ∀ x, C.eval (List.ofFn x) = W C C.output x := fun x => rfl
  have ho : C.output < 7 + C.gates.length := by
    by_contra hc
    have h1 := hf x0
    rw [hx0, hev, W, List.getD_eq_default _ _ (by rw [wires_len, List.length_ofFn]; omega)] at h1
    cases h1
  have hT : val ps C C.output = encL f ps := by
    unfold val
    congr 1
    funext x
    rw [← hev]
    exact hf x
  have hrun := run_need ps (encL f ps) C hC hT C.gates.length le_rfl
  have hb := need_bound C ho C.gates.length le_rfl
  let S := (List.range 7).filter (fun i => decide (i ∈ need C C.gates.length))
  have p : (need C C.gates.length).toList.Perm S := by
    apply toL_perm (List.Nodup.filter _ List.nodup_range)
    intro w
    constructor
    · intro hw
      have := hb w hw
      exact List.mem_filter.2 ⟨List.mem_range.2 (by omega), decide_eq_true hw⟩
    · intro hw
      exact of_decide_eq_true (List.mem_filter.1 hw).2
  have hmap : S.map (val ps C) = S.map (Xv ps) :=
    List.map_congr_left (fun i hi => val_input ps C i (List.mem_range.1 (List.mem_filter.1 hi).1))
  refine ⟨S.map (Xv ps), (List.filter_sublist).map (Xv ps), ?_⟩
  rw [← hmap]
  exact Run.perm (p.map (val ps C)) hrun


/-! ## Part B (lead): invariant, certificate, main theorem -/

def EL : List (ℕ × ℕ) := [(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)]

def fE (x : Fin 7 → Bool) : Bool :=
  decide (∃ u v : Fin 7, (u.val, v.val) ∈ EL ∧ x u = true ∧ x v = true)

def pts : List (Fin 7 → Bool) := (List.range 128).map fun k => fun i => k.testBit i.val

def AA : ℕ := 340282366920938463463374607431768211455

def TT : ℕ := 0xffffffffffeceeecffffeae8ffe8eae8
def XX : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def FP : List ℕ := [18, 33, 76, 42, 81, 84, 44]
def FPM : List ℕ := [0x40000, 0x200000000, 0x10000000000000000000, 0x40000000000, 0x200000000000000000000, 0x1000000000000000000000, 0x100000000000]
def SG : List ℕ := [0, 2, 1, 3, 4, 6, 5, 7, 64, 66, 65, 67, 68, 70, 69, 71, 32, 34, 33, 35, 36, 38, 37, 39, 96, 98, 97, 99, 100, 102, 101, 103, 16, 18, 17, 19, 20, 22, 21, 23, 80, 82, 81, 83, 84, 86, 85, 87, 48, 50, 49, 51, 52, 54, 53, 55, 112, 114, 113, 115, 116, 118, 117, 119, 8, 10, 9, 11, 12, 14, 13, 15, 72, 74, 73, 75, 76, 78, 77, 79, 40, 42, 41, 43, 44, 46, 45, 47, 104, 106, 105, 107, 108, 110, 109, 111, 24, 26, 25, 27, 28, 30, 29, 31, 88, 90, 89, 91, 92, 94, 93, 95, 56, 58, 57, 59, 60, 62, 61, 63, 120, 122, 121, 123, 124, 126, 125, 127]


theorem AA_eq : AA = 2 ^ 128 - 1 := by decide

theorem AA_bit {k : ℕ} (hk : k < 128) : AA.testBit k = true := by
  rw [AA_eq, Nat.testBit_two_pow_sub_one]
  simpa using hk

theorem TT_lt : TT < 2 ^ 128 := by decide

theorem TT_bit {k : ℕ} (h : TT.testBit k = true) : k < 128 := by
  by_contra hk
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le TT_lt (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
  cases h

def opb : Fin 4 → Bool → Bool → Bool
  | 0, x, y => x && y
  | 1, x, y => x || y
  | 2, x, _ => !x
  | 3, _, y => !y

theorem opv_bit (o : Fin 4) (a b : ℕ) {k : ℕ} (hk : k < 128) :
    (opv AA o a b).testBit k = opb o (a.testBit k) (b.testBit k) := by
  have hA := AA_bit hk
  fin_cases o <;> simp [opv, opb, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hA]

theorem xor_bit (a : ℕ) {k : ℕ} (hk : k < 128) : (AA ^^^ a).testBit k = !a.testBit k := by
  simp [Nat.testBit_xor, AA_bit hk]

theorem opb_diff : ∀ (o : Fin 4) (x1 y1 x2 y2 : Bool), opb o x1 y1 ≠ opb o x2 y2 → x1 ≠ x2 ∨ y1 ≠ y2 := by
  decide

/-! ### Separation -/

def Cov (L : List ℕ) : Prop :=
  ∀ t u, t < 128 → u < 128 → TT.testBit t = true → TT.testBit u = false →
    ∃ v ∈ L, v.testBit t ≠ v.testBit u

theorem Cov.perm {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) (h : Cov L₁) : Cov L₂ := by
  intro t u ht hu h1 h2
  obtain ⟨v, hv, hne⟩ := h t u ht hu h1 h2
  exact ⟨v, p.subset hv, hne⟩

def sepm (u : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (if v.testBit u then AA ^^^ v else v) ||| sepm u vs

theorem sepm_bit (u t : ℕ) (ht : t < 128) : ∀ L : List ℕ, (∃ v ∈ L, v.testBit t ≠ v.testBit u) →
    (sepm u L).testBit t = true
  | [], ⟨v, hv, _⟩ => by simp at hv
  | x :: xs, ⟨v, hv, hne⟩ => by
    unfold sepm
    rw [Nat.testBit_or]
    rcases List.mem_cons.1 hv with rfl | hv
    · split
      · rename_i hu
        rw [xor_bit _ ht]
        rw [hu] at hne
        simp [hne]
      · rename_i hu
        simp only [Bool.not_eq_true] at hu
        rw [hu] at hne
        simp only [ne_eq, Bool.not_eq_false] at hne
        simp [hne]
    · rw [sepm_bit u t ht xs ⟨v, hv, hne⟩, Bool.or_true]

def sepk (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (if Nat.beq (v &&& m) 0 then v else AA ^^^ v) ||| sepk m vs

theorem beq_mask (v u : ℕ) : Nat.beq (v &&& 2 ^ u) 0 = !v.testBit u := by
  rw [Nat.and_two_pow]
  cases v.testBit u
  · simp
  · simp only [Bool.toNat_true, one_mul, Bool.not_true]
    cases h : Nat.beq (2 ^ u) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) (by positivity)

theorem sepk_eq (u : ℕ) : ∀ L : List ℕ, sepk (2 ^ u) L = sepm u L
  | [] => rfl
  | v :: vs => by
    unfold sepk sepm
    rw [beq_mask, sepk_eq u vs]
    cases v.testBit u <;> rfl

def covB (L : List ℕ) : Bool := FPM.all fun m => Nat.beq (sepk m L &&& TT) TT

theorem fp_ok : ∀ u ∈ FP, u < 128 ∧ TT.testBit u = false := by decide

theorem fpm_eq : FPM = FP.map (fun u => 2 ^ u) := by decide

theorem covB_of_cov {L : List ℕ} (h : Cov L) : covB L = true := by
  unfold covB
  rw [List.all_eq_true, fpm_eq]
  intro m hm
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
  obtain ⟨hu1, hu2⟩ := fp_ok u hu
  rw [sepk_eq, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and]
  cases htt : TT.testBit t
  · simp
  · have ht := TT_bit htt
    rw [sepm_bit u t ht L (h t u ht hu1 htt hu2)]
    rfl

/-! ### The read-once witness invariant for tight states -/

def d4 (a1 b1 a2 b2 a3 b3 a4 b4 : Bool) : Bool :=
  !(a1 == a2 && b1 == b2) && !(a1 == a3 && b1 == b3) && !(a1 == a4 && b1 == b4) &&
  !(a2 == a3 && b2 == b3) && !(a2 == a4 && b2 == b4) && !(a3 == a4 && b3 == b4)

theorem d4_swap : ∀ a1 b1 a2 b2 a3 b3 a4 b4 : Bool,
    d4 a1 b1 a2 b2 a3 b3 a4 b4 = d4 b1 a1 b2 a2 b3 a3 b4 a4 := by decide

def piB (o : Fin 4) (x : Bool) : Bool := if o = 2 then !x else x

theorem key1 : ∀ (o : Fin 4) (a1 b1 a2 b2 a3 b3 a4 b4 : Bool), d4 a1 b1 a2 b2 a3 b3 a4 b4 = true →
    opb o a1 b1 ≠ opb o a2 b2 → opb o a1 b1 ≠ opb o a3 b3 → opb o a1 b1 ≠ opb o a4 b4 →
    (o = 0 ∧ a1 = true ∧ b1 = true) ∨ (o = 1 ∧ a1 = false ∧ b1 = false) := by decide

theorem key2 : ∀ (o : Fin 4) (β a1 b1 a2 b2 a3 b3 a4 b4 : Bool), d4 a1 b1 a2 b2 a3 b3 a4 b4 = true →
    (opb o a1 β ≠ opb o a2 β ∨ b1 ≠ b2) → (opb o a1 β ≠ opb o a3 β ∨ b1 ≠ b3) →
    (opb o a1 β ≠ opb o a4 β ∨ b1 ≠ b4) →
    d4 (opb o a1 β) b1 (opb o a2 β) b2 (opb o a3 β) b3 (opb o a4 β) b4 = true ∧
    opb o a1 β = piB o a1 := by decide

theorem piB_ne : ∀ (o : Fin 4) (x y z w : Bool), (piB o x != piB o y || z != w) = (x != y || z != w) := by
  decide

def cst (r : List ℕ) (p1 p2 p3 p4 : ℕ) : Prop :=
  ∀ v ∈ r, v.testBit p2 = v.testBit p1 ∧ v.testBit p3 = v.testBit p1 ∧ v.testBit p4 = v.testBit p1

def BadAt (a b : ℕ) (r : List ℕ) (p1 p2 p3 p4 q1 q2 q3 q4 : ℕ) : Prop :=
  (p1 < 128 ∧ p2 < 128 ∧ p3 < 128 ∧ p4 < 128 ∧ q1 < 128 ∧ q2 < 128 ∧ q3 < 128 ∧ q4 < 128) ∧
  cst r p1 p2 p3 p4 ∧ cst r q1 q2 q3 q4 ∧
  d4 (a.testBit p1) (b.testBit p1) (a.testBit p2) (b.testBit p2) (a.testBit p3) (b.testBit p3)
    (a.testBit p4) (b.testBit p4) = true ∧
  d4 (a.testBit q1) (b.testBit q1) (a.testBit q2) (b.testBit q2) (a.testBit q3) (b.testBit q3)
    (a.testBit q4) (b.testBit q4) = true ∧
  (TT.testBit p1 = true ∧ TT.testBit p2 = false ∧ TT.testBit p3 = false ∧ TT.testBit p4 = false) ∧
  (TT.testBit q1 = false ∧ TT.testBit q2 = true ∧ TT.testBit q3 = true ∧ TT.testBit q4 = true) ∧
  (a.testBit p1 != a.testBit q1 || b.testBit p1 != b.testBit q1) = true

def Bad (a b : ℕ) (r : List ℕ) : Prop :=
  ∃ p1 p2 p3 p4 q1 q2 q3 q4 : ℕ, BadAt a b r p1 p2 p3 p4 q1 q2 q3 q4

def ROk (L : List ℕ) : Prop := ∀ a b r, L.Perm (a :: b :: r) → ¬ Bad a b r

theorem cst_sub {r r' : List ℕ} (hs : ∀ v ∈ r', v ∈ r) {p1 p2 p3 p4 : ℕ} (h : cst r p1 p2 p3 p4) :
    cst r' p1 p2 p3 p4 := fun v hv => h v (hs v hv)

theorem Bad.sub {a b : ℕ} {r r' : List ℕ} (hs : ∀ v ∈ r', v ∈ r) (h : Bad a b r) : Bad a b r' := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cP, cQ, h3⟩ := h
  exact ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cst_sub hs cP, cst_sub hs cQ, h3⟩

theorem Bad.swap {a b : ℕ} {r : List ℕ} (h : Bad a b r) : Bad b a r := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cP, cQ, dP, dQ, tP, tQ, hx⟩ := h
  refine ⟨p1, p2, p3, p4, q1, q2, q3, q4, hl, cP, cQ, ?_, ?_, tP, tQ, ?_⟩
  · rw [← d4_swap]; exact dP
  · rw [← d4_swap]; exact dQ
  · rw [Bool.or_comm]; exact hx

theorem gate_diff {o : Fin 4} {a b : ℕ} {r : List ℕ} (hc : Cov (opv AA o a b :: r)) {t u : ℕ}
    (ht : t < 128) (hu : u < 128) (htt : TT.testBit t = true) (huu : TT.testBit u = false)
    (hcu : ∀ v ∈ r, v.testBit t = v.testBit u) :
    opb o (a.testBit t) (b.testBit t) ≠ opb o (a.testBit u) (b.testBit u) := by
  obtain ⟨v, hv, hne⟩ := hc t u ht hu htt huu
  rcases List.mem_cons.1 hv with rfl | hv
  · rwa [opv_bit _ _ _ ht, opv_bit _ _ _ hu] at hne
  · exact absurd (hcu v hv) hne

theorem bad_gate (o : Fin 4) {a b : ℕ} {r : List ℕ} (hc : Cov (opv AA o a b :: r)) (h : Bad a b r) :
    False := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP, cQ, dP, dQ,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3, u4⟩, hx⟩ := h
  have e2 := gate_diff hc l1 l2 t1 t2 (fun v hv => (cP v hv).1.symm)
  have e3 := gate_diff hc l1 l3 t1 t3 (fun v hv => (cP v hv).2.1.symm)
  have e4 := gate_diff hc l1 l4 t1 t4 (fun v hv => (cP v hv).2.2.symm)
  have f2 := gate_diff hc l6 l5 u2 u1 (fun v hv => (cQ v hv).1)
  have f3 := gate_diff hc l7 l5 u3 u1 (fun v hv => (cQ v hv).2.1)
  have f4 := gate_diff hc l8 l5 u4 u1 (fun v hv => (cQ v hv).2.2)
  have k1 := key1 o _ _ _ _ _ _ _ _ dP e2 e3 e4
  have k2 := key1 o _ _ _ _ _ _ _ _ dQ (Ne.symm f2) (Ne.symm f3) (Ne.symm f4)
  rcases k1 with ⟨ho, ha, hb⟩ | ⟨ho, ha, hb⟩ <;> rcases k2 with ⟨ho', ha', hb'⟩ | ⟨ho', ha', hb'⟩
  · rw [ha, hb, ha', hb'] at hx; cases hx
  · rw [ho] at ho'; cases ho'
  · rw [ho] at ho'; cases ho'
  · rw [ha, hb, ha', hb'] at hx; cases hx

theorem side_diff {w b : ℕ} {m : List ℕ} (hc : Cov (w :: b :: m)) {t u : ℕ}
    (ht : t < 128) (hu : u < 128) (htt : TT.testBit t = true) (huu : TT.testBit u = false)
    (hcu : ∀ v ∈ m, v.testBit t = v.testBit u) :
    w.testBit t ≠ w.testBit u ∨ b.testBit t ≠ b.testBit u := by
  obtain ⟨v, hv, hne⟩ := hc t u ht hu htt huu
  rcases List.mem_cons.1 hv with rfl | hv
  · exact Or.inl hne
  · rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr hne
    · exact absurd (hcu v hv) hne

theorem bad_side (o : Fin 4) {a b b' : ℕ} {m : List ℕ} (hc : Cov (opv AA o a b' :: b :: m))
    (h : Bad a b (b' :: m)) : Bad (opv AA o a b') b m := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP, cQ, dP, dQ,
    tP, tQ, hx⟩ := h
  have cP' : cst m p1 p2 p3 p4 := cst_sub (fun v hv => List.mem_cons_of_mem _ hv) cP
  have cQ' : cst m q1 q2 q3 q4 := cst_sub (fun v hv => List.mem_cons_of_mem _ hv) cQ
  obtain ⟨bp2, bp3, bp4⟩ := cP b' (List.mem_cons_self ..)
  obtain ⟨bq2, bq3, bq4⟩ := cQ b' (List.mem_cons_self ..)
  have e2 := side_diff hc l1 l2 tP.1 tP.2.1 (fun v hv => (cP' v hv).1.symm)
  have e3 := side_diff hc l1 l3 tP.1 tP.2.2.1 (fun v hv => (cP' v hv).2.1.symm)
  have e4 := side_diff hc l1 l4 tP.1 tP.2.2.2 (fun v hv => (cP' v hv).2.2.symm)
  have f2 := side_diff hc l6 l5 tQ.2.1 tQ.1 (fun v hv => (cQ' v hv).1)
  have f3 := side_diff hc l7 l5 tQ.2.2.1 tQ.1 (fun v hv => (cQ' v hv).2.1)
  have f4 := side_diff hc l8 l5 tQ.2.2.2 tQ.1 (fun v hv => (cQ' v hv).2.2)
  simp only [opv_bit _ _ _ l1, opv_bit _ _ _ l2, opv_bit _ _ _ l3, opv_bit _ _ _ l4,
    opv_bit _ _ _ l5, opv_bit _ _ _ l6, opv_bit _ _ _ l7, opv_bit _ _ _ l8,
    bp2, bp3, bp4, bq2, bq3, bq4] at e2 e3 e4 f2 f3 f4
  obtain ⟨dP', hP⟩ := key2 o _ _ _ _ _ _ _ _ _ dP e2 e3 e4
  obtain ⟨dQ', hQ⟩ := key2 o _ _ _ _ _ _ _ _ _ dQ (f2.imp Ne.symm Ne.symm) (f3.imp Ne.symm Ne.symm)
    (f4.imp Ne.symm Ne.symm)
  refine ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP', cQ', ?_, ?_, tP, tQ, ?_⟩
  · simp only [opv_bit _ _ _ l1, opv_bit _ _ _ l2, opv_bit _ _ _ l3, opv_bit _ _ _ l4, bp2, bp3, bp4]
    exact dP'
  · simp only [opv_bit _ _ _ l5, opv_bit _ _ _ l6, opv_bit _ _ _ l7, opv_bit _ _ _ l8, bq2, bq3, bq4]
    exact dQ'
  · rw [opv_bit _ _ _ l1, opv_bit _ _ _ l5, hP, hQ, piB_ne]
    exact hx

theorem bad_far (o : Fin 4) {a b a' b' : ℕ} {m : List ℕ} (h : Bad a b (a' :: b' :: m)) :
    Bad a b (opv AA o a' b' :: m) := by
  obtain ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, cP, cQ, h3⟩ := h
  refine ⟨p1, p2, p3, p4, q1, q2, q3, q4, ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩, ?_, ?_, h3⟩
  · intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · obtain ⟨x2, x3, x4⟩ := cP a' (by simp)
      obtain ⟨y2, y3, y4⟩ := cP b' (by simp)
      simp only [opv_bit _ _ _ l1, opv_bit _ _ _ l2, opv_bit _ _ _ l3, opv_bit _ _ _ l4,
        x2, x3, x4, y2, y3, y4]
      simp
    · exact cP v (by simp [hv])
  · intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · obtain ⟨x2, x3, x4⟩ := cQ a' (by simp)
      obtain ⟨y2, y3, y4⟩ := cQ b' (by simp)
      simp only [opv_bit _ _ _ l5, opv_bit _ _ _ l6, opv_bit _ _ _ l7, opv_bit _ _ _ l8,
        x2, x3, x4, y2, y3, y4]
      simp
    · exact cQ v (by simp [hv])

def swp : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

theorem opv_swp (o : Fin 4) (a b : ℕ) : opv AA o a b = opv AA (swp o) b a := by
  fin_cases o
  · exact Nat.land_comm a b
  · exact Nat.lor_comm a b
  · rfl
  · rfl

theorem perm_two {x y : ℕ} {s t : List ℕ} (h : (x :: s).Perm (y :: t)) (hne : x ≠ y) :
    ∃ m, s.Perm (y :: m) ∧ t.Perm (x :: m) := by
  have hy : y ∈ s := by
    have := h.symm.subset (List.mem_cons_self ..)
    rcases List.mem_cons.1 this with e | e
    · exact absurd e.symm hne
    · exact e
  have hs := List.perm_cons_erase hy
  refine ⟨s.erase y, hs, ?_⟩
  have : (y :: x :: s.erase y).Perm (y :: t) :=
    (List.Perm.swap _ _ _).trans ((hs.cons x).symm.trans h)
  exact this.cons_inv.symm

theorem perm_split {x y a b : ℕ} {z r : List ℕ} (h : (x :: y :: z).Perm (a :: b :: r)) :
    (x = a ∧ y = b ∧ z.Perm r) ∨ (x = b ∧ y = a ∧ z.Perm r) ∨
    (∃ m, x = a ∧ z.Perm (b :: m) ∧ r.Perm (y :: m)) ∨
    (∃ m, x = b ∧ z.Perm (a :: m) ∧ r.Perm (y :: m)) ∨
    (∃ m, y = a ∧ z.Perm (b :: m) ∧ r.Perm (x :: m)) ∨
    (∃ m, y = b ∧ z.Perm (a :: m) ∧ r.Perm (x :: m)) ∨
    (∃ m, z.Perm (a :: b :: m) ∧ r.Perm (x :: y :: m)) := by
  by_cases hxa : x = a
  · subst hxa
    have h1 := h.cons_inv
    by_cases hyb : y = b
    · subst hyb
      exact Or.inl ⟨rfl, rfl, h1.cons_inv⟩
    · obtain ⟨m, h2, h3⟩ := perm_two h1 hyb
      exact Or.inr (Or.inr (Or.inl ⟨m, rfl, h2, h3⟩))
  · obtain ⟨m1, h1, h2⟩ := perm_two h hxa
    -- h1 : (y :: z).Perm (a :: m1), h2 : (b :: r).Perm (x :: m1)
    by_cases hya : y = a
    · subst hya
      have h3 := h1.cons_inv
      by_cases hxb : x = b
      · subst hxb
        exact Or.inr (Or.inl ⟨rfl, rfl, h3.trans h2.cons_inv.symm⟩)
      · obtain ⟨m, h4, h5⟩ := perm_two h2 (Ne.symm hxb)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl, h3.trans h5, h4⟩))))
    · obtain ⟨m2, h3, h4⟩ := perm_two h1 hya
      -- h3 : z.Perm (a :: m2), h4 : m1.Perm (y :: m2)
      have h5 : (b :: r).Perm (x :: y :: m2) := h2.trans (h4.cons x)
      by_cases hxb : x = b
      · subst hxb
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m2, rfl, h3, h5.cons_inv⟩)))
      · by_cases hyb : y = b
        · subst hyb
          have h6 : (y :: r).Perm (y :: x :: m2) := h5.trans (List.Perm.swap _ _ _)
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m2, rfl, h3, h6.cons_inv⟩)))))
        · obtain ⟨m3, h6, h7⟩ := perm_two h5 (Ne.symm hxb)
          obtain ⟨m4, h8, h9⟩ := perm_two h7 hyb
          -- h6 : r.Perm (x :: m3), h7 : (y :: m2).Perm (b :: m3), h8 : m2.Perm (b :: m4), h9 : m3.Perm (y :: m4)
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m4, ?_, ?_⟩)))))
          · exact h3.trans (h8.cons a)
          · exact h6.trans (h9.cons x)

theorem rok_two {o : Fin 4} {a b : ℕ} {r : List ℕ} (hc : Cov (opv AA o a b :: r))
    (hr : ROk (opv AA o a b :: r)) : ROk (a :: b :: r) := by
  intro x y z hp hbad
  rcases perm_split hp.symm with ⟨rfl, rfl, hz⟩ | ⟨rfl, rfl, hz⟩ | ⟨m, rfl, hz, hm⟩ |
      ⟨m, rfl, hz, hm⟩ | ⟨m, rfl, hz, hm⟩ | ⟨m, rfl, hz, hm⟩ | ⟨m, hz, hm⟩
  · exact bad_gate o hc (hbad.sub fun v hv => hz.symm.subset hv)
  · rw [opv_swp] at hc
    exact bad_gate (swp o) hc (hbad.sub fun v hv => hz.symm.subset hv)
  · have hc' : Cov (opv AA o x b :: y :: m) := hc.perm (hm.cons _)
    have hb := bad_side o hc' (hbad.sub fun v hv => hz.symm.subset hv)
    exact hr _ _ _ (hm.cons _) hb
  · rw [opv_swp] at hc hr
    have hc' : Cov (opv AA (swp o) x a :: y :: m) := hc.perm (hm.cons _)
    have hb := bad_side (swp o) hc' (hbad.sub fun v hv => hz.symm.subset hv)
    exact hr _ _ _ (hm.cons _) hb
  · have hc' : Cov (opv AA o y b :: x :: m) := hc.perm (hm.cons _)
    have hb := bad_side o hc' ((hbad.sub fun v hv => hz.symm.subset hv).swap)
    exact hr _ _ _ (hm.cons _) hb
  · rw [opv_swp] at hc hr
    have hc' : Cov (opv AA (swp o) y a :: x :: m) := hc.perm (hm.cons _)
    have hb := bad_side (swp o) hc' ((hbad.sub fun v hv => hz.symm.subset hv).swap)
    exact hr _ _ _ (hm.cons _) hb
  · have hb := bad_far o (hbad.sub fun v hv => hz.symm.subset hv)
    refine hr x y (opv AA o a b :: m) ?_ hb
    refine (hm.cons _).trans ?_
    exact (List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)

/-! ### Invariants of runs -/

theorem len_kept (k : Bool) (x : ℕ) (xs : List ℕ) : xs.length ≤ (kept k x xs).length := by
  cases k <;> simp [kept]

theorem cov_TT : Cov [TT] := fun t u _ _ h1 h2 => ⟨TT, by simp, by rw [h1, h2]; simp⟩

theorem Run.inv {s : ℕ} {L : List ℕ} (h : Run TT AA s L) :
    L.length ≤ s + 1 ∧ Cov L ∧ (L.length = s + 1 → ROk L) := by
  induction h with
  | done s =>
    refine ⟨by simp, cov_TT, fun _ a b r hp _ => ?_⟩
    have := hp.length_eq
    simp at this
  | perm p _ ih =>
    refine ⟨p.length_eq ▸ ih.1, ih.2.1.perm p, fun hl a b r hp => ?_⟩
    exact ih.2.2 (p.length_eq ▸ hl) a b r (p.trans hp)
  | mono _ ih =>
    exact ⟨by omega, ih.2.1, fun hl => absurd hl (by omega)⟩
  | @two s a b r o ka kb _ ih =>
    obtain ⟨hl, hc, hro⟩ := ih
    have h1 := len_kept ka a (kept kb b r)
    have h2 := len_kept kb b r
    simp only [List.length_cons] at hl
    refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
    · intro t u ht hu h1 h2
      obtain ⟨v, hv, hne⟩ := hc t u ht hu h1 h2
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [opv_bit _ _ _ ht, opv_bit _ _ _ hu] at hne
        rcases opb_diff _ _ _ _ _ hne with e | e
        · exact ⟨a, by simp, e⟩
        · exact ⟨b, by simp, e⟩
      · rcases mem_kept hv with rfl | hv
        · exact ⟨v, by simp, hne⟩
        · rcases mem_kept hv with rfl | hv
          · exact ⟨v, by simp, hne⟩
          · exact ⟨v, by simp [hv], hne⟩
    · intro hlen
      simp only [List.length_cons] at hlen
      cases ka <;> cases kb
      · exact rok_two hc (hro (by simp [kept]; omega))
      · simp [kept] at hl; omega
      · simp [kept] at hl; omega
      · simp [kept] at hl; omega
  | @one s a w r ka hw _ ih =>
    obtain ⟨hl, hc, _⟩ := ih
    have h1 := len_kept ka a r
    simp only [List.length_cons] at hl
    refine ⟨by simp only [List.length_cons]; omega, ?_, fun hlen => by simp at hlen; omega⟩
    intro t u ht hu h1 h2
    obtain ⟨v, hv, hne⟩ := hc t u ht hu h1 h2
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨v, by simp, hne⟩
      · rw [xor_bit _ ht, xor_bit _ hu] at hne
        exact ⟨a, by simp, fun e => hne (by rw [e])⟩
      · simp at hne
      · rw [AA_bit ht, AA_bit hu] at hne
        exact absurd rfl hne
    · rcases mem_kept hv with rfl | hv
      · exact ⟨v, by simp, hne⟩
      · exact ⟨v, by simp [hv], hne⟩
  | @const s w r hw _ ih =>
    obtain ⟨hl, hc, _⟩ := ih
    simp only [List.length_cons] at hl
    refine ⟨by omega, ?_, fun hlen => by omega⟩
    intro t u ht hu h1 h2
    obtain ⟨v, hv, hne⟩ := hc t u ht hu h1 h2
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases hw with rfl | rfl
      · simp at hne
      · rw [AA_bit ht, AA_bit hu] at hne
        exact absurd rfl hne
    · exact ⟨v, hv, hne⟩

/-! ### Witnesses -/

structure Wt where
  xi : ℕ
  xj : ℕ
  nxi : ℕ
  nxj : ℕ
  m1 : ℕ
  m2 : ℕ
  p1 : ℕ
  p2 : ℕ
  p3 : ℕ
  p4 : ℕ
  q1 : ℕ
  q2 : ℕ
  q3 : ℕ
  q4 : ℕ

def WL : List Wt := [⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf0, 3, 0, 1, 2, 4, 5, 6, 7⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x55555555555555555555555555555555, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33, 0xcc, 5, 0, 1, 4, 2, 3, 6, 7⟩,
  ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33333333333333333333333333333333, 0x55, 0xaa, 6, 0, 2, 4, 1, 3, 5, 7⟩,
  ⟨0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff, 0x1010101, 0x202020200000000, 24, 0, 8, 16, 33, 41, 49, 57⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf000000000000000000, 3, 0, 1, 2, 72, 73, 74, 75⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0x55555555555555555555555555555555, 0xff00ff00ff00ff00ff00ff00ff00ff, 0x303, 0xc0c0000, 9, 0, 1, 8, 18, 19, 26, 27⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0x55555555555555555555555555555555, 0xff00ff00ff00ff00ff00ff00ff00ff, 0x303, 0x30300000, 9, 0, 1, 8, 20, 21, 28, 29⟩,
  ⟨0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff, 0x1000100010001, 0x1000100010001000000000000000000, 48, 0, 16, 32, 72, 88, 104, 120⟩,
  ⟨0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000, 0xffffffff00000000ffffffff, 0xffffffffffffffff, 0x1000000010000000100000001, 0x40000000400000004000000040000, 96, 0, 32, 64, 18, 50, 82, 114⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf00000000000000000, 3, 0, 1, 2, 68, 69, 70, 71⟩,
  ⟨0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33333333333333333333333333333333, 0x55, 0xaa0000000000000000, 6, 0, 2, 4, 65, 67, 69, 71⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0x55555555555555555555555555555555, 0x33333333333333333333333333333333, 0xf, 0xf000, 3, 0, 1, 2, 12, 13, 14, 15⟩,
  ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x55555555555555555555555555555555, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0x33, 0xcc00, 5, 0, 1, 4, 10, 11, 14, 15⟩,
  ⟨0xffffffffffffffff0000000000000000, 0xcccccccccccccccccccccccccccccccc, 0xffffffffffffffff, 0x33333333333333333333333333333333, 0x50000000000000005, 0xa000000000000000a00000000, 66, 0, 2, 64, 33, 35, 97, 99⟩,
  ⟨0xffffffffffffffff0000000000000000, 0xcccccccccccccccccccccccccccccccc, 0xffffffffffffffff, 0x33333333333333333333333333333333, 0x50000000000000005, 0x50000000000000005000000000, 66, 0, 2, 64, 36, 38, 100, 102⟩]


def cm (v m : ℕ) : Bool := (v &&& m == 0) || (v &&& m == m)

def wgood (w : Wt) (a b : ℕ) : Bool :=
  decide (w.p1 < 128 ∧ w.p2 < 128 ∧ w.p3 < 128 ∧ w.p4 < 128 ∧ w.q1 < 128 ∧ w.q2 < 128 ∧
    w.q3 < 128 ∧ w.q4 < 128) &&
  (w.m1.testBit w.p1 && w.m1.testBit w.p2 && w.m1.testBit w.p3 && w.m1.testBit w.p4) &&
  (w.m2.testBit w.q1 && w.m2.testBit w.q2 && w.m2.testBit w.q3 && w.m2.testBit w.q4) &&
  d4 (a.testBit w.p1) (b.testBit w.p1) (a.testBit w.p2) (b.testBit w.p2) (a.testBit w.p3)
    (b.testBit w.p3) (a.testBit w.p4) (b.testBit w.p4) &&
  d4 (a.testBit w.q1) (b.testBit w.q1) (a.testBit w.q2) (b.testBit w.q2) (a.testBit w.q3)
    (b.testBit w.q3) (a.testBit w.q4) (b.testBit w.q4) &&
  (TT.testBit w.p1 && !TT.testBit w.p2 && !TT.testBit w.p3 && !TT.testBit w.p4) &&
  (!TT.testBit w.q1 && TT.testBit w.q2 && TT.testBit w.q3 && TT.testBit w.q4) &&
  (a.testBit w.p1 != a.testBit w.q1 || b.testBit w.p1 != b.testBit w.q1) && (a != b)

set_option maxHeartbeats 4000000 in
theorem wl_good : ∀ w ∈ WL, ∀ a ∈ [w.xi, w.nxi], ∀ b ∈ [w.xj, w.nxj],
    wgood w a b = true := by decide +kernel

theorem cm_eq {v m p q : ℕ} (h : cm v m = true) (hp : m.testBit p = true) (hq : m.testBit q = true) :
    v.testBit q = v.testBit p := by
  unfold cm at h
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  have ep : (v &&& m).testBit p = v.testBit p := by rw [Nat.testBit_and, hp, Bool.and_true]
  have eq : (v &&& m).testBit q = v.testBit q := by rw [Nat.testBit_and, hq, Bool.and_true]
  rcases h with h | h
  · rw [← ep, ← eq, h]; simp
  · rw [← ep, ← eq, h, hp, hq]


/-! ### Trees, sorting, children -/

def picks : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map fun q => (q.1, x :: q.2)

def pairsOf : List ℕ → List (ℕ × ℕ × List ℕ)
  | [] => []
  | x :: xs => (picks xs).map (fun q => (x, q.1, q.2)) ++
      (pairsOf xs).map fun q => (q.1, q.2.1, x :: q.2.2)

def wone (w : Wt) (L : List ℕ) (a b : ℕ) : Bool :=
  L.count a == 1 && L.count b == 1 && L.all (fun v => v == a || v == b || (cm v w.m1 && cm v w.m2))

def wtry (w : Wt) (L : List ℕ) : Bool :=
  wone w L w.xi w.xj || wone w L w.xi w.nxj || wone w L w.nxi w.xj || wone w L w.nxi w.nxj

def wit (L : List ℕ) : Bool := WL.any fun w => wtry w L

def passes (s : ℕ) (L : List ℕ) : Bool :=
  Nat.ble L.length (s + 1) && covB L && !(L.length == s + 1 && wit L)

def twoCh (a b : ℕ) (r : List ℕ) : List (List ℕ) :=
  ([0, 1, 2, 3] : List (Fin 4)).flatMap fun o => [true, false].flatMap fun ka =>
    [true, false].map fun kb => opv AA o a b :: kept ka a (kept kb b r)

def children (L : List ℕ) : List (List ℕ) :=
  (pairsOf L).flatMap (fun q => twoCh q.1 q.2.1 q.2.2) ++
  (picks L).flatMap (fun q => [q.1 :: q.1 :: q.2, (AA ^^^ q.1) :: q.1 :: q.2, (AA ^^^ q.1) :: q.2,
    0 :: q.1 :: q.2, 0 :: q.2, AA :: q.1 :: q.2, AA :: q.2]) ++
  [0 :: L, AA :: L]

def ksOf (n lev : ℕ) : List (Bool × Bool) :=
  if n = lev + 1 then [(false, false)] else if n = lev then [(true, false), (false, true), (false, false)]
  else [(true, true), (true, false), (false, true), (false, false)]

def ksF (o : Fin 4) (ks : List (Bool × Bool)) : List (Bool × Bool) :=
  if o = 2 then ks.filter (fun k => !k.2) else if o = 3 then ks.filter (fun k => !k.1) else ks

def twoS (ks : List (Bool × Bool)) (a b : ℕ) (r : List ℕ) : List (List ℕ) :=
  ([0, 1, 2, 3] : List (Fin 4)).flatMap fun o => (ksF o ks).map fun k =>
    opv AA o a b :: kept k.1 a (kept k.2 b r)

def oneS (n lev a : ℕ) (r : List ℕ) : List (List ℕ) :=
  if n + 1 ≤ lev then [a :: a :: r, (AA ^^^ a) :: a :: r, (AA ^^^ a) :: r, 0 :: a :: r, 0 :: r,
    AA :: a :: r, AA :: r]
  else [(AA ^^^ a) :: r, 0 :: r, AA :: r]

def childrenS (L : List ℕ) (lev : ℕ) : List (List ℕ) :=
  (pairsOf L).flatMap (fun q => twoS (ksOf L.length lev) q.1 q.2.1 q.2.2) ++
  (picks L).flatMap (fun q => oneS L.length lev q.1 q.2) ++
  (if L.length + 1 ≤ lev then [0 :: L, AA :: L] else [])

inductive Tr where
  | E : Tr
  | N : Tr → List ℕ → ℕ → Tr → Tr

def cmpL : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: as, b :: bs => if Nat.blt a b then Ordering.lt else if Nat.blt b a then Ordering.gt else cmpL as bs

def look : Tr → List ℕ → ℕ → Bool
  | Tr.E, _, _ => false
  | Tr.N l k v r, x, s =>
    match cmpL x k with
    | Ordering.lt => look l x s
    | Ordering.gt => look r x s
    | Ordering.eq => Nat.ble s v

def srt (L : List ℕ) : List ℕ := List.insertionSort (fun a b => a ≤ b) L

def pg : List ℕ → ℕ → ℕ
  | [], _ => 0
  | q :: qs, v => Nat.bit (v.testBit q) (pg qs v)

def lookS (t t2 : Tr) (s : ℕ) (L : List ℕ) : Bool :=
  look t (srt L) s || look t2 (srt L) s

def chkE (t t2 : Tr) (K : List ℕ) (lev : ℕ) : Bool :=
  Nat.ble 1 lev && !(cmpL K [TT] == Ordering.eq) &&
    (childrenS K lev).all fun ch => !(passes (lev - 1) ch) || lookS t t2 (lev - 1) ch

def allE (t t2 : Tr) : Tr → Bool
  | Tr.E => true
  | Tr.N l k v r => chkE t t2 k v && allE t t2 l && allE t t2 r

def allS (t : Tr) : Tr → Bool
  | Tr.E => true
  | Tr.N l k v r => look t (srt (k.map (pg SG))) v && allS t l && allS t r


theorem srt_perm {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) : srt L₁ = srt L₂ := by
  apply List.Perm.eq_of_sortedLE
  · exact List.sortedLE_iff_pairwise.2 (List.pairwise_insertionSort _ _)
  · exact List.sortedLE_iff_pairwise.2 (List.pairwise_insertionSort _ _)
  · exact ((List.perm_insertionSort _ L₁).trans p).trans (List.perm_insertionSort _ L₂).symm

theorem srt_perm_self (L : List ℕ) : (srt L).Perm L := List.perm_insertionSort _ L

inductive Mem : Tr → List ℕ → ℕ → Prop
  | here (l : Tr) (k : List ℕ) (v : ℕ) (r : Tr) : Mem (Tr.N l k v r) k v
  | left {l : Tr} {k k' : List ℕ} {v v' : ℕ} (r : Tr) : Mem l k' v' → Mem (Tr.N l k v r) k' v'
  | right (l : Tr) {r : Tr} {k k' : List ℕ} {v v' : ℕ} : Mem r k' v' → Mem (Tr.N l k v r) k' v'

theorem cmpL_eq : ∀ {a b : List ℕ}, cmpL a b = Ordering.eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpL] at h
  | _ :: _, [], h => by simp [cmpL] at h
  | x :: xs, y :: ys, h => by
    unfold cmpL at h
    by_cases h1 : Nat.blt x y = true
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : Nat.blt y x = true
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [Nat.blt_eq] at h1 h2
        rw [cmpL_eq h, show x = y by omega]

theorem look_sound : ∀ {t : Tr} {x : List ℕ} {s : ℕ}, look t x s = true → ∃ v, Mem t x v ∧ s ≤ v
  | Tr.E, _, _, h => by simp [look] at h
  | Tr.N l k v r, x, s, h => by
    unfold look at h
    split at h
    · obtain ⟨w, hw, hs⟩ := look_sound h
      exact ⟨w, Mem.left r hw, hs⟩
    · obtain ⟨w, hw, hs⟩ := look_sound h
      exact ⟨w, Mem.right l hw, hs⟩
    · rename_i hc
      rw [cmpL_eq hc]
      exact ⟨v, Mem.here l k v r, Nat.le_of_ble_eq_true h⟩

theorem allE_sound (t t2 : Tr) : ∀ {t' : Tr} {K : List ℕ} {v : ℕ}, allE t t2 t' = true → Mem t' K v →
    chkE t t2 K v = true
  | Tr.E, _, _, _, hm => by cases hm
  | Tr.N l k w r, K, v, h, hm => by
    unfold allE at h
    simp only [Bool.and_eq_true] at h
    cases hm with
    | here => exact h.1.1
    | left _ hm => exact allE_sound t t2 h.1.2 hm
    | right _ hm => exact allE_sound t t2 h.2 hm

theorem allS_sound (t : Tr) : ∀ {t' : Tr} {K : List ℕ} {v : ℕ}, allS t t' = true → Mem t' K v →
    look t (srt (K.map (pg SG))) v = true
  | Tr.E, _, _, _, hm => by cases hm
  | Tr.N l k w r, K, v, h, hm => by
    unfold allS at h
    simp only [Bool.and_eq_true] at h
    cases hm with
    | here => exact h.1.1
    | left _ hm => exact allS_sound t h.1.2 hm
    | right _ hm => exact allS_sound t h.2 hm

theorem picks_sound : ∀ {L : List ℕ} {x : ℕ} {r : List ℕ}, (x, r) ∈ picks L → L.Perm (x :: r)
  | [], _, _, h => by simp [picks] at h
  | y :: ys, x, r, h => by
    simp only [picks, List.mem_cons, Prod.mk.injEq, List.mem_map] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨⟨a, b⟩, hq, he⟩
    · exact List.Perm.refl _
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ((picks_sound hq).cons y).trans (List.Perm.swap _ _ _)

theorem picks_complete : ∀ {L : List ℕ} {x : ℕ}, x ∈ L → ∃ r, (x, r) ∈ picks L
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ys, by simp [picks]⟩
    · obtain ⟨r, hr⟩ := picks_complete h
      exact ⟨y :: r, by simp only [picks, List.mem_cons, List.mem_map]; exact Or.inr ⟨(x, r), hr, rfl⟩⟩

theorem pick_perm {L r : List ℕ} {x : ℕ} (hL : L.Perm (x :: r)) :
    ∃ r', (x, r') ∈ picks L ∧ r'.Perm r := by
  obtain ⟨r', hr'⟩ := picks_complete (hL.symm.subset (List.mem_cons_self ..))
  exact ⟨r', hr', ((picks_sound hr').symm.trans hL).cons_inv⟩

theorem pairs_complete : ∀ {K : List ℕ} {a b : ℕ} {r : List ℕ}, K.Perm (a :: b :: r) →
    ∃ q ∈ pairsOf K, ((q.1 = a ∧ q.2.1 = b) ∨ (q.1 = b ∧ q.2.1 = a)) ∧ q.2.2.Perm r
  | [], _, _, _, h => by have := h.length_eq; simp at this
  | x :: xs, a, b, r, h => by
    by_cases hxa : x = a
    · subst hxa
      have h1 : xs.Perm (b :: r) := h.cons_inv
      obtain ⟨r', hr', hp⟩ := pick_perm h1
      exact ⟨(x, b, r'), by simp only [pairsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨(b, r'), hr', rfl⟩,
        Or.inl ⟨rfl, rfl⟩, hp⟩
    · by_cases hxb : x = b
      · subst hxb
        have h1 : xs.Perm (a :: r) := (h.trans (List.Perm.swap _ _ _)).cons_inv
        obtain ⟨r', hr', hp⟩ := pick_perm h1
        exact ⟨(x, a, r'), by simp only [pairsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨(a, r'), hr', rfl⟩,
          Or.inr ⟨rfl, rfl⟩, hp⟩
      · have hxr : x ∈ r := by
          have := h.subset (List.mem_cons_self ..)
          simp only [List.mem_cons] at this
          rcases this with h' | h' | h'
          · exact absurd h' hxa
          · exact absurd h' hxb
          · exact h'
        have hr := List.perm_cons_erase hxr
        have h2 : xs.Perm (a :: b :: r.erase x) := by
          apply List.Perm.cons_inv (a := x)
          refine h.trans ?_
          refine ((hr.cons b).cons a).trans ?_
          exact ((List.Perm.swap _ _ _).cons a).trans (List.Perm.swap _ _ _)
        obtain ⟨q, hq, hab, hp⟩ := pairs_complete h2
        refine ⟨(q.1, q.2.1, x :: q.2.2), ?_, hab, ?_⟩
        · simp only [pairsOf, List.mem_append, List.mem_map]
          exact Or.inr ⟨q, hq, rfl⟩
        · exact (hp.cons x).trans hr.symm

theorem kept_swap (ka kb : Bool) (a b : ℕ) (r : List ℕ) :
    (kept ka a (kept kb b r)).Perm (kept kb b (kept ka a r)) := by
  cases ka <;> cases kb <;> simp [kept] <;> exact List.Perm.swap _ _ _

theorem kept_perm (k : Bool) (x : ℕ) {l₁ l₂ : List ℕ} (p : l₁.Perm l₂) :
    (kept k x l₁).Perm (kept k x l₂) := by
  cases k
  · exact p
  · exact p.cons x


theorem pairsOf_sound : ∀ {L : List ℕ} {q : ℕ × ℕ × List ℕ}, q ∈ pairsOf L →
    L.Perm (q.1 :: q.2.1 :: q.2.2)
  | [], _, h => by simp [pairsOf] at h
  | x :: xs, q, h => by
    simp only [pairsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨a, r⟩, hq, rfl⟩ | ⟨q', hq, rfl⟩
    · exact (picks_sound hq).cons x
    · exact ((pairsOf_sound hq).cons x).trans
        ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

theorem wone_bad {w : Wt} (hw : w ∈ WL) {a b : ℕ} {L : List ℕ} (h : wone w L a b = true)
    (hab : a ∈ [w.xi, w.nxi] ∧ b ∈ [w.xj, w.nxj]) : ∃ r, L.Perm (a :: b :: r) ∧ Bad a b r := by
  unfold wone at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hca, hcb⟩, hall⟩ := h
  have hg := wl_good w hw a hab.1 b hab.2
  unfold wgood at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hl, hm⟩, hn⟩, dP⟩, dQ⟩, ht⟩, hu⟩, hx⟩, hne⟩ := hg
  obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hm
  obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hn
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := ht
  obtain ⟨⟨⟨u1, u2⟩, u3⟩, u4⟩ := hu
  have ha : a ∈ L := List.count_pos_iff.1 (by omega)
  have hb : b ∈ L := List.count_pos_iff.1 (by omega)
  have hb' : b ∈ L.erase a := (List.mem_erase_of_ne (Ne.symm hne)).2 hb
  let r := (L.erase a).erase b
  have hp : L.Perm (a :: b :: r) := (List.perm_cons_erase ha).trans ((List.perm_cons_erase hb').cons a)
  have hra : ∀ v ∈ r, v ≠ a := by
    intro v hv e
    rw [e] at hv
    have c1 : r.count a = 0 := by
      simp only [r]
      rw [List.count_erase_of_ne hne, List.count_erase_self, hca]
    have := List.count_pos_iff.2 hv
    omega
  have hrb : ∀ v ∈ r, v ≠ b := by
    intro v hv e
    rw [e] at hv
    have c1 : r.count b = 0 := by
      simp only [r]
      rw [List.count_erase_self, List.count_erase_of_ne (Ne.symm hne), hcb]
    have := List.count_pos_iff.2 hv
    omega
  have hcm : ∀ v ∈ r, cm v w.m1 = true ∧ cm v w.m2 = true := by
    intro v hv
    have hvL : v ∈ L := List.mem_of_mem_erase (List.mem_of_mem_erase hv)
    rcases hall v hvL with (e | e) | e
    · exact absurd e (hra v hv)
    · exact absurd e (hrb v hv)
    · exact e
  refine ⟨r, hp, w.p1, w.p2, w.p3, w.p4, w.q1, w.q2, w.q3, w.q4, hl, ?_, ?_, dP, dQ,
    ⟨t1, t2, t3, t4⟩, ⟨u1, u2, u3, u4⟩, hx⟩
  · intro v hv
    have hc := (hcm v hv).1
    exact ⟨cm_eq hc m1 m2, cm_eq hc m1 m3, cm_eq hc m1 m4⟩
  · intro v hv
    have hc := (hcm v hv).2
    exact ⟨cm_eq hc n1 n2, cm_eq hc n1 n3, cm_eq hc n1 n4⟩

theorem wit_sound {L : List ℕ} (h : wit L = true) : ∃ a b r, L.Perm (a :: b :: r) ∧ Bad a b r := by
  unfold wit at h
  obtain ⟨w, hw, h⟩ := List.any_eq_true.1 h
  unfold wtry at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩
  · obtain ⟨r, hp, hb⟩ := wone_bad hw h ⟨by simp, by simp⟩; exact ⟨_, _, r, hp, hb⟩

theorem Run.passOk {s : ℕ} {L : List ℕ} (h : Run TT AA s L) {s' : ℕ} (hs : s ≤ s') :
    passes s' L = true := by
  obtain ⟨hl, hc, hr⟩ := h.inv
  unfold passes
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, covB_of_cov hc]
  refine ⟨⟨by omega, rfl⟩, ?_⟩
  rw [Bool.not_eq_true']
  cases hw : wit L
  · simp
  · by_cases hlen : L.length = s' + 1
    · obtain ⟨a, b, r, hp, hb⟩ := wit_sound hw
      exact absurd hb (hr (by omega) a b r hp)
    · simp [hlen]

/-! ### Symmetry -/

theorem pg_bit : ∀ (p : List ℕ) (v j : ℕ), (pg p v).testBit j = (p[j]?.map v.testBit).getD false
  | [], v, j => by simp [pg]
  | q :: qs, v, 0 => by simp [pg, Nat.testBit_bit_zero]
  | q :: qs, v, j + 1 => by simp [pg, Nat.testBit_bit_succ, pg_bit qs v j]

theorem pg_and (p : List ℕ) (a b : ℕ) : pg p (a &&& b) = pg p a &&& pg p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, pg_bit, pg_bit, pg_bit]
  cases p[j]? <;> simp [Nat.testBit_and]

theorem pg_or (p : List ℕ) (a b : ℕ) : pg p (a ||| b) = pg p a ||| pg p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, pg_bit, pg_bit, pg_bit]
  cases p[j]? <;> simp [Nat.testBit_or]

theorem pg_xor (p : List ℕ) (a b : ℕ) : pg p (a ^^^ b) = pg p a ^^^ pg p b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, pg_bit, pg_bit, pg_bit]
  cases p[j]? <;> simp [Nat.testBit_xor]

def Hom (f : ℕ → ℕ) : Prop :=
  (∀ a b, f (a &&& b) = f a &&& f b) ∧ (∀ a b, f (a ||| b) = f a ||| f b) ∧
    (∀ a b, f (a ^^^ b) = f a ^^^ f b) ∧ f 0 = 0 ∧ f TT = TT ∧ f AA = AA

set_option maxHeartbeats 4000000 in
theorem sg_fix : pg SG 0 = 0 ∧ pg SG TT = TT ∧ pg SG AA = AA := by decide +kernel

theorem hom_sg : Hom (pg SG) := ⟨pg_and SG, pg_or SG, pg_xor SG, sg_fix.1, sg_fix.2.1, sg_fix.2.2⟩

theorem hom_id : Hom id := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Hom.comp {f g : ℕ → ℕ} (hf : Hom f) (hg : Hom g) : Hom (f ∘ g) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hg
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, ?_, ?_, ?_⟩ <;>
    simp only [Function.comp_apply, f1, f2, f3, f4, f5, f6, g1, g2, g3, g4, g5, g6]

theorem hom_opv {f : ℕ → ℕ} (hf : Hom f) (o : Fin 4) (a b : ℕ) :
    f (opv AA o a b) = opv AA o (f a) (f b) := by
  fin_cases o
  · exact hf.1 a b
  · exact hf.2.1 a b
  · show f (AA ^^^ a) = AA ^^^ f a
    rw [hf.2.2.1, hf.2.2.2.2.2]
  · show f (AA ^^^ b) = AA ^^^ f b
    rw [hf.2.2.1, hf.2.2.2.2.2]

theorem hom_not {f : ℕ → ℕ} (hf : Hom f) (a : ℕ) : f (AA ^^^ a) = AA ^^^ f a := by
  rw [hf.2.2.1, hf.2.2.2.2.2]

theorem Run.mapH {f : ℕ → ℕ} (hf : Hom f) {s : ℕ} {L : List ℕ} (h : Run TT AA s L) :
    Run TT AA s (L.map f) := by
  induction h with
  | done s =>
    rw [List.map_cons, List.map_nil, hf.2.2.2.2.1]
    exact Run.done s
  | perm p _ ih => exact Run.perm (p.map _) ih
  | mono _ ih => exact Run.mono ih
  | @two s a b r o ka kb _ ih =>
    simp only [List.map_cons, map_kept, hom_opv hf] at ih ⊢
    exact Run.two o ka kb ih
  | @one s a w r ka hw _ ih =>
    simp only [List.map_cons, map_kept] at ih ⊢
    refine Run.one ka ?_ ih
    rcases hw with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hom_not hf a))
    · exact Or.inr (Or.inr (Or.inl hf.2.2.2.1))
    · exact Or.inr (Or.inr (Or.inr hf.2.2.2.2.2))
  | @const s w r hw _ ih =>
    simp only [List.map_cons] at ih ⊢
    refine Run.const ?_ ih
    rcases hw with rfl | rfl
    · exact Or.inl hf.2.2.2.1
    · exact Or.inr hf.2.2.2.2.2

theorem lookS_sound {t t2 : Tr} (hS : allS t t2 = true) {s : ℕ} {L : List ℕ} (h : lookS t t2 s L = true) :
    ∃ g, Hom g ∧ ∃ v, Mem t (srt (L.map g)) v ∧ s ≤ v := by
  unfold lookS at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨v, hv, hs⟩ := look_sound h
    exact ⟨id, hom_id, v, by rwa [List.map_id], hs⟩
  · obtain ⟨w, hw, hs⟩ := look_sound h
    obtain ⟨v, hv, hs2⟩ := look_sound (allS_sound t hS hw)
    refine ⟨pg SG, hom_sg, v, ?_, by omega⟩
    rwa [srt_perm ((srt_perm_self L).map (pg SG))] at hv

/-! ### Children -/

def Child (P c : List ℕ) : Prop :=
  (∃ a b r o ka kb, P = a :: b :: r ∧ c = opv AA o a b :: kept ka a (kept kb b r)) ∨
  (∃ a r w ka, P = a :: r ∧ (w = AA ^^^ a ∨ w = 0 ∨ w = AA ∨ (w = a ∧ ka = true)) ∧
    c = w :: kept ka a r) ∨
  (∃ w, (w = 0 ∨ w = AA) ∧ c = w :: P)

theorem child_map {f : ℕ → ℕ} (hf : Hom f) {P c : List ℕ} (h : Child P c) :
    Child (P.map f) (c.map f) := by
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · left
    refine ⟨f a, f b, r.map f, o, ka, kb, rfl, ?_⟩
    simp [map_kept, hom_opv hf]
  · right; left
    refine ⟨f a, r.map f, f w, ka, rfl, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl | ⟨rfl, rfl⟩
      · exact Or.inl (hom_not hf a)
      · exact Or.inr (Or.inl hf.2.2.2.1)
      · exact Or.inr (Or.inr (Or.inl hf.2.2.2.2.2))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · simp [map_kept]
  · right; right
    refine ⟨f w, ?_, ?_⟩
    · rcases hw with rfl | rfl
      · exact Or.inl hf.2.2.2.1
      · exact Or.inr hf.2.2.2.2.2
    · simp

theorem mem_twoCh (a b : ℕ) (r : List ℕ) (o : Fin 4) (ka kb : Bool) :
    opv AA o a b :: kept ka a (kept kb b r) ∈ twoCh a b r := by
  unfold twoCh
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨o, by fin_cases o <;> simp, ka, by cases ka <;> simp, kb, by cases kb <;> simp, rfl⟩

theorem child_perm {P c K : List ℕ} (h : Child P c) (hK : K.Perm P) :
    ∃ c' ∈ children K, c'.Perm c := by
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · obtain ⟨q, hq, hab, hp⟩ := pairs_complete hK
    have hmem : ∀ o' ka' kb', opv AA o' q.1 q.2.1 :: kept ka' q.1 (kept kb' q.2.1 q.2.2) ∈ children K := by
      intro o' ka' kb'
      unfold children
      simp only [List.mem_append]
      left; left
      rw [List.mem_flatMap]
      exact ⟨q, hq, mem_twoCh _ _ _ o' ka' kb'⟩
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨_, hmem o ka kb, ?_⟩
      rw [h1, h2]
      exact (kept_perm ka a (kept_perm kb b hp)).cons _
    · refine ⟨_, hmem (swp o) kb ka, ?_⟩
      rw [h1, h2, ← opv_swp]
      exact ((kept_perm kb b (kept_perm ka a hp)).trans (kept_swap kb ka b a r)).cons _
  · obtain ⟨r', hr', hp⟩ := pick_perm hK
    have hmem : ∀ ch ∈ [a :: a :: r', (AA ^^^ a) :: a :: r', (AA ^^^ a) :: r', 0 :: a :: r', 0 :: r',
        AA :: a :: r', AA :: r'], ch ∈ children K := by
      intro ch hch
      unfold children
      simp only [List.mem_append]
      left; right
      rw [List.mem_flatMap]
      exact ⟨(a, r'), hr', hch⟩
    rcases hw with rfl | rfl | rfl | ⟨rfl, rfl⟩
    · cases ka
      · exact ⟨_, hmem _ (by simp), hp.cons _⟩
      · exact ⟨_, hmem _ (by simp), (hp.cons a).cons _⟩
    · cases ka
      · exact ⟨_, hmem _ (by simp), hp.cons _⟩
      · exact ⟨_, hmem _ (by simp), (hp.cons a).cons _⟩
    · cases ka
      · exact ⟨_, hmem _ (by simp), hp.cons _⟩
      · exact ⟨_, hmem _ (by simp), (hp.cons a).cons _⟩
    · exact ⟨_, hmem (w :: w :: r') (by simp), (hp.cons w).cons w⟩
  · refine ⟨w :: K, ?_, hK.cons w⟩
    unfold children
    simp only [List.mem_append]
    right
    rcases hw with rfl | rfl <;> simp

theorem len_kept_eq (k : Bool) (x : ℕ) (xs : List ℕ) :
    (kept k x xs).length = xs.length + (if k then 1 else 0) := by
  cases k <;> simp [kept]

theorem ks_mem (ka kb : Bool) {n m lev : ℕ} (hn : n = m + 2)
    (hl : m + (if ka then 1 else 0) + (if kb then 1 else 0) + 1 ≤ lev) : (ka, kb) ∈ ksOf n lev := by
  unfold ksOf
  cases ka <;> cases kb <;> simp only [if_true, if_false, Bool.false_eq_true] at hl <;>
    split_ifs <;> simp <;> omega

theorem mem_twoS {ks : List (Bool × Bool)} {k : Bool × Bool} (hk : k ∈ ks) (a b : ℕ) (r : List ℕ)
    (o : Fin 4) (h2 : o = 2 → k.2 = false) (h3 : o = 3 → k.1 = false) :
    opv AA o a b :: kept k.1 a (kept k.2 b r) ∈ twoS ks a b r := by
  unfold twoS
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨o, by fin_cases o <;> simp, k, ?_, rfl⟩
  unfold ksF
  split_ifs with e2 e3
  · exact List.mem_filter.2 ⟨hk, by simp [h2 e2]⟩
  · exact List.mem_filter.2 ⟨hk, by simp [h3 e3]⟩
  · exact hk

theorem two_or_one {K : List ℕ} {lev : ℕ} {q : ℕ × ℕ × List ℕ} (hq : q ∈ pairsOf K) (o : Fin 4)
    (k : Bool × Bool) (hk : k ∈ ksOf K.length lev)
    (hl : q.2.2.length + (if k.1 then 1 else 0) + (if k.2 then 1 else 0) + 1 ≤ lev) :
    ∃ c' ∈ childrenS K lev, c'.Perm (opv AA o q.1 q.2.1 :: kept k.1 q.1 (kept k.2 q.2.1 q.2.2)) := by
  have hp := pairsOf_sound hq
  have hKl := hp.length_eq
  simp only [List.length_cons] at hKl
  have hpair : ∀ k' ∈ ksOf K.length lev, ∀ o', (o' = 2 → k'.2 = false) → (o' = 3 → k'.1 = false) →
      opv AA o' q.1 q.2.1 :: kept k'.1 q.1 (kept k'.2 q.2.1 q.2.2) ∈ childrenS K lev := by
    intro k' hk' o' h2 h3
    unfold childrenS
    simp only [List.mem_append]
    left; left
    rw [List.mem_flatMap]
    exact ⟨q, hq, mem_twoS hk' _ _ _ o' h2 h3⟩
  have hone : ∀ x r', (x, r') ∈ picks K → ∀ ch ∈ oneS K.length lev x r', ch ∈ childrenS K lev := by
    intro x r' hr ch hch
    unfold childrenS
    simp only [List.mem_append]
    left; right
    rw [List.mem_flatMap]
    exact ⟨(x, r'), hr, hch⟩
  by_cases e2 : o = 2 ∧ k.2 = true
  · obtain ⟨rfl, hk2⟩ := e2
    obtain ⟨r', hr', hpr⟩ := pick_perm hp
    have hv : opv AA 2 q.1 q.2.1 = AA ^^^ q.1 := rfl
    rw [hv, hk2]
    cases hk1 : k.1
    · refine ⟨(AA ^^^ q.1) :: r', hone _ _ hr' _ ?_, ?_⟩
      · unfold oneS; split_ifs <;> simp
      · exact hpr.cons _
    · refine ⟨(AA ^^^ q.1) :: q.1 :: r', hone _ _ hr' _ ?_, ?_⟩
      · unfold oneS
        rw [if_pos (by rw [hk1, hk2] at hl; simp at hl; omega)]
        simp
      · exact (hpr.cons _).cons _
  · by_cases e3 : o = 3 ∧ k.1 = true
    · obtain ⟨rfl, hk1⟩ := e3
      have hp' : K.Perm (q.2.1 :: q.1 :: q.2.2) := hp.trans (List.Perm.swap _ _ _)
      obtain ⟨r', hr', hpr⟩ := pick_perm hp'
      have hv : opv AA 3 q.1 q.2.1 = AA ^^^ q.2.1 := rfl
      rw [hv, hk1]
      cases hk2 : k.2
      · refine ⟨(AA ^^^ q.2.1) :: r', hone _ _ hr' _ ?_, ?_⟩
        · unfold oneS; split_ifs <;> simp
        · exact hpr.cons _
      · refine ⟨(AA ^^^ q.2.1) :: q.2.1 :: r', hone _ _ hr' _ ?_, ?_⟩
        · unfold oneS
          rw [if_pos (by rw [hk1, hk2] at hl; simp at hl; omega)]
          simp
        · exact ((hpr.cons _).trans (List.Perm.swap _ _ _)).cons _
    · refine ⟨_, hpair k hk o (fun h => ?_) (fun h => ?_), List.Perm.refl _⟩
      · cases hk2 : k.2
        · rfl
        · exact absurd ⟨h, hk2⟩ e2
      · cases hk1 : k.1
        · rfl
        · exact absurd ⟨h, hk1⟩ e3

theorem child_perm2 {P c K : List ℕ} {lev : ℕ} (h : Child P c) (hK : K.Perm P) (hl : c.length ≤ lev) :
    ∃ c' ∈ childrenS K lev, c'.Perm c := by
  have hKl := hK.length_eq
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · obtain ⟨q, hq, hab, hp⟩ := pairs_complete hK
    simp only [List.length_cons, len_kept_eq] at hl hKl
    have hql : q.2.2.length = r.length := hp.length_eq
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨c', hc', hcp⟩ := two_or_one (lev := lev) hq o (ka, kb) (ks_mem ka kb (m := r.length) hKl (by omega)) (by simp only; omega)
      refine ⟨c', hc', hcp.trans ?_⟩
      rw [h1, h2]
      exact (kept_perm ka a (kept_perm kb b hp)).cons _
    · obtain ⟨c', hc', hcp⟩ := two_or_one (lev := lev) hq (swp o) (kb, ka) (ks_mem kb ka (m := r.length) hKl (by omega))
        (by simp only; omega)
      refine ⟨c', hc', hcp.trans ?_⟩
      rw [h1, h2, ← opv_swp]
      exact ((kept_perm kb b (kept_perm ka a hp)).trans (kept_swap kb ka b a r)).cons _
  · obtain ⟨r', hr', hp⟩ := pick_perm hK
    simp only [List.length_cons, len_kept_eq] at hl hKl
    have hmem : ∀ ch ∈ oneS K.length lev a r', ch ∈ childrenS K lev := by
      intro ch hch
      unfold childrenS
      simp only [List.mem_append]
      left; right
      rw [List.mem_flatMap]
      exact ⟨(a, r'), hr', hch⟩
    cases ka
    · have hw' : w = AA ^^^ a ∨ w = 0 ∨ w = AA := by
        rcases hw with e | e | e | ⟨_, e⟩
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)
        · cases e
      refine ⟨w :: r', hmem _ ?_, hp.cons _⟩
      unfold oneS
      split_ifs <;> rcases hw' with rfl | rfl | rfl <;> simp
    · have h1 : K.length + 1 ≤ lev := by simp at hl; omega
      refine ⟨w :: a :: r', hmem _ ?_, (hp.cons a).cons _⟩
      unfold oneS
      rw [if_pos h1]
      rcases hw with rfl | rfl | rfl | ⟨rfl, _⟩ <;> simp
  · refine ⟨w :: K, ?_, hK.cons w⟩
    simp only [List.length_cons] at hl
    have h1 : K.length + 1 ≤ lev := by omega
    unfold childrenS
    simp only [List.mem_append]
    right
    rw [if_pos h1]
    rcases hw with rfl | rfl <;> simp

/-! ### The certificate argument -/

theorem cert (t t2 : Tr) (ht : allE t t2 t = true) (hS : allS t t2 = true) {s : ℕ} {L : List ℕ}
    (h : Run TT AA s L) :
    ∀ f, Hom f → ∀ v, Mem t (srt (L.map f)) v → s ≤ v → False := by
  have step : ∀ {s : ℕ} {P c : List ℕ}, Child P c → Run TT AA s c →
      (∀ f, Hom f → ∀ v, Mem t (srt (c.map f)) v → s ≤ v → False) →
      ∀ f, Hom f → ∀ v, Mem t (srt (P.map f)) v → s + 1 ≤ v → False := by
    intro s P c hch hc ih f hf v hm hv
    have hK := allE_sound t t2 ht hm
    unfold chkE at hK
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hK
    have hcl : (c.map f).length ≤ v := by rw [List.length_map]; have := hc.inv.1; omega
    obtain ⟨c', hc'm, hc'p⟩ := child_perm2 (child_map hf hch) (srt_perm_self (P.map f)) hcl
    have hrun : Run TT AA s c' := Run.perm hc'p.symm (hc.mapH hf)
    rcases hK.2 c' hc'm with hf' | hl
    · rw [hrun.passOk (show s ≤ v - 1 by omega)] at hf'
      cases hf'
    · obtain ⟨g, hg, w, hw, hs⟩ := lookS_sound hS hl
      have e : srt (c'.map g) = srt (c.map (g ∘ f)) := by
        rw [← List.map_map]
        exact srt_perm (hc'p.map _)
      rw [e] at hw
      exact ih _ (hg.comp hf) w hw (by omega)
  induction h with
  | done s =>
    intro f hf v hm _
    have e : srt ([TT].map f) = [TT] := by
      rw [List.map_cons, List.map_nil, hf.2.2.2.2.1]
      rfl
    rw [e] at hm
    have hK := allE_sound t t2 ht hm
    unfold chkE at hK
    simp only [Bool.and_eq_true] at hK
    have : cmpL [TT] [TT] = Ordering.eq := by decide
    rw [this] at hK
    simp at hK
  | perm p _ ih =>
    intro f hf v hm hv
    rw [← srt_perm (p.map f)] at hm
    exact ih f hf v hm hv
  | mono _ ih =>
    intro f hf v hm hv
    exact ih f hf v hm (by omega)
  | @two s a b r o ka kb hc ih =>
    exact step (Or.inl ⟨a, b, r, o, ka, kb, rfl, rfl⟩) hc ih
  | @one s a w r ka hw hc ih =>
    by_cases htriv : w = a ∧ ka = false
    · obtain ⟨rfl, rfl⟩ := htriv
      intro f hf v hm hv
      exact ih f hf v hm (by omega)
    · refine step (Or.inr (Or.inl ⟨a, r, w, ka, rfl, ?_, rfl⟩)) hc ih
      rcases hw with rfl | rfl | rfl | rfl
      · cases ka
        · exact absurd ⟨rfl, rfl⟩ htriv
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
  | @const s w r hw hc ih =>
    exact step (Or.inr (Or.inr ⟨w, hw, rfl⟩)) hc ih


def cv0 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def cv1 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff00
def cv2 : ℕ := 0xffffffffffffffff0000000000000000
def cv3 : ℕ := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def cv4 : ℕ := 0xcccccccccccccccccccccccccccccccc
def cv5 : ℕ := 0xffff0000ffff0000ffff0000ffff0000
def cv6 : ℕ := 0xffffffff00000000ffffffff00000000
def cv7 : ℕ := 0xffffffffffffffff
def cv8 : ℕ := 0xff00ff00ff00ff00ff00ff00ff00ff
def cv9 : ℕ := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def cv10 : ℕ := 0xffffffff00000000ffffffff
def cv11 : ℕ := 0x33333333333333333333333333333333
def cv12 : ℕ := 0xffff0000ffff0000ffff0000ffff
def cv13 : ℕ := 0x55555555555555555555555555555555
def cv14 : ℕ := 0xffffffffcccccccccccccccccccccccc
def cv15 : ℕ := 0xffaaaaaaffaaaaaaffaaaaaaffaaaaaa
def cv16 : ℕ := 0xffffccccffffccccffffccccffffcccc
def cv17 : ℕ := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def cv18 : ℕ := 0xffccffccffccffccffccffccffccffcc
def cv19 : ℕ := 0xffffffffffffffffaaaaaaaaaaaaaaaa
def cv20 : ℕ := 0xffffccccccccccccffffcccccccccccc
def cv21 : ℕ := 0xffffaaaaaaaaaaaaffffaaaaaaaaaaaa
def cv22 : ℕ := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def cv23 : ℕ := 0xffffffffccccccccffffffffcccccccc
def cv24 : ℕ := 0xfffff0f0f0f0f0f0fffff0f0f0f0f0f0
def cv25 : ℕ := 0xffff000000000000ffff000000000000
def cv26 : ℕ := 0xffff0000ff000000ffff0000ff000000
def cv27 : ℕ := 0xffffffff00000000ffff000000000000
def cv28 : ℕ := 0xffffffffff00ff00ffffffffff00ff00
def cv29 : ℕ := 0xffffffffffffffffffff0000ffff0000
def cv30 : ℕ := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def cv31 : ℕ := 0xfffffffffffffffff0f0f0f0f0f0f0f0
def cv32 : ℕ := 0xffffccccffccccccffffccccffcccccc
def cv33 : ℕ := 0xffffffffaaaaaaaaffffaaaaaaaaaaaa
def cv34 : ℕ := 0xffffffffccccccccffffcccccccccccc
def cv35 : ℕ := 0xffffaaaaffaaaaaaffffaaaaffaaaaaa
def cv36 : ℕ := 0xffccccccffccccccffccccccffcccccc
def cv37 : ℕ := 0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa
def cv38 : ℕ := 0xffffff00ff00ff00ffffff00ff00ff00
def cv39 : ℕ := 0xffffffffffffffffffff000000000000
def cv40 : ℕ := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def cv41 : ℕ := 0xff000000ff000000ff000000ff000000
def cv42 : ℕ := 0xffffffff000000000000000000000000
def cv43 : ℕ := 0xffffffffff000000ffffffffff000000
def cv44 : ℕ := 0xffffffffffff0000ffff0000ffff0000
def cv45 : ℕ := 0xfffff0f0fff0f0f0fffff0f0fff0f0f0
def cv46 : ℕ := 0xfffffffff0f0f0f0fffff0f0f0f0f0f0
def cv47 : ℕ := 0xecececececececececececececececec
def cv48 : ℕ := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def cv49 : ℕ := 0xffffffffffffffffff00ff00ff00ff00
def cv50 : ℕ := 0xeecceecceecceecceecceecceecceecc
def cv51 : ℕ := 0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa
def cv52 : ℕ := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def cv53 : ℕ := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def cv54 : ℕ := 0xfaf0faf0faf0faf0faf0faf0faf0faf0
def cv55 : ℕ := 0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0
def cv56 : ℕ := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def cv57 : ℕ := 0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0
def cv58 : ℕ := 0xaa00aa00aa00aa00aa00aa00aa00aa00
def cv59 : ℕ := 0xcccccccccccccccc0000000000000000
def cv60 : ℕ := 0xfafafafafafafafafafafafafafafafa
def cv61 : ℕ := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def cv62 : ℕ := 0xff00aa00ff00aa00ff00aa00ff00aa00
def cv63 : ℕ := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def cv64 : ℕ := 0xfffffffff0f0f0f0fffffffff0f0f0f0
def cv65 : ℕ := 0xffffffffcccccccc0000000000000000
def cv66 : ℕ := 0xffffffffccccccccffffffff00000000
def cv67 : ℕ := 0xffffaa00ffffaa00ffffaa00ffffaa00
def cv68 : ℕ := 0xffffffffff00ff00ff00ff00ff00ff00
def cv69 : ℕ := 0xffffffffffffffffff000000ff000000
def cv70 : ℕ := 0xff88ff88ff88ff88ff88ff88ff88ff88
def cv71 : ℕ := 0xffccffccffccffccff00ff00ff00ff00
def cv72 : ℕ := 0xffffffffffffffff8888888888888888
def cv73 : ℕ := 0xffffffffffffffffaa00aa00aa00aa00
def cv74 : ℕ := 0xffffffffa0a0a0a0ffffffffa0a0a0a0
def cv75 : ℕ := 0xffffffffc0c0c0c0ffffffffc0c0c0c0
def cv76 : ℕ := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0
def cv77 : ℕ := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def cv78 : ℕ := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def cv79 : ℕ := 0xffffffffffffffffc0c0c0c0c0c0c0c0
def t0 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x0, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [0x0, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N Tr.E [0x0, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x0, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [0xffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xffff0000ffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xff00ff00ff00ff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xffffff00ffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)) [0xf0f0f0f0f0f0f0f, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xf0fffff0f0fffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0x3333333333333333, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t1 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x5555555555555555, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x5555ffff5555ffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 (Tr.N Tr.E [0x55ff55ff55ff55ff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)) [0x5f5f5f5f5f5f5f5f, cv3, cv4, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [0x7777777777777777, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xaaaaaaaaaaaaaaaa, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)) [0xaaaaaaaaaaaaaaaa, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xcccccccccccccccc, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [0xcccccccccccccccc, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xf0f0f0f0f0f0f0f0, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N Tr.E [0xf0f0f0f0f0f0f0f0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xff00ff00ff00ff00, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)))
def u2 : Tr := Tr.N t0 [0x3f3f3f3f3f3f3f3f, cv3, cv4, cv0, cv1, cv5, cv6] 7 t1
def t3 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffff0000, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [0xffff0000ffff0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xffffffff00000000, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)) [0xffffffff00000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xffffffffcccccccc, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xffffffffffff0000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)) [cv7, cv7, cv3, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv10, cv12, cv3, cv4, cv0, cv1] 7 Tr.E) [cv7, cv10, cv8, cv3, cv4, cv0, cv5] 7 (Tr.N Tr.E [cv7, cv10, cv9, cv3, cv4, cv1, cv5] 7 Tr.E)) [cv7, cv10, cv11, cv3, cv0, cv1, cv5] 7 (Tr.N (Tr.N Tr.E [cv7, cv10, cv13, cv4, cv0, cv1, cv5] 7 Tr.E) [cv7, cv10, cv3, cv4, cv0, cv1, cv5] 8 Tr.E)))
def t4 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv7, cv12, cv9, cv3, cv4, cv1, cv6] 7 (Tr.N Tr.E [cv7, cv12, cv11, cv3, cv0, cv1, cv6] 7 Tr.E)) [cv7, cv12, cv13, cv4, cv0, cv1, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv12, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv12, cv3, cv4, cv0, cv1, cv6] 8 Tr.E)) [cv7, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv8, cv9, cv3, cv4, cv5, cv6] 7 Tr.E) [cv7, cv8, cv11, cv3, cv0, cv5, cv6] 7 Tr.E) [cv7, cv8, cv3, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv8, cv3, cv4, cv0, cv5, cv6] 8 Tr.E) [cv7, cv9, cv11, cv3, cv1, cv5, cv6] 7 Tr.E)))
def u5 : Tr := Tr.N t3 [cv7, cv10, cv3, cv4, cv0, cv1, cv5, cv6] 8 t4
def u6 : Tr := Tr.N u2 [0xff00ff00ff00ff00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 u5
def t7 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv9, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv9, cv3, cv4, cv1, cv5, cv6] 8 (Tr.N Tr.E [cv7, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv7, cv11, cv13, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv11, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv11, cv3, cv0, cv1, cv5, cv6] 8 Tr.E)) [cv7, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv13, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv13, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N Tr.E [cv7, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv7, 0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv52, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, 0xa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaa, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)))
def t8 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [cv7, cv58, cv3, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N Tr.E [cv7, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)) [cv7, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, 0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, 0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)) [cv7, cv3, cv3, cv4, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, 0xaaaaaaaaaaaaaaaaffffffffffffffff, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv53, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)))
def u9 : Tr := Tr.N t7 [cv7, 0xa0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0, cv3, cv4, cv1, cv5, cv6] 7 t8
def t10 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv59, cv4, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv6] 7 (Tr.N Tr.E [cv7, cv3, cv4, cv4, cv0, cv1, cv5, cv6] 8 Tr.E)) [cv7, cv3, cv4, 0xccccccccccccccccffffffffffffffff, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, cv6] 7 Tr.E) [cv7, cv3, cv4, cv40, cv0, cv1, cv5, cv6] 8 Tr.E)) [cv7, cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv1, cv5, cv6] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, 0xf0f00000f0f00000f0f0f0f0f0f0f0f0, cv1, cv5, cv6] 7 Tr.E) [cv7, cv3, cv4, 0xf0f00000f0f00000ffff0000ffff0000, cv0, cv1, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv6] 7 Tr.E)))
def t11 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv0, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, 0xf0f0f0f0f0f0f0f0ffffffffffffffff, cv1, cv5, cv6] 8 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv60, cv1, cv5, cv6] 8 Tr.E)) [cv7, cv3, cv4, cv0, cv61, cv1, cv5, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv41, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, 0xff000000ff000000ff00ff00ff00ff00, cv5, cv6] 7 Tr.E)) [cv7, cv3, cv4, cv0, 0xff000000ff000000ffff0000ffff0000, cv1, cv6] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv62, cv5, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv1, cv5, cv6] 8 Tr.E)))
def u12 : Tr := Tr.N t10 [cv7, cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv5, cv6] 8 t11
def u13 : Tr := Tr.N u9 [cv7, cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv5, cv6] 8 u12
def u14 : Tr := Tr.N u6 [cv7, cv9, cv13, cv4, cv1, cv5, cv6] 7 u13
def t15 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6] 8 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv18, cv5, cv6] 8 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv30, cv5, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv25, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6] 7 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv26, cv6] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6] 7 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv5, cv6] 8 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, 0xffff0000ffff0000ffffffffffffffff, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv22, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv16, cv6] 8 Tr.E)))
def t16 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv63, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000] 7 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6] 8 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, cv42, cv6] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv27] 7 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, cv6] 9 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv6] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff00000000ffffffffffffffff] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv17] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv23] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv64] 8 Tr.E)))
def u17 : Tr := Tr.N t15 [cv7, cv3, cv4, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000] 7 t16
def t18 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv19] 8 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv31] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv49] 8 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv29] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffffffffff00000000] 8 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffffffffffffffffff] 8 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffffffaaaaaaaa] 7 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000fffffffff0f0f0f0] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffffffff00ff00] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888] 7 Tr.E)))
def t19 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv5, cv75] 7 (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, 0xffffffffcc00cc00ffffffffcc00cc00] 7 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv5, cv66] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv5, cv43] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6] 7 Tr.E)) [cv7, cv3, cv4, cv0, cv1, cv76, cv6] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, cv67, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv77, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, cv1, cv6, cv44] 7 Tr.E)))
def u20 : Tr := Tr.N t18 [cv7, cv3, cv4, cv0, cv1, cv5, cv74] 7 t19
def u21 : Tr := Tr.N u17 [cv7, cv3, cv4, cv0, cv1, cv5, cv6, cv28] 8 u20
def t22 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv70, cv5, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, cv78, cv5, cv6] 7 (Tr.N Tr.E [cv7, cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6] 7 Tr.E)) [cv7, cv3, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv71, cv5, cv6] 7 Tr.E) [cv7, cv3, cv4, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6] 7 Tr.E)) [cv7, cv3, cv4, cv0, cv5, cv38, cv6] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv0, cv5, cv6, cv68] 7 Tr.E) [cv7, cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6] 7 (Tr.N Tr.E [cv7, cv3, cv4, cv54, cv1, cv5, cv6] 7 Tr.E)) [cv7, cv3, cv4, cv55, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv1, cv56, cv5, cv6] 7 Tr.E) [cv7, cv3, cv4, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6] 7 Tr.E)))
def t23 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv4, cv1, cv5, cv6, cv57] 7 Tr.E) [cv7, cv3, 0xccccccccccccccccffffccccffffcccc, cv0, cv1, cv5, cv6] 7 (Tr.N Tr.E [cv7, cv3, cv47, cv0, cv1, cv5, cv6] 7 Tr.E)) [cv7, cv3, cv50, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv3, cv0, cv1, cv36, cv5, cv6] 7 Tr.E) [cv7, cv3, cv0, cv1, cv5, cv20, cv6] 7 Tr.E)) [cv7, cv3, cv0, cv1, cv5, cv20, cv17] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv3, cv0, cv1, cv5, cv6, cv14] 7 Tr.E) [cv7, cv3, cv1, cv32, cv45, cv6] 5 Tr.E) [cv7, cv4, cv48, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv4, cv51, cv0, cv1, cv5, cv6] 7 Tr.E) [cv7, cv4, cv0, cv1, cv15, cv5, cv6] 7 Tr.E)))
def u24 : Tr := Tr.N t22 [cv7, cv3, cv4, cv1, cv5, cv24, cv6] 7 t23
def t25 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv7, cv4, cv0, cv1, cv5, cv6, cv37] 7 Tr.E) [cv7, cv4, cv0, cv1, cv21, cv16, cv6] 6 (Tr.N Tr.E [cv7, cv4, cv1, cv5, cv33, cv46] 5 Tr.E)) [cv7, cv0, cv1, cv5, cv21, cv20, cv6] 6 (Tr.N (Tr.N Tr.E [cv7, cv0, cv1, cv5, cv33, cv34] 5 Tr.E) [cv7, cv0, cv1, cv35, cv32, cv6] 5 Tr.E)) [0xffff000000000000ffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffff0000ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0xffffffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xf0f0f0f000000000f0f0f0f, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xf0f0f0f00000f0f0f0f0f0f, cv4, cv1, cv5, cv33, cv2] 5 Tr.E) [0xf0f0f0f0f0f0f0f0f0f0f0f, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)))
def t26 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x3333333300000000ffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x333333330000333333333333, cv0, cv1, cv5, cv33, cv2] 5 (Tr.N Tr.E [0x333333333333333333333333, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0x33333333ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [0x33ff33ff0000000033ff33ff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x3f3f3f3f000000003f3f3f3f, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [0x555555550000000055555555, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x555555550000000055555555, cv3, cv0, cv1, cv5, cv20, cv2] 6 Tr.E) [0x555555550000555555555555, cv4, cv1, cv5, cv46, cv2] 5 Tr.E) [0x555555550000555555555555, cv0, cv1, cv5, cv34, cv2] 5 (Tr.N (Tr.N Tr.E [0x555555555555555555555555, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x55ff55ff0000000055ff55ff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)))
def u27 : Tr := Tr.N t25 [0x333333330000000033333333, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 t26
def u28 : Tr := Tr.N u24 [cv7, cv4, cv0, cv1, cv5, cv21, cv6] 7 u27
def u29 : Tr := Tr.N u21 [cv7, cv3, cv4, cv0, 0xff00ff00ff00ff00fff0fff0fff0fff0, cv5, cv6] 7 u28
def u30 : Tr := Tr.N u14 [cv7, cv3, cv4, cv0, cv1, 0xff00ff00ff00ff00ffffffffffffffff, cv5, cv6] 8 u29
def t31 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x777777770000000077777777, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0xaaaaaaaa00000000aaaaaaaa, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N Tr.E [0xaaaaaaaa00000000aaaaaaaa, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xaaaaaaaaaaaaaaaaaaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xcccccccc00000000cccccccc, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [0xcccccccc00000000cccccccc, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xcccccccccccccccccccccccc, cv3, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xf0f0f0f000000000f0f0f0f0, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [0xf0f0f0f000000000f0f0f0f0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xf0f0f0f0f0f0f0f0f0f0f0f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xff00ff0000000000ff00ff00, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N (Tr.N Tr.E [0xff00ff0000000000ff00ff00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xff00ff00ff00ff00ff00ff00, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)))
def t32 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff000000000000ffff0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xffff0000ffff0000ffff0000, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N Tr.E [0xfffff0f000000000fffff0f0, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [0xffffff0000000000ffffff00, cv3, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [0xffffffff0000000000000000, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [0xffffffff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xffffffff00000000cccccccc, cv3, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xffffffff00000000ffff0000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [cv10, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv12, cv9, cv3, cv4, cv1, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv12, cv11, cv3, cv0, cv1, cv2] 7 Tr.E) [cv10, cv12, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E)))
def u33 : Tr := Tr.N t31 [0xffff000000000000ffff0000, cv10, cv3, cv4, cv0, cv1, cv5, cv2] 8 t32
def t34 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv9, cv11, cv3, cv1, cv5, cv2] 7 Tr.E) [cv10, cv9, cv13, cv4, cv1, cv5, cv2] 7 (Tr.N Tr.E [cv10, cv9, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv9, cv3, cv4, cv1, cv5, cv2] 8 Tr.E) [cv10, cv11, cv13, cv0, cv1, cv5, cv2] 7 Tr.E)) [cv10, cv11, cv3, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv10, cv11, cv3, cv0, cv1, cv5, cv2] 8 (Tr.N Tr.E [cv10, cv13, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv13, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, 0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E)))
def t35 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [cv10, cv58, cv3, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N Tr.E [cv10, 0xaa00aa00aaaaaaaaaa00aa00aaaaaaaa, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [cv10, 0xaa00aa00ff00ff00aa00aa00ff00ff00, cv3, cv4, cv0, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [cv10, 0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv10, 0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, 0xaaaaaaaaffffffffaaaaaaaaffffffff, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv53, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv2] 7 Tr.E)))
def u36 : Tr := Tr.N t34 [cv10, cv52, cv3, cv4, cv0, cv1, cv5, cv2] 8 t35
def u37 : Tr := Tr.N u33 [cv10, cv12, cv3, cv4, cv0, cv1, cv2] 8 u36
def t38 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv5, cv2] 8 (Tr.N Tr.E [cv10, cv3, cv59, cv4, cv0, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv4, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, 0xccccccccffffffffccccccccffffffff, cv0, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv40, cv0, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv1, cv5, cv2] 8 (Tr.N Tr.E [cv10, cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv2] 7 Tr.E) [cv10, cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv5, cv2] 8 Tr.E)))
def t39 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, 0xf0f0f0f0fffffffff0f0f0f0ffffffff, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv60, cv1, cv5, cv2] 8 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv61, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv3, cv4, cv0, cv41, cv1, cv5, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv62, cv5, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv1, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, 0xff00ff00ffffffffff00ff00ffffffff, cv5, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv2] 8 Tr.E)))
def u40 : Tr := Tr.N t38 [cv10, cv3, cv4, cv0, cv0, cv1, cv5, cv2] 8 t39
def t41 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv30, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv25, cv5, cv2] 8 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv2] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv26, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv2] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv5, cv5, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, 0xffff0000ffffffffffff0000ffffffff, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv22, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv16, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv63, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv2] 8 Tr.E)))
def t42 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv17, cv2] 8 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv65] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv5, cv23, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv64, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv28, cv2] 8 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffff00000000000000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv2] 9 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv2, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv2, 0xffffffffffffffff00000000ffffffff] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv2, cv19] 8 Tr.E)))
def u43 : Tr := Tr.N t41 [cv10, cv3, cv4, cv0, cv1, cv5, cv42, cv2] 8 t42
def u44 : Tr := Tr.N u40 [cv10, cv3, cv4, cv0, cv1, cv18, cv5, cv2] 8 u43
def u45 : Tr := Tr.N u37 [cv10, cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv1, cv5, cv2] 8 u44
def t46 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv2, cv31] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv2, cv49] 8 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv2, cv29] 8 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv5, cv2, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv2, 0xffffffffffffffffffffffffffffffff] 8 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffffffff00000000aaaaaaaa] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffffffff00000000f0f0f0f0] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffffffff00000000ff00ff00] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv72] 7 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv5, cv73] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv79] 7 Tr.E)))
def t47 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv5, cv69] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv5, cv39] 7 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, 0xffff0000ffffaaaaffff0000ffffaaaa, cv2] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, 0xffff0000ffffccccffff0000ffffcccc, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv76, cv2] 7 Tr.E)) [cv10, cv3, cv4, cv0, cv1, cv67, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, cv77, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv1, cv44, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, cv70, cv5, cv2] 7 Tr.E)))
def u48 : Tr := Tr.N t46 [cv10, cv3, cv4, cv0, cv1, cv5, 0xfffffffffffffffff0f00000f0f00000] 7 t47
def t49 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv2] 7 (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv71, cv5, cv2] 7 Tr.E)) [cv10, cv3, cv4, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv0, cv5, cv38, cv2] 7 Tr.E) [cv10, cv3, cv4, cv0, cv5, cv68, cv2] 7 Tr.E)) [cv10, cv3, cv4, 0xf0f0f0f0fff0fff0f0f0f0f0fff0fff0, cv1, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv2] 7 Tr.E) [cv10, cv3, cv4, cv54, cv1, cv5, cv2] 7 Tr.E) [cv10, cv3, cv4, cv55, cv1, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv1, cv56, cv5, cv2] 7 Tr.E) [cv10, cv3, cv4, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv2] 7 Tr.E)))
def t50 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv3, cv4, cv1, cv5, cv57, cv2] 7 Tr.E) [cv10, cv3, cv47, cv0, cv1, cv5, cv2] 7 (Tr.N Tr.E [cv10, cv3, cv50, cv0, cv1, cv5, cv2] 7 Tr.E)) [cv10, cv3, cv0, cv1, cv36, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv3, cv0, cv1, cv5, cv20, cv2] 7 Tr.E) [cv10, cv3, cv0, cv1, cv5, cv14, cv2] 7 Tr.E)) [cv10, cv3, cv1, cv32, cv45, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv4, cv48, cv0, cv1, cv5, cv2] 7 Tr.E) [cv10, cv4, cv51, cv0, cv1, cv5, cv2] 7 Tr.E) [cv10, cv4, cv0, cv1, cv15, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv4, cv0, cv1, cv5, cv21, cv2] 7 Tr.E) [cv10, cv4, cv0, cv1, cv5, cv37, cv2] 7 Tr.E)))
def u51 : Tr := Tr.N t49 [cv10, cv3, cv4, cv1, cv5, cv24, cv2] 7 t50
def u52 : Tr := Tr.N u48 [cv10, cv3, cv4, cv0, cv78, cv5, cv2] 7 u51
def t53 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv0, cv1, cv5, cv21, cv20, cv2] 6 Tr.E) [cv10, cv0, cv1, cv35, cv32, cv2] 5 (Tr.N Tr.E [0xffffffff0000ffffffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [0xffffffff33333333ffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [0xffffffffffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xffffffffff000000ffffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [0xf0f0f0f0f0f00000f0f0f0f0f0f, cv3, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xf0fffffffff00000f0fffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x3333333333330000333333333333, cv3, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [0x3333333333330000333333333333, cv3, cv0, cv1, cv5, cv17, cv2] 6 Tr.E)) [0x3333333333330000333333333333, cv0, cv1, cv5, cv21, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaa0000aaaaaaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xf0f0f0f0f0f00000f0f0f0f0f0f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)))
def t54 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffffffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xffffffffffff0000ffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xf000f000f000f0f0f0f0f0f0f0f0f, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xf000f000f000f0f0f0f0f0f0f0f0f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xff00ff00ff00ffffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x3030303030303030303030303030303, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x3030303030303030f0f0f0f0f0f0f0f, cv3, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x7070707070707070707070707070707, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0xf000f000f000f000f000f000f000f00, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u55 : Tr := Tr.N t53 [0xff00ff00ff000000ff00ff00ff00, cv3, cv4, cv0, cv5, cv6, cv2] 7 t54
def t56 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xf000f00ff00ff000f000f00ff00ff00, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0xf0f00000f0f00000f0f00000f0f0000, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xf0f00000f0f00000f0f00000f0f0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xf0f0f0f0f0f00000f0f0f0f0f0f0000, cv3, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv11, cv13, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv9, cv11, cv3, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv11, cv3, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, 0x88888888888888888888888888888888, cv3, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv52, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)))
def t57 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv9, 0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv9, 0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, 0xafafafafafafafafafafafafafafafaf, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv40, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv60, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv41, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u58 : Tr := Tr.N t56 [cv9, cv58, cv3, cv4, cv1, cv5, cv6, cv2] 8 t57
def u59 : Tr := Tr.N u55 [0xf000f000f000f000f000f000f000f00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 u58
def u60 : Tr := Tr.N u52 [cv10, cv4, cv0, cv1, cv21, cv16, cv2] 6 u59
def u61 : Tr := Tr.N u45 [cv10, cv3, cv4, cv0, cv1, cv5, cv2, 0xffffffffffffffffcccccccccccccccc] 8 u60
def u62 : Tr := Tr.N u30 [0x5f5f5f5f000000005f5f5f5f, cv3, cv4, cv0, cv1, cv5, cv2] 7 u61
def t63 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv62, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv9, cv3, cv4, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, cv2] 7 Tr.E)) [cv9, cv3, cv4, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, 0xff00ff00ff00ff000f000f000f000f00, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, 0xff0f0000ff0f0000ff0f0000ff0f0000, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, 0xff0fff0fff0fff0fff0fff0fff0fff0f, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6, cv2] 7 (Tr.N Tr.E [cv9, cv3, cv4, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv18, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv30, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, cv25, cv5, cv6, cv2] 8 Tr.E)))
def t64 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv26, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 7 (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv5, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv5, 0xffff0f0fffff0f0fffff0f0fffff0f0f, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv22, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv16, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv5, cv63, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv28, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv2] 9 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv2, cv49] 8 Tr.E)))
def u65 : Tr := Tr.N t63 [cv9, cv3, cv4, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv2] 7 t64
def t66 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv72] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv73] 7 Tr.E)) [cv9, cv3, cv4, cv1, cv5, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv79] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, 0xfffffffffffffffff0f00000f0f00000] 7 Tr.E)) [cv9, cv3, cv4, cv1, cv5, cv6, cv69] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv39] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, 0xffffffff0f000f00ffffffff0f000f00, cv2] 7 (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E)) [cv9, cv3, cv4, cv1, cv5, cv74, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv75, cv2] 7 Tr.E)))
def t67 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv66, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv43, cv2] 7 (Tr.N Tr.E [cv9, cv3, 0xcfcccfcccfcccfcccfcccfcccfcccfcc, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv9, cv3, cv47, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv50, cv1, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv1, cv36, cv5, cv6, cv2] 7 Tr.E)) [cv9, cv3, cv1, cv5, cv20, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv1, cv5, cv20, cv17, cv2] 6 Tr.E) [cv9, cv3, cv1, cv5, cv6, cv14, cv2] 7 Tr.E) [cv9, cv1, cv5, cv21, cv20, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv9, cv1, cv5, cv33, cv34, cv2] 5 Tr.E) [0xf0f0f0f0f0f0f0fffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u68 : Tr := Tr.N t66 [cv9, cv3, cv4, cv1, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 7 t67
def u69 : Tr := Tr.N u65 [cv9, cv3, cv4, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffffffffff] 8 u68
def t70 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xf0f0f0fffffffff0f0f0f0fffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x11111111111111111111111111111111, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0x11111111111111115555555555555555, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0x13131313131313131313131313131313, cv3, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0x22222222222222222222222222222222, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x22222222222222222222222222222222, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x2222222222222222aaaaaaaaaaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [0x30303030303030303030303030303030, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x30303030303030303030303030303030, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x3030303030303030f0f0f0f0f0f0f0f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0x32323232323232323232323232323232, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def t71 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x33003300330033003300330033003300, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x3300330033003300ff00ff00ff00ff00, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N Tr.E [0x33003300ff00ff0033003300ff00ff00, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)) [0x33330000333300003333000033330000, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x33330000333300003333000033330000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x3333000033330000ffff0000ffff0000, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E)) [0x33333333000000003333333300000000, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x33333333000000003333333300000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x3333333300000000ffffffff00000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x33333333333333330000000000000000, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x33333333333333330000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x33333333333333333333333300000000, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def u72 : Tr := Tr.N t70 [0x33003300330033003300330033003300, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 t71
def t73 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv13, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, cv13, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv11, 0x88888888888888888888888888888888, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv11, cv52, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv11, cv58, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv11, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv11, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv11, 0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, 0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t74 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv11, cv3, 0xcccccccc00000000cccccccc00000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv11, cv3, cv59, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv11, cv3, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv40, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, 0xf000f000f000f000f000f000f000f000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u75 : Tr := Tr.N t73 [cv11, cv3, cv53, cv0, cv1, cv5, cv6, cv2] 8 t74
def u76 : Tr := Tr.N u72 [cv11, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 u75
def u77 : Tr := Tr.N u69 [0xf0f0f0f0f0fffff0f0f0f0f0f0fffff, cv3, cv4, cv1, cv5, cv6, cv2] 7 u76
def t78 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, 0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3, cv1, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv60, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv11, cv3, cv0, cv61, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv11, cv3, cv0, cv41, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, 0xff003300ff003300ff003300ff003300, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, cv62, cv5, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv11, cv3, cv0, cv1, 0xff330000ff330000ff330000ff330000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, 0xff33ff33ff33ff33ff33ff33ff33ff33, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6, cv2] 7 Tr.E)))
def t79 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv18, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv30, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv25, cv5, cv6, cv2] 8 Tr.E)) [cv11, cv3, cv0, cv1, 0xffff000033330000ffff000033330000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, cv26, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv5, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, 0xffff333300000000ffff333300000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, 0xffff3333ffff3333ffff3333ffff3333, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv22, cv6, cv2] 8 Tr.E)))
def u80 : Tr := Tr.N t78 [cv11, cv3, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 8 t79
def t81 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv63, cv6, cv2] 8 (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv42, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv5, cv27, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv6, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, 0xffffffff33333333ffffffff33333333, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv17, cv2] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv65] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv23, cv2] 8 Tr.E)))
def t82 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv28, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, 0xffffffffffff00000000000000000000] 7 (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E)) [cv11, cv3, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv2, cv2] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff3333333333333333] 8 Tr.E)) [cv11, cv3, cv0, cv1, cv5, cv6, cv2, cv19] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv2, cv31] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv2, cv49] 8 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv2, cv29] 8 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 Tr.E)))
def u83 : Tr := Tr.N t81 [cv11, cv3, cv0, cv1, cv5, cv6, cv64, cv2] 8 t82
def u84 : Tr := Tr.N u80 [cv11, cv3, cv0, cv1, cv5, cv16, cv6, cv2] 8 u83
def t85 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, 0xffffffffffffffff3333000033330000] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv72] 7 (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv5, cv6, cv73] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv79] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f00000f0f00000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv6, cv69] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv6, cv39] 7 (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv5, cv74, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv75, cv2] 7 Tr.E)))
def t86 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv5, cv66, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, cv5, cv43, cv2] 7 (Tr.N Tr.E [cv11, cv3, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv76, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, cv67, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv1, cv77, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, cv1, cv6, cv44, cv2] 7 Tr.E) [cv11, cv3, cv0, cv70, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv78, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 7 Tr.E)))
def u87 : Tr := Tr.N t85 [cv11, cv3, cv0, cv1, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 7 t86
def t88 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv0, cv71, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv11, cv3, cv0, cv5, cv38, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv0, cv5, cv6, cv68, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv11, cv3, cv54, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv3, cv55, cv1, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, cv1, cv56, cv5, cv6, cv2] 7 Tr.E) [cv11, cv3, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv3, cv1, cv5, cv24, cv6, cv2] 7 Tr.E) [cv11, cv3, cv1, cv5, cv6, cv57, cv2] 7 Tr.E)))
def t89 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv11, cv51, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv11, cv0, cv1, cv15, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv11, cv0, cv1, cv5, cv21, cv6, cv2] 7 Tr.E)) [cv11, cv0, cv1, cv5, cv6, cv37, cv2] 7 (Tr.N (Tr.N Tr.E [cv11, cv0, cv1, cv21, cv16, cv6, cv2] 6 Tr.E) [cv11, cv1, cv5, cv33, cv46, cv2] 5 Tr.E)) [0x333333333333333333333333ffffffff, cv3, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x3333333333333333ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x33333333ffffffff33333333ffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x3333ffff3333ffff3333ffff3333ffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x33ff33ff0000000033ff33ff00000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x33ff33ff33ff33ff33ff33ff33ff33ff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u90 : Tr := Tr.N t88 [cv11, cv48, cv0, cv1, cv5, cv6, cv2] 7 t89
def u91 : Tr := Tr.N u87 [cv11, cv3, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6, cv2] 7 u90
def u92 : Tr := Tr.N u84 [cv11, cv3, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffffffffff] 8 u91
def u93 : Tr := Tr.N u77 [cv11, cv3, cv0, cv0, cv1, cv5, cv6, cv2] 8 u92
def t94 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x3f003f003f003f003f003f003f003f00, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0x3f3f00003f3f00003f3f00003f3f0000, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N Tr.E [0x3f3f3f3f000000003f3f3f3f00000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E)) [0x3f3f3f3f3f3f3f3f0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [0x3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x70707070707070707070707070707070, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)) [0x77007700770077007700770077007700, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x77770000777700007777000077770000, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0x77777777777777777777777777777777, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0x80808080808080808080808080808080, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x88008800880088008800880088008800, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x88880000888800008888000088880000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x88888888888888888888888888888888, cv52, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t95 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, cv5, cv6, cv72] 8 Tr.E) [0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2] 8 (Tr.N Tr.E [0x88888888888888888888888888888888, cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x88888888888888888888888888888888, cv3, cv40, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x88888888888888888888888888888888, cv48, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x8888888888888888ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)) [0x88888888ffffffff88888888ffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0xa000a000a000a000a000a000a000a000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xa0a00000a0a00000a0a00000a0a00000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xa0a0a0a000000000a0a0a0a000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xa0a0a0a0a0a0a0a00000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u96 : Tr := Tr.N t94 [0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 t95
def t97 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv52, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv52, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 8 (Tr.N Tr.E [cv52, cv3, cv4, cv0, cv1, cv5, cv74, cv2] 8 Tr.E)) [cv52, cv3, cv4, cv0, cv1, cv76, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv52, cv3, cv4, cv0, cv78, cv5, cv6, cv2] 8 Tr.E) [cv52, cv3, cv4, cv60, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv52, cv3, cv4, cv1, cv5, cv6, cv2, cv31] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv52, cv3, cv4, cv1, cv5, cv6, cv79] 7 Tr.E) [cv52, cv3, cv47, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv52, cv4, cv48, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv52, cv4, cv0, cv60, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv52, cv4, cv0, cv1, cv5, cv27, cv19] 6 Tr.E) [cv52, cv4, cv0, cv1, cv5, cv6, cv2, cv19] 8 Tr.E)))
def t98 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv52, cv4, cv0, cv1, cv5, cv6, cv19, cv29] 7 Tr.E) [cv52, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv72] 6 (Tr.N Tr.E [cv52, cv4, cv0, cv1, cv76, cv6, cv2, cv19] 7 Tr.E)) [cv52, cv4, cv0, cv1, cv76, cv6, cv72] 6 (Tr.N (Tr.N Tr.E [cv52, cv4, cv0, cv1, cv6, cv44, cv19] 6 Tr.E) [cv52, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xa0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xa0a0a0a0a0a0a0a0f0f0f0f0f0f0f0f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0xa0a0a0a0a0a0a0a0ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xa0a0a0a0ffffffffa0a0a0a0ffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N Tr.E [0xa0a0ffffa0a0ffffa0a0ffffa0a0ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0xa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)))
def u99 : Tr := Tr.N t97 [cv52, cv4, cv0, cv1, cv5, cv6, cv72] 7 t98
def u100 : Tr := Tr.N u96 [cv52, cv3, cv53, cv4, cv1, cv5, cv6, cv2] 8 u99
def t101 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv61, cv1, cv5, cv6, cv2] 8 Tr.E) [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv27, cv2] 6 (Tr.N Tr.E [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv6, cv2, cv29] 7 (Tr.N (Tr.N Tr.E [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 7 Tr.E) [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, cv2] 7 Tr.E)) [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv6, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 6 Tr.E) [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8, cv5, cv6, cv2] 7 (Tr.N Tr.E [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv47, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xaa000000aa000000aa000000aa000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaa00aa0000000000aa00aa0000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t102 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv58, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv58, cv3, cv4, cv0, cv41, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv58, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E)) [cv58, cv3, cv4, cv0, cv1, cv5, cv6, cv73] 8 (Tr.N (Tr.N Tr.E [cv58, cv3, cv4, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 8 Tr.E) [cv58, cv3, cv4, cv0, cv1, cv67, cv6, cv2] 8 Tr.E)) [cv58, cv3, cv4, cv0, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv58, cv3, cv4, cv0, cv26, cv6, cv2] 7 Tr.E) [cv58, cv3, cv4, cv0, cv5, cv6, cv28, cv2] 8 Tr.E) [cv58, cv3, cv4, cv0, cv5, cv43, cv2] 7 (Tr.N (Tr.N Tr.E [cv58, cv3, cv4, cv54, cv1, cv5, cv6, cv2] 8 Tr.E) [cv58, cv3, cv50, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u103 : Tr := Tr.N t101 [0xaa00aa00aa00aa000000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 t102
def t104 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv58, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 8 Tr.E) [cv58, cv4, cv0, cv1, cv5, cv6, cv17, cv2] 8 (Tr.N Tr.E [cv58, cv4, cv0, cv1, cv5, cv17, cv23, cv2] 7 Tr.E)) [cv58, cv50, cv0, cv1, cv5, cv6, cv17, cv2] 7 (Tr.N (Tr.N Tr.E [cv58, cv0, cv1, cv5, cv20, cv17, cv2] 6 Tr.E) [cv58, cv0, cv1, cv5, cv17, cv14, cv2] 6 Tr.E)) [cv58, cv0, cv35, cv32, cv6, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [0xaa00aa00aa00aa00ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xaa00aa00aaaaaaaaaa00aa00aaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaa00aa00ff00ff00aa00aa00ff00ff00, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xaa00aa00ffffffffaa00aa00ffffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0xaa00ffffaa00ffffaa00ffffaa00ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E)))
def t105 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, cv4, cv60, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xaaaa000000000000aaaa000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xaaaa0000aaaa00000000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv41, cv1, cv6, cv2] 8 Tr.E)) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv22, cv6, cv2] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv4, cv0, cv1, cv15, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv4, cv0, cv1, cv5, cv22, cv6, cv2] 8 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa0000, cv4, cv0, cv1, cv67, cv6, cv2] 7 Tr.E)))
def u106 : Tr := Tr.N t104 [0xaa88aa88aa88aa88aa88aa88aa88aa88, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 t105
def u107 : Tr := Tr.N u103 [cv58, cv3, cv32, cv45, cv6, cv2] 5 u106
def u108 : Tr := Tr.N u100 [0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 u107
def t109 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaaa8888aaaa8888aaaa8888aaaa8888, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xaaaaa8a8aaaaa8a8aaaaa8a8aaaaa8a8, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv2] 7 Tr.E) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 Tr.E)) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, cv6, cv23, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaaaa00aaaaaa00] 7 (Tr.N Tr.E [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv67, cv6, cv2] 7 Tr.E)) [0xaaaaaa88aaaaaa88aaaaaa88aaaaaa88, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xaaaaaaa0aaaaaaa0aaaaaaa0aaaaaaa0, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaaaaaaa000000000000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t110 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv0, cv1, cv5, cv17, cv2] 8 Tr.E) [0xaaaaaaaa00000000aaaaaaaa00000000, cv4, cv0, cv1, cv5, cv6, cv17, cv2] 8 (Tr.N Tr.E [0xaaaaaaaa88888888aaaaaaaa88888888, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xaaaaaaaaa8a8a8a8aaaaaaaaa8a8a8a8, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xaaaaaaaaaaaa0000aaaaaaaaaaaa0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaa0a0aaaaaaaaaaaaa0a0, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaaaaaaaaaaaaa00aaaaaaaaaaaaaa00, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv19] 8 Tr.E) [0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 8 Tr.E)))
def u111 : Tr := Tr.N t109 [0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 t110
def t112 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaa8888888888888888, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xaaaaaaaaaaaaaaaaaa00aa00aa00aa00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaaaa88aa88aa88aa88, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xaaaaaaaaaaaaaaaaaaaaaa00aaaaaa00, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaaaaaaaaaaaaaaaaaaa00000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaaaaaaaaaaaaaaaaaaaaaaa88888888, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, 0xaaaaaaaaaaaaaaaaffffffffffffffff, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t113 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xaaaaffffaaaaffff0000ffff0000ffff, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [cv3, 0xaaaaffffaaaaffffaaaaffffaaaaffff, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, 0xaaffaaffaaffaaffaaffaaffaaffaaff, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, 0xaf0faf0faf0faf0faf0faf0faf0faf0f, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xafafafafafafafafafafafafafafafaf, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xb3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, 0xbb33bb33bb33bb33bb33bb33bb33bb33, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv40, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, cv6, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 7 Tr.E)))
def u114 : Tr := Tr.N t112 [cv3, 0xaaaaaaaaffffffffaaaaaaaaffffffff, cv4, cv0, cv1, cv5, cv6, cv2] 8 t113
def u115 : Tr := Tr.N u111 [0xaaaaaaaaaaaaaaaa0000000000000000, cv4, cv0, cv1, cv5, cv6, cv2, cv19] 8 u114
def t116 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv48, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xee00ee00ee00ee00ee00ee00ee00ee00, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv50, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xeeee0000eeee0000eeee0000eeee0000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaa, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xeeeecccceeeecccceeeecccceeeecccc, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv1, cv25, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv40, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv1, cv26, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv40, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv1, cv5, cv6, cv28, cv2] 8 Tr.E) [cv3, cv4, cv40, cv0, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E)))
def t117 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv1, cv5, cv6, cv39] 7 Tr.E) [cv3, cv4, cv40, cv0, cv1, cv5, cv43, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv40, cv1, cv5, cv24, cv6, cv2] 7 Tr.E)) [cv3, cv4, 0xf0000000f0000000f0000000f0000000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf000f00000000000f000f00000000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf000f000f000f0000000000000000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv30, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv1, cv30, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def u118 : Tr := Tr.N t116 [cv3, cv4, cv40, cv0, cv1, cv5, cv6, cv2] 9 t117
def t119 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, 0xf0f0f0f000000000f0f0f0f000000000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv25, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv5, cv6, cv2] 9 Tr.E)) [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f00000f0f00000] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv63, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv6, cv2, cv29] 8 Tr.E)) [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv6, cv39] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv1, cv5, cv63, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv1, cv5, cv6, cv2, cv31] 8 Tr.E) [cv3, cv4, 0xf0f00000f0f00000f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f00000f0f00000ffff0000ffff0000, cv0, cv1, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf0f00000f0f00000ffffffffffffffff, cv0, cv1, cv5, cv6] 7 Tr.E)))
def t120 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0e0e0f0f0e0e0f0f0e0e0f0f0e0e0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, 0xf0f0f000f0f0f000f0f0f000f0f0f000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f000f000f0f0f0f0f000f000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f0a0a0f0f0f0f0f0f0a0a0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f0f000f0f0f0f0f0f0f000, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f0f0f0f000f000f000f000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u121 : Tr := Tr.N t119 [cv3, cv4, 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0, cv0, cv1, cv5, cv6, cv2] 8 t120
def u122 : Tr := Tr.N u118 [cv3, cv4, 0xf0f0000000000000f0f0000000000000, cv0, cv1, cv5, cv6, cv2] 8 u121
def u123 : Tr := Tr.N u115 [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, cv2] 7 u122
def u124 : Tr := Tr.N u108 [0xaaaa0000aaaa0000ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6] 7 u123
def u125 : Tr := Tr.N u93 [0x37373737373737373737373737373737, cv3, cv0, cv1, cv5, cv6, cv2] 7 u124
def u126 : Tr := Tr.N u62 [cv9, cv3, cv4, 0xff000f00ff000f00ff000f00ff000f00, cv5, cv6, cv2] 7 u125
def t127 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xf0f0f0f0f0f0f0f0ffffffffffffffff, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xf0f0f0f0fffffffff0f0f0f0ffffffff, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, 0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfa00fa00fa00fa00fa00fa00fa00fa00, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfaaafaaafaaafaaafaaafaaafaaafaaa, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv54, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfafa0000fafa0000fafa0000fafa0000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfafaaaaafafaaaaafafaaaaafafaaaaa, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xfafafafa00000000fafafafa00000000, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfafafafaaaaaaaaafafafafaaaaaaaaa, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfafafafaf0f0f0f0fafafafaf0f0f0f0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def t128 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfafafafafafafafaaaaaaaaaaaaaaaaa, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfafafafafafafafaf0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv60, cv1, cv5, cv27, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv60, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv60, cv1, cv5, cv6, cv2, cv29] 8 Tr.E) [cv3, cv4, cv0, cv60, cv1, cv5, cv6, cv39] 7 Tr.E)) [cv3, cv4, cv0, cv60, cv1, cv6, cv44, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfe00fe00fe00fe00fe00fe00fe00fe00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfefe0000fefe0000fefe0000fefe0000, cv1, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfefefefefefefefefefefefefefefefe, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00000000000000ff00000000000000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff000000ff0000000000000000000000, cv1, cv5, cv6, cv2] 8 Tr.E)))
def u129 : Tr := Tr.N t127 [cv3, cv4, cv0, 0xfafafafafafafafa0000000000000000, cv1, cv5, cv6, cv2] 8 t128
def t130 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv1, cv25, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv41, cv1, cv5, cv6, cv2] 9 (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv1, cv5, cv6, cv69] 8 Tr.E)) [cv3, cv4, cv0, cv41, cv1, cv5, cv43, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv1, cv16, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv41, cv1, cv63, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv41, cv1, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv1, cv27, cv2] 7 Tr.E) [cv3, cv4, cv0, cv41, cv1, cv6, cv2, cv29] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv1, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E)) [cv3, cv4, cv0, cv41, cv1, cv6, cv39] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv18, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv41, cv30, cv5, cv6, cv2] 8 Tr.E)))
def t131 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv41, cv5, cv6, cv2, cv49] 8 Tr.E) [cv3, cv4, cv0, cv41, cv5, cv6, cv73] 7 (Tr.N Tr.E [cv3, cv4, cv0, 0xff000000ff000000ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xff000000ff000000ffff0000ffff0000, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff000000ff000000ffffffffffffffff, cv1, cv5, cv6] 7 Tr.E) [cv3, cv4, cv0, 0xff000000ffffffffff000000ffffffff, cv1, cv5, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xff000f00ff000f00ff000f00ff000f00, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff003300ff003300ff003300ff003300, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff00aa00ff000000ff00aa00ff000000, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv62, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv62, cv25, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv62, cv5, cv22, cv6, cv2] 8 Tr.E)))
def u132 : Tr := Tr.N t130 [cv3, cv4, cv0, cv41, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 t131
def u133 : Tr := Tr.N u129 [cv3, cv4, cv0, cv41, 0xff00ff0000000000ff00ff0000000000, cv5, cv6, cv2] 8 u132
def t134 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv62, cv5, cv6, 0xffffffffffffffffff00aa00ff00aa00] 7 Tr.E) [cv3, cv4, cv0, cv62, cv5, 0xffffffffff00aa00ffffffffff00aa00, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv62, cv67, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv62, cv27, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv62, cv6, cv2, cv29] 7 Tr.E) [cv3, cv4, cv0, cv62, cv6, cv39] 6 Tr.E)) [cv3, cv4, cv0, 0xff00cc00ff00cc00ff00cc00ff00cc00, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ee00ff00ee00ff00ee00ff00ee00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff00f000ff00f000ff00f000ff00f000, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, 0xff00fa00ff00fa00ff00fa00ff00fa00, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv25, cv5, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv28, cv2] 8 Tr.E)))
def t135 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv5, cv6, cv28, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv5, cv43, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00aa00aa00ff00ff00aa00aa00, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xff00ff00cc00cc00ff00ff00cc00cc00, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00f000f000ff00ff00f000f000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, 0xffffffffffff00000000000000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv43, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00aa00ff00ff00ff00aa00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00cc00ff00ff00ff00cc00, cv5, cv6, cv2] 7 Tr.E)))
def u136 : Tr := Tr.N t134 [cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv5, cv38, cv2] 7 t135
def t137 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6, cv31] 8 (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6, cv49] 8 Tr.E)) [cv3, cv4, cv0, 0xff00ff00ff00ff000f000f000f000f00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff00aa00aa00aa00aa00, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ff00cc00cc00cc00cc00, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xff00ff00ff00ff00ee00ee00ee00ee00, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff00f000f000f000f000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ff00ff000000ff000000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ff00ff00aa00ff00aa00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff00ff00ff0000000000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ff00ff00ff00cc00cc00, cv5, cv6, cv2] 7 Tr.E)))
def t138 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, cv4, cv0, cv1, 0xff00ff00ff00ff00ffffffffffffffff, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xff00ff00ffffffffff00ff00ffffffff, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xff00ffffff00ffffff00ffffff00ffff, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xff0f0000ff0f0000ff0f0000ff0f0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xff0fff0fff0fff0fff0fff0fff0fff0f, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xff330000ff330000ff330000ff330000, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xff33ff33ff33ff33ff33ff33ff33ff33, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xff55ff55ff55ff55ff55ff55ff55ff55, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv70, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv78, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffaa0000ff000000ffaa0000ff000000, cv6, cv2] 7 Tr.E)))
def u139 : Tr := Tr.N t137 [cv3, cv4, cv0, 0xff00ff00ff00ff00ff00ff00ff000000, cv5, cv6, cv2] 7 t138
def u140 : Tr := Tr.N u136 [cv3, cv4, cv0, 0xff00ff00ff00f000ff00ff00ff00f000, cv5, cv6, cv2] 7 u139
def u141 : Tr := Tr.N u133 [cv3, cv4, cv0, cv62, cv5, cv6, cv2] 8 u140
def t142 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6, 0xffffffffffffffffffaa0000ffaa0000] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv15, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffaaff00ffaaff00ffaaff00ffaaff00, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffaaffaa00000000ffaaffaa00000000, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffaaffaaff00ff00ffaaffaaff00ff00, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaaaaaaaaaaaaaaaaa, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaff00ff00ff00ff00, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv23, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 9 Tr.E) [cv3, cv4, cv0, cv1, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 8 Tr.E)))
def t143 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv36, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffccff00ffccff00ffccff00ffccff00, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffccffcc00000000ffccffcc00000000, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffccffccaa88aa88ffccffccaa88aa88, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffccffccccccccccffccffcccccccccc, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv71, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv18, cv5, cv6, cv17, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv18, cv5, cv6, cv64, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv18, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv18, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv18, cv5, cv74, cv2] 7 Tr.E)))
def u144 : Tr := Tr.N t142 [cv3, cv4, cv0, cv1, 0xffcc0000ffcc0000ffcc0000ffcc0000, cv5, cv6, cv2] 8 t143
def t145 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffee0000ffee0000ffee0000ffee0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffeeffeeffeeffeeffeeffeeffeeffee, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xfff00000fff00000fff00000fff00000, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv56, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xfff0ff00fff0ff00fff0ff00fff0ff00, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xfff0fff000000000fff0fff000000000, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xfff0fff0f0f0f0f0fff0fff0f0f0f0f0, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xfff0fff0fff0fff0ff00ff00ff00ff00, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv30, cv5, cv6, cv23, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv30, cv5, cv6, cv2] 9 Tr.E) [cv3, cv4, cv0, cv1, 0xfffa0000fffa0000fffa0000fffa0000, cv6, cv2] 7 Tr.E)))
def t146 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xfffcfffcfffcfffcfffcfffcfffcfffc, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv25, cv5, cv6, cv2] 9 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv25, cv5, cv6, cv39] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv25, cv5, cv17, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv25, cv5, cv23, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv25, cv5, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv25, cv5, 0xffffffffffff0000ffffffffffff0000, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv25, cv22, cv23, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv25, cv16, cv17, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff000000000000ffffffffffffffff, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff000033330000ffff000033330000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff000055550000ffff000055550000, cv6, cv2] 7 Tr.E)))
def u147 : Tr := Tr.N t145 [cv3, cv4, cv0, cv1, 0xfffafffafffafffafffafffafffafffa, cv5, cv6, cv2] 8 t146
def u148 : Tr := Tr.N u144 [cv3, cv4, cv0, cv1, cv18, cv5, cv75, cv2] 7 u147
def t149 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000cccc0000ffff0000cccc0000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000f0000000ffff0000f0000000, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff000000000000, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv64, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, 0xffffffffffffffffffff0000f0f00000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000fafa0000ffff0000fafa0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000fcfc0000ffff0000fcfc0000, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ff000000ffff000000000000, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv26, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv26, cv6, cv28, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv26, cv6, cv2] 8 Tr.E)))
def t150 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv26, cv23, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv26, cv43, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffaa0000ffff0000ffaa0000, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000ffcc0000ffff0000ffcc0000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000fff00000ffff0000fff00000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ff000000ff000000, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffaa0000ffaa0000, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv39] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff0000aaaa0000, cv6, cv2] 7 Tr.E)))
def u151 : Tr := Tr.N t149 [cv3, cv4, cv0, cv1, cv26, cv6, 0xffffffffffffffffffff0000ff000000] 7 t150
def t152 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff0000f0f00000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff0000ff000000, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv5, cv6, cv2] 9 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffff0000ffff0000ffffffffffffffff, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffff0000ffffffffffff0000ffffffff, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffff00ffffff00ffffff00ffffff00ff, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffff0f0fffff0f0fffff0f0fffff0f0f, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffff3333ffff3333ffff3333ffff3333, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffff5555ffff5555ffff5555ffff5555, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv76, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv67, cv6, cv2] 8 Tr.E)))
def t153 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffaaaaffff0000ffffaaaaffff0000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv22, cv6, cv23, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv22, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv22, cv6, cv79] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv77, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffcc00ffffcc00ffffcc00ffffcc00, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffccccaaaa8888ffffccccaaaa8888, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv20, cv17, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffccccffff0000ffffccccffff0000, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv16, cv6, cv17, cv2] 8 Tr.E)))
def u154 : Tr := Tr.N t152 [cv3, cv4, cv0, cv1, cv5, cv21, cv6, cv2] 8 t153
def u155 : Tr := Tr.N u151 [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff0000cccc0000, cv6, cv2] 7 u154
def u156 : Tr := Tr.N u148 [cv3, cv4, cv0, cv1, 0xffff0000aaaa0000ffff0000aaaa0000, cv5, cv6, cv2] 8 u155
def u157 : Tr := Tr.N u141 [cv3, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv6, cv2] 8 u156
def t158 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xfffff000fffff000fffff000fffff000, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv24, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xfffff0f0ffff0000fffff0f0ffff0000, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffff0f0fffff0f0ffff0000ffff0000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv63, cv6, cv2] 9 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xfffffafafffffafafffffafafffffafa, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffffcfcfffffcfcfffffcfcfffffcfc, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv38, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffff00ffff0000ffffff00ffff0000, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ff00ff00ff00ff00, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ffff0000ffff0000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 9 Tr.E)))
def t159 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffccffffffccffffffccffffffcc, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xfffffff0fffffff0fffffff0fffffff0, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv27, cv19] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv27, cv31] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv27, 0xfffffffffffffffffafafafafafafafa] 6 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv27, cv39] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv43, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv68, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv28, cv2] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffaaffaaffffffffffaaffaa, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffccffccffffffffffccffcc, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffeeffeeffffffffffeeffee, cv2] 7 Tr.E)))
def u160 : Tr := Tr.N t158 [cv3, cv4, cv0, cv1, cv5, 0xffffffaaffffffaaffffffaaffffffaa, cv6, cv2] 8 t159
def t161 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffcfffcfffffffffffcfffc, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 9 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffaaaaffffffffffffaaaa, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffeeeeffffffffffffeeee, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffff0f0fffffffffffff0f0, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffff00ffffffffffffff00, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2] 10 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv49] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffaaffaaffaaffaa] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffffff0fff0fff0fff0] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffff00ffffff00] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffffffffff] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff000000000000ffff] 7 Tr.E)))
def t162 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff00000000aaaaaaaa] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff00000000f0f0f0f0] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff00000000ff00ff00] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff00f000f000f000f0] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff3333000033330000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff8080808080808080] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff8800880088008800] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff8888000088880000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff8888888800000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv72] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa000a000a000a000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a00000a0a00000] 7 Tr.E)))
def u163 : Tr := Tr.N t161 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffff0000000033333333] 7 t162
def u164 : Tr := Tr.N u160 [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffff0fff0fffffffffff0fff0, cv2] 8 u163
def t165 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaa000000aa000000] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaa00aa0000000000] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv73] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaa88aa88aa88aa88] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaa0aaa0aaa0aaa0] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaa000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaa8888aaaa8888] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaaa0a0aaaaa0a0] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaaaa00aaaaaa00] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv19, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E)))
def t166 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv19, cv49] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv19, cv29] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv19, 0xffffffffffffffffffffccccffffcccc] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv19, 0xfffffffffffffffffffff0f0fffff0f0] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffc000c000c000c000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffc0c00000c0c00000] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffc0c0c0c000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv79] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffcc000000cc000000] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffcccc000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffcccccccccccccccc, cv31] 8 Tr.E)))
def u167 : Tr := Tr.N t165 [cv3, cv4, cv0, cv1, cv5, cv6, cv19, cv31] 8 t166
def t168 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0000000f0000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f0000000000000] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f00000f0f00000] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f0a0a0f0f0a0a0] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f0c0c0f0f0c0c0] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv31, cv29] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv31, 0xffffffffffffffffffffaaaaffffaaaa] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffffafa0000fafa0000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffffafafafafafafafa, cv29] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffff00000000000000] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv69] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffff00aa00ff00aa00] 7 Tr.E)))
def t169 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffffaa0000ffaa0000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffffff00000fff00000] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv39] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffffff0000aaaa0000] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffffff0000f0f00000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffffff0000ff000000] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv29, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffffff0000ffff, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffffff33333333, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffffffaaaaaaaa, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000fffffffff0f0f0f0, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffffffff00ff00, cv2] 7 Tr.E)))
def u170 : Tr := Tr.N t168 [cv3, cv4, cv0, cv1, cv5, cv6, cv49, cv29] 8 t169
def u171 : Tr := Tr.N u167 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 7 u170
def u172 : Tr := Tr.N u164 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a000000000] 7 u171
def t173 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000f0fffffffff00000f0f, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff0000aaaaffffffff0000aaaa, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff0000ccccffffffff0000cccc, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffff0f000f00ffffffff0f000f00, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff80808080ffffffff80808080, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff88008800ffffffff88008800, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffff88880000ffffffff88880000, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff00000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2, cv49] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv72] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffa000a000ffffffffa000a000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffa0a00000ffffffffa0a00000, cv2] 7 Tr.E)))
def t174 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv74, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv74, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffffaa000000ffffffffaa000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffff00000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv73] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffaa88aa88ffffffffaa88aa88, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffaaa0aaa0ffffffffaaa0aaa0, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv17, cv23, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv17, cv64, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv17, cv28, cv2] 8 Tr.E)))
def u175 : Tr := Tr.N t173 [cv3, cv4, cv0, cv1, cv5, 0xffffffffa0a0a0a0ffffffff00000000, cv2] 7 t174
def t176 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffc000c000ffffffffc000c000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffc0c00000ffffffffc0c00000, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffc0c0c0c0ffffffff00000000, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv75, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv75, cv79] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffffcc000000ffffffffcc000000, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffcc00cc00ffffffff00000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffcc88cc88ffffffffcc88cc88, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffccc0ccc0ffffffffccc0ccc0, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffcccc0000ffffffff00000000, cv2] 7 Tr.E)))
def t177 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv66, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv66, cv29] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffccccccccffffffff88888888, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffffccccccccffffffffc0c0c0c0, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffccccccccffffffffcc00cc00, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv23, cv64, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv23, cv28, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv23, 0xffffffffffaaffaaffffffffffaaffaa, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv23, 0xfffffffffff0fff0fffffffffff0fff0, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv23, cv2, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv23, cv39] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, cv2] 7 Tr.E)))
def u178 : Tr := Tr.N t176 [cv3, cv4, cv0, cv1, cv5, 0xffffffffccccccccffff000000000000] 6 t177
def u179 : Tr := Tr.N u175 [cv3, cv4, cv0, cv1, cv5, cv17, 0xffffffffffccffccffffffffffccffcc, cv2] 7 u178
def t180 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv28, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xfffffffff0000000fffffffff0000000, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffffff000000ffffffff00000000, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv43, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv43, cv69] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffffff00aa00ffffffffff00aa00, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffffff00cc00ffffffffff00cc00, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv28, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv72] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv76, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv76, cv74, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv67, cv6, cv73] 7 Tr.E)))
def t181 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv19] 7 Tr.E) [cv3, cv4, cv0, cv1, cv22, cv27, cv31] 6 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv22, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv22, cv6, cv31, cv29] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv22, cv6, cv39] 7 Tr.E) [cv3, cv4, cv0, cv1, cv22, cv23, cv39] 6 Tr.E)) [cv3, cv4, cv0, cv1, cv77, cv6, cv79] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv16, cv6, cv19, cv29] 7 Tr.E) [cv3, cv4, cv0, cv1, cv16, cv6, cv69] 7 Tr.E) [cv3, cv4, cv0, cv1, cv16, cv6, cv39] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv6, cv39] 6 Tr.E) [cv3, cv4, cv0, cv1, cv6, cv44, cv19] 7 Tr.E)))
def u182 : Tr := Tr.N t180 [cv3, cv4, cv0, cv1, cv67, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 t181
def t183 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv6, cv44, 0xfffffffffffffffffafafafafafafafa] 6 Tr.E) [cv3, cv4, cv0, cv1, cv6, cv44, cv49] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv6, cv44, 0xffffffffffffffffffffffff00000000] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv6, 0xffffffffffff0000ffffffffffff0000, cv39] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv66, 0xffffffffffffccccffff0000ffff0000] 6 Tr.E) [cv3, cv4, cv0, cv1, 0xffffffffff000000ffff0000ff000000, cv2] 6 Tr.E)) [cv3, cv4, cv0, cv1, cv43, cv2, cv29] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv43, 0xffffffffffffffffffff0000ff000000] 6 Tr.E) [cv3, cv4, cv0, cv1, 0xffffffffffccccccffff0000ff000000] 5 Tr.E) [cv3, cv4, cv0, cv70, cv5, cv6, cv72] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv78, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E) [cv3, cv4, cv0, cv71, cv5, cv6, cv29] 7 Tr.E)))
def t184 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv18, cv5, cv6, cv69] 7 Tr.E) [cv3, cv4, cv0, cv5, cv38, cv6, cv39] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv5, 0xffffffffff00aa00ffffffffff00aa00, 0xffffffffffffffffff00aa00ff00aa00] 6 Tr.E)) [cv3, cv4, 0xf0f0f0f0f0f0fffff0f0f0f0f0f0ffff, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0fff0fff0f0f0f0f0fff0fff0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf8f0f8f0f8f0f8f0f8f0f8f0f8f0f8f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf8f8f0f0f8f8f0f0f8f8f0f0f8f8f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv72] 7 Tr.E) [cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E)))
def u185 : Tr := Tr.N t183 [cv3, cv4, cv0, cv71, cv6, cv44] 6 t184
def u186 : Tr := Tr.N u182 [cv3, cv4, cv0, cv1, cv6, cv44, cv31] 7 u185
def u187 : Tr := Tr.N u179 [cv3, cv4, cv0, cv1, cv5, 0xffffffffee00ee00ffffffffee00ee00, cv2] 7 u186
def u188 : Tr := Tr.N u172 [cv3, cv4, cv0, cv1, cv5, 0xffffffff000000ffffffffff000000ff, cv2] 7 u187
def u189 : Tr := Tr.N u157 [cv3, cv4, cv0, cv1, cv5, cv16, cv6, cv2] 9 u188
def t190 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xfaf0faf0f0f0f0f0faf0faf0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xfaf0faf0faf0faf0f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv54, cv41, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv54, cv1, cv5, cv6, cv23, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv54, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv54, cv1, cv5, cv6, cv73] 7 Tr.E)) [cv3, cv4, cv54, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv54, cv1, cv67, cv6, cv2] 7 Tr.E) [cv3, cv4, cv54, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv54, cv26, cv6, cv2] 6 Tr.E)) [cv3, cv4, cv54, cv26, cv23, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv4, cv54, cv5, cv6, cv28, cv2] 7 Tr.E) [cv3, cv4, cv54, cv5, cv23, cv28, cv2] 6 Tr.E)))
def t191 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xfaf8faf8faf8faf8faf8faf8faf8faf8, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xfafaf0f0f0f0f0f0fafaf0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, 0xfafafafaf0f0f0f0f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv60, cv61, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv60, cv1, cv30, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv60, cv78, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv41, cv1, cv56, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv41, cv1, cv24, cv6, cv2] 7 Tr.E) [cv3, cv4, cv41, cv1, cv24, cv23, cv2] 6 Tr.E) [cv3, cv4, cv41, cv18, cv24, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv62, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xff00ff00ff00ff000000000000000000, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 8 Tr.E)))
def u192 : Tr := Tr.N t190 [cv3, cv4, cv54, cv5, cv43, cv2] 6 t191
def t193 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, 0xff0fff0fff0fff0f0f0f0f0f0f0f0f0f, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, cv18, cv5, cv24, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv1, cv18, cv5, cv6, cv57, cv2] 7 Tr.E)) [cv3, cv4, cv1, 0xfff0f0f0f0f0f0f0fff0f0f0f0f0f0f0, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, 0xfff0f0f0fff0f0f0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, cv56, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv1, cv56, cv5, cv6, cv69] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv56, cv5, cv43, cv2] 7 Tr.E) [cv3, cv4, cv1, cv56, cv16, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv1, cv56, cv16, cv6, cv69] 6 Tr.E)) [cv3, cv4, cv1, cv56, cv16, cv43, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 8 Tr.E)))
def t194 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, 0xfff0fff0fff0fff0fff0f0f0fff0f0f0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, cv30, cv5, cv63, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv1, cv30, cv5, cv6, cv2, cv31] 8 Tr.E)) [cv3, cv4, cv1, cv30, cv5, cv6, cv79] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv30, cv77, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, cv25, cv5, cv24, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv24, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv26, cv45, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, cv26, cv45, cv23, cv2] 6 Tr.E) [cv3, cv4, cv1, cv5, 0xffff0f0f0f0f0f0fffff0f0f0f0f0f0f, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv24, cv6, cv2] 8 Tr.E) [cv3, cv4, cv1, cv5, cv24, cv6, cv39] 7 Tr.E)))
def u195 : Tr := Tr.N t193 [cv3, cv4, cv1, 0xfff0fff0fff0fff0faf0faf0faf0faf0, cv5, cv6, cv2] 7 t194
def u196 : Tr := Tr.N u192 [cv3, cv4, cv1, 0xff0f0f0fff0f0f0fff0f0f0fff0f0f0f, cv5, cv6, cv2] 7 u195
def t197 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv24, cv17, cv39] 6 Tr.E) [cv3, cv4, cv1, cv5, cv24, cv23, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv24, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv2] 6 Tr.E)) [cv3, cv4, cv1, cv5, cv45, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv63, cv6, cv64, cv2] 8 Tr.E) [cv3, cv4, cv1, cv5, cv27, cv46, cv19] 6 Tr.E)) [cv3, cv4, cv1, cv5, cv6, cv57, cv19] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv6, cv46, cv19] 6 Tr.E) [cv3, cv4, cv1, cv5, cv33, cv46, cv2] 6 (Tr.N Tr.E [cv3, cv4, cv1, cv5, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 6 Tr.E)) [cv3, cv4, cv1, cv22, cv24, cv6, cv39] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv22, cv24, cv23, cv2] 6 Tr.E) [cv3, cv4, cv1, cv16, cv24, cv17, cv2] 6 Tr.E)))
def t198 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv6, cv57, cv44, cv19] 6 Tr.E) [cv3, cv4, cv1, cv6, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0, 0xffffffffffffccccffff0000ffff0000] 6 (Tr.N Tr.E [cv3, cv4, cv78, cv5, cv6, cv79] 6 Tr.E)) [cv3, cv4, cv18, cv56, cv5, cv6, cv69] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xffe0ffe0ffe0ffe0ffe0ffe0ffe0ffe0, cv5, cv6, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 6 Tr.E) [cv3, 0xccccccccccccccccccccccccffffffff, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, 0xccccccccccccccccffffccccffffcccc, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xcfcccfcccfcccfcccfcccfcccfcccfcc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv47, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xeccceccceccceccceccceccceccceccc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xececccccececccccececccccececcccc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def u199 : Tr := Tr.N t197 [cv3, cv4, cv1, 0xffffe0e0ffffe0e0ffffe0e0ffffe0e0, 0xffffffffe0e0e0e0ffffffffe0e0e0e0, cv2] 6 t198
def t200 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xececececececececcccccccccccccccc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv47, cv0, cv1, cv26, cv6, cv2] 6 (Tr.N Tr.E [cv3, cv47, cv0, cv1, cv5, cv6, cv28, cv2] 7 Tr.E)) [cv3, cv47, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv47, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E) [cv3, cv47, cv0, cv1, cv5, cv74, cv2] 7 Tr.E)) [cv3, cv47, cv0, cv1, cv76, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv47, cv0, cv78, cv5, cv6, cv2] 7 Tr.E) [cv3, cv47, cv60, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv47, cv1, cv5, cv6, cv2, cv31] 7 (Tr.N (Tr.N Tr.E [cv3, cv47, cv1, cv5, cv6, cv79] 6 Tr.E) [cv3, cv47, cv1, cv5, cv6, 0xffffffffffffffffe0e0e0e0e0e0e0e0] 6 Tr.E)))
def t201 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xeecceecccccccccceecceecccccccccc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xeecceecceecceecccccccccccccccccc, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv50, cv0, cv41, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv50, cv0, cv1, cv5, cv6, cv17, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv50, cv0, cv1, cv5, cv6, cv64, cv2] 7 Tr.E) [cv3, cv50, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv50, cv0, cv1, cv5, cv6, cv73] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv50, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 Tr.E) [cv3, cv50, cv0, cv1, cv67, cv6, cv2] 7 Tr.E) [cv3, cv50, cv0, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv50, cv0, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 6 Tr.E) [cv3, cv50, cv0, cv26, cv6, cv2] 6 Tr.E)))
def u202 : Tr := Tr.N t200 [cv3, 0xeecccccceecccccceecccccceecccccc, cv0, cv1, cv5, cv6, cv2] 7 t201
def u203 : Tr := Tr.N u199 [cv3, 0xececececccccccccececececcccccccc, cv0, cv1, cv5, cv6, cv2] 7 u202
def u204 : Tr := Tr.N u196 [cv3, cv4, cv1, cv5, cv24, cv17, cv2] 7 u203
def t205 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv50, cv0, cv5, cv6, 0xffffffffffaaffaaffffffffffaaffaa, cv2] 6 Tr.E) [cv3, cv50, cv0, cv5, cv17, cv28, cv2] 6 (Tr.N Tr.E [cv3, cv50, cv0, cv5, cv43, cv2] 6 Tr.E)) [cv3, cv50, cv54, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv50, cv54, cv26, cv6, cv2] 5 Tr.E) [cv3, cv50, cv54, cv5, cv6, cv28, cv2] 6 Tr.E)) [cv3, cv50, cv26, cv45, cv6, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xeeeceeeceeeceeeceeeceeeceeeceeec, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xeeeceeeceeeceeeceeeceeeceeeceeec, cv0, cv26, cv6, cv2] 5 (Tr.N Tr.E [cv3, 0xeeeceeeceeeceeeceeeceeeceeeceeec, cv0, cv5, cv6, cv28, cv2] 6 Tr.E)) [cv3, 0xeeeecccccccccccceeeecccccccccccc, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xeeeecccccccccccceeeecccccccccccc, cv0, cv1, cv5, cv17, cv2] 6 Tr.E) [cv3, 0xeeeeeeeecccccccccccccccccccccccc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def t206 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv40, cv0, cv1, cv18, cv5, cv6, cv2] 8 Tr.E) [cv3, cv40, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, 0xffffffff88888888ffffffff88888888, cv2] 6 (Tr.N Tr.E [cv3, cv40, cv0, cv70, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv40, cv0, cv70, cv5, 0xffffffff88888888ffffffff88888888, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv40, cv0, cv18, cv26, cv6, cv2] 6 Tr.E) [cv3, cv40, cv0, cv18, cv5, cv6, cv28, cv2] 7 Tr.E)) [cv3, cv40, cv0, cv18, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv40, cv0, cv18, cv5, cv43, cv2] 6 Tr.E) [cv3, cv40, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv0, 0xfcccccccfcccccccfcccccccfccccccc, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, 0xfcfcccccccccccccfcfccccccccccccc, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv0, 0xfcfcfcfccccccccccccccccccccccccc, cv1, cv5, cv6, cv2] 7 Tr.E)))
def u207 : Tr := Tr.N t205 [cv3, cv40, cv0, cv61, cv1, cv5, cv6, cv2] 8 t206
def t208 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv41, cv1, cv20, cv6, cv2] 7 Tr.E) [cv3, cv0, cv62, 0xffcceeccffcceeccffcceeccffcceecc, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv0, cv1, 0xff333333ff333333ff333333ff333333, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv14, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, 0xffccccccccccccccffcccccccccccccc, cv5, cv6, cv2] 7 Tr.E) [cv3, cv0, cv1, 0xffccccccffcccccccccccccccccccccc, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv0, cv1, cv36, cv25, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv36, cv5, cv6, cv17, cv2] 7 Tr.E) [cv3, cv0, cv1, cv36, cv5, cv6, cv2] 8 Tr.E) [cv3, cv0, cv1, cv36, cv5, cv6, cv2, cv19] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv36, cv5, cv6, cv69] 7 Tr.E) [cv3, cv0, cv1, cv36, cv5, cv43, cv2] 7 Tr.E)))
def t209 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv36, cv63, cv6, cv69] 6 Tr.E) [cv3, cv0, cv1, cv36, cv63, cv43, cv2] 6 (Tr.N Tr.E [cv3, cv0, cv1, cv36, cv6, cv2, cv29] 7 Tr.E)) [cv3, cv0, cv1, cv36, cv6, cv19, cv29] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv36, cv6, cv39] 6 Tr.E) [cv3, cv0, cv1, 0xffcceeccffcceeccffcceeccffcceecc, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv0, cv1, 0xffccffcccccccccccccccccccccccccc, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv18, cv5, cv16, cv6, cv2] 8 Tr.E) [cv3, cv0, cv1, cv18, cv5, cv75, cv79] 6 Tr.E) [cv3, cv0, cv1, cv18, cv77, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv18, cv77, cv6, cv79] 6 Tr.E) [cv3, cv0, cv1, cv18, cv77, cv75, cv2] 6 Tr.E)))
def u210 : Tr := Tr.N t208 [cv3, cv0, cv1, cv36, cv63, cv6, cv2] 7 t209
def u211 : Tr := Tr.N u207 [cv3, cv0, cv41, cv1, cv36, cv5, cv6, cv2] 8 u210
def t212 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv25, cv5, cv20, cv6, cv2] 8 Tr.E) [cv3, cv0, cv1, cv25, cv5, cv20, cv17, cv2] 7 (Tr.N Tr.E [cv3, cv0, cv1, cv25, cv5, cv14, cv2] 7 Tr.E)) [cv3, cv0, cv1, cv25, cv5, cv14, cv19] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv25, cv22, cv20, cv6, cv2] 7 Tr.E) [cv3, cv0, cv1, cv25, cv22, cv14, cv2] 6 Tr.E)) [cv3, cv0, cv1, cv26, cv32, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv26, cv14, cv2] 6 Tr.E) [cv3, cv0, cv1, cv26, cv14, cv19] 5 (Tr.N Tr.E [cv3, cv0, cv1, cv26, cv14, cv31] 5 Tr.E)) [cv3, cv0, cv1, cv5, 0xffff333333333333ffff333333333333, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv21, cv20, cv6, cv2] 7 Tr.E) [cv3, cv0, cv1, cv5, cv22, cv6, cv14, cv2] 7 Tr.E)))
def t213 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv20, cv6, cv17, cv2] 7 Tr.E) [cv3, cv0, cv1, cv5, cv20, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv20, cv6, cv2, cv19] 7 Tr.E)) [cv3, cv0, cv1, cv5, cv20, cv6, cv39] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv20, cv17, cv2] 7 Tr.E) [cv3, cv0, cv1, cv5, cv20, cv17, cv39] 6 Tr.E)) [cv3, cv0, cv1, cv5, cv32, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv32, cv17, cv2] 6 Tr.E) [cv3, cv0, cv1, cv5, cv16, cv6, cv23, cv2] 8 Tr.E) [cv3, cv0, cv1, cv5, cv16, cv17, cv23, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv16, cv66, cv2] 7 Tr.E) [cv3, cv0, cv1, cv5, cv42, cv6, cv14, cv2] 8 Tr.E)))
def u214 : Tr := Tr.N t212 [cv3, cv0, cv1, cv5, 0xffffcccccccccccccccccccccccccccc, cv6, cv2] 7 t213
def t215 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv27, cv34, cv2] 7 Tr.E) [cv3, cv0, cv1, cv5, cv27, cv34, cv19] 6 (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv6, 0xffffffff333333333333333333333333, cv2] 7 Tr.E)) [cv3, cv0, cv1, cv5, cv6, cv65, cv14] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv6, cv14, cv2] 8 Tr.E) [cv3, cv0, cv1, cv5, cv6, cv14, cv19] 7 Tr.E)) [cv3, cv0, cv1, cv5, cv6, cv14, cv31] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv6, cv34, cv2] 7 Tr.E) [cv3, cv0, cv1, cv5, cv6, cv34, cv19] 6 Tr.E) [cv3, cv0, cv1, cv5, cv6, cv23, cv2, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv33, cv34, cv2] 6 Tr.E) [cv3, cv0, cv1, cv5, cv17, cv14, cv2] 7 Tr.E)))
def t216 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 6 Tr.E) [cv3, cv0, cv1, cv5, cv14, cv64, cv2] 7 (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv14, cv28, cv2] 7 Tr.E)) [cv3, cv0, cv1, cv5, cv14, cv28, cv19] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv14, cv28, cv31] 6 Tr.E) [cv3, cv0, cv1, cv5, cv14, 0xffffffffffaaffaaffffffffffaaffaa, cv2] 6 Tr.E)) [cv3, cv0, cv1, cv5, cv14, 0xfffffffffff0fff0fffffffffff0fff0, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv14, cv2, 0xffffffffffffffffffffffff00000000] 7 Tr.E) [cv3, cv0, cv1, cv5, cv34, cv39] 6 Tr.E) [cv3, cv0, cv1, cv5, cv34, 0xffffffffffffffffffffaaaaaaaaaaaa] 5 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv5, cv66, cv2, 0xffffffffffffffffcccccccccccccccc] 7 Tr.E) [cv3, cv0, cv1, cv35, cv32, cv6, cv2] 6 Tr.E)))
def u217 : Tr := Tr.N t215 [cv3, cv0, cv1, cv5, cv17, cv34, cv2] 6 t216
def u218 : Tr := Tr.N u214 [cv3, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv14, cv2] 7 u217
def u219 : Tr := Tr.N u211 [cv3, cv0, cv1, cv30, cv5, cv6, cv14, cv2] 7 u218
def u220 : Tr := Tr.N u204 [cv3, cv50, cv0, cv5, cv6, cv28, cv2] 7 u219
def t221 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv22, cv20, cv6, cv39] 6 Tr.E) [cv3, cv0, cv1, cv22, cv16, cv6, cv23, cv2] 7 (Tr.N Tr.E [cv3, cv0, cv1, cv22, cv16, cv66, cv2] 6 Tr.E)) [cv3, cv0, cv1, cv22, cv27, cv34, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv22, cv6, cv34, cv2] 6 Tr.E) [cv3, cv0, cv1, cv22, cv34, cv39] 5 Tr.E)) [cv3, cv0, cv1, 0xffffc8c8ffc8c8c8ffffc8c8ffc8c8c8, cv6, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv2] 6 Tr.E) [cv3, cv0, cv1, cv32, cv45, cv6, cv2] 6 (Tr.N Tr.E [cv3, cv0, cv1, cv32, cv6, 0xffffffffffffffffffff0000ff000000] 6 Tr.E)) [cv3, cv0, cv1, cv6, cv14, cv44, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv0, cv1, cv6, cv14, cv44, cv19] 6 Tr.E) [cv3, cv0, cv1, cv17, cv14, cv44, cv2] 6 Tr.E)))
def t222 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv70, cv77, cv75, cv2] 5 Tr.E) [cv3, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv5, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 5 (Tr.N Tr.E [cv3, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, cv6, cv2] 6 Tr.E)) [cv3, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv0, cv36, cv30, cv25, cv6, cv2] 6 Tr.E) [cv3, cv0, cv36, cv30, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv0, cv36, cv30, cv5, cv6, cv69] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv36, cv30, cv5, cv43, cv2] 6 Tr.E) [cv3, cv0, cv36, cv30, cv6, cv2, cv29] 6 Tr.E) [cv3, cv0, cv36, cv30, cv6, cv39] 5 (Tr.N (Tr.N Tr.E [cv3, cv0, cv36, cv5, cv6, cv2, cv49] 7 Tr.E) [cv3, cv0, cv36, cv5, cv6, cv2, 0xfffffffffffffffffff0fff0fff0fff0] 6 Tr.E)))
def u223 : Tr := Tr.N t221 [cv3, cv0, cv70, cv5, cv75, cv79] 5 t222
def t224 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv36, cv63, cv6, cv2, cv49] 6 Tr.E) [cv3, cv0, 0xffcceeccffcceeccffcceeccffcceecc, cv5, cv6, 0xffffffffffffffffff00aa00ff00aa00] 6 (Tr.N Tr.E [cv3, cv0, 0xffcceeccffcceeccffcceeccffcceecc, cv5, 0xffffffffff00aa00ffffffffff00aa00, cv2] 6 Tr.E)) [cv3, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv14, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv71, cv5, cv16, cv6, cv2] 7 Tr.E) [cv3, cv0, cv71, cv22, cv16, cv6, cv2] 6 Tr.E)) [cv3, cv0, cv71, cv16, cv63, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv18, 0xffffc0c0ffc0c0c0ffffc0c0ffc0c0c0, cv6, cv2] 5 Tr.E) [cv3, cv0, cv18, cv77, cv6, cv28, cv2] 6 (Tr.N Tr.E [cv3, cv0, cv18, cv77, cv6, cv2, cv49] 6 Tr.E)) [cv3, cv0, cv18, cv77, cv43, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv0, cv30, cv26, cv32, cv6, cv2] 6 Tr.E) [cv3, cv0, cv30, cv26, cv14, cv2] 5 Tr.E)))
def t225 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv30, cv32, cv6, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv3, cv0, cv5, cv20, cv38, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv0, cv5, cv20, cv38, cv17, cv2] 6 Tr.E)) [cv3, cv0, cv5, cv38, cv14, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv5, cv38, cv14, cv19] 5 Tr.E) [cv3, cv0, cv5, cv38, cv14, cv31] 5 Tr.E)) [cv3, cv0, cv5, cv6, cv14, cv68, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv5, cv6, cv14, cv68, cv19] 6 Tr.E) [cv3, cv0, cv5, cv6, cv14, cv68, cv31] 6 Tr.E) [cv3, cv0, cv5, cv17, cv14, cv68, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv0, cv5, cv14, cv64, cv68, cv2] 6 Tr.E) [cv3, cv0, cv5, cv14, 0xffffffffff00ff00ffccffccff00ff00, cv2] 6 Tr.E)))
def u226 : Tr := Tr.N t224 [cv3, cv0, cv30, cv5, cv14, cv28, cv2] 6 t225
def u227 : Tr := Tr.N u223 [cv3, cv0, cv36, cv5, cv6, cv19, cv49] 6 u226
def t228 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv0, cv5, cv34, 0xffffffffff00ff00ffffff00ff00ff00, cv19] 5 Tr.E) [cv3, cv0, cv5, cv34, 0xffffffffff00ff00ffffff00ff00ff00, cv31] 5 (Tr.N Tr.E [cv3, cv0, cv22, cv20, cv38, cv6, cv2] 6 Tr.E)) [cv3, cv0, cv22, cv38, cv14, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv0, cv22, cv34, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 5 Tr.E) [cv3, cv54, cv26, cv32, cv6, cv2] 5 Tr.E)) [cv3, cv54, cv32, cv6, 0xffffffffffffffffffff0000ff000000] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv55, cv71, cv5, cv16, cv6, cv2] 6 Tr.E) [cv3, cv41, cv1, cv36, cv24, cv6, cv2] 6 (Tr.N Tr.E [cv3, cv41, cv1, cv20, cv24, cv6, cv2] 6 Tr.E)) [cv3, cv41, cv1, cv24, cv14, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv41, cv1, cv34, cv46, cv2] 5 Tr.E) [cv3, cv62, cv20, cv24, cv6, cv2] 5 Tr.E)))
def t229 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv36, cv56, cv25, cv6, cv2] 6 Tr.E) [cv3, cv1, cv36, cv56, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv1, cv36, cv56, cv27, cv2] 5 Tr.E)) [cv3, cv1, cv36, cv56, cv6, cv2, cv29] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv36, cv56, cv6, cv39] 5 Tr.E) [cv3, cv1, cv36, cv24, cv6, cv2] 6 Tr.E)) [cv3, cv1, cv36, cv24, cv6, cv69] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv36, cv45, cv6, cv2] 5 Tr.E) [cv3, cv1, cv18, cv16, cv24, cv6, cv2] 6 Tr.E) [cv3, cv1, cv30, cv5, cv6, cv14, cv31] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv26, cv32, cv45, cv6, cv2] 6 Tr.E) [cv3, cv1, cv26, cv45, cv14, cv2] 5 Tr.E)))
def u230 : Tr := Tr.N t228 [cv3, cv62, cv34, cv46, cv2] 4 t229
def t231 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv26, cv14, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 4 Tr.E) [cv3, cv1, cv5, cv20, cv24, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv1, cv5, cv20, cv24, cv17, cv2] 6 Tr.E)) [cv3, cv1, cv5, cv24, cv14, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv5, cv24, cv14, cv19] 5 Tr.E) [cv3, cv1, cv5, cv6, cv14, cv57, cv2] 7 Tr.E)) [cv3, cv1, cv5, cv6, cv14, cv57, cv49] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv5, cv6, cv14, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 6 Tr.E) [cv3, cv1, cv5, cv14, cv57, cv28, cv2] 6 Tr.E) [cv3, cv1, cv5, cv14, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0, cv28] 5 (Tr.N (Tr.N Tr.E [cv3, cv1, cv5, cv34, cv46, cv2] 6 Tr.E) [cv3, cv1, cv5, cv34, cv46, cv19] 5 Tr.E)))
def t232 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv22, cv24, cv14, cv2] 5 Tr.E) [cv3, cv1, cv22, cv34, cv46, cv2] 5 (Tr.N Tr.E [cv3, cv1, cv32, cv45, cv42, cv2] 5 Tr.E)) [cv3, cv1, cv32, cv45, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv1, cv32, cv45, cv6, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv3, cv1, cv32, cv45, cv65] 4 Tr.E)) [cv3, cv1, cv32, cv45, cv23, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv1, cv32, cv45, cv43, cv2] 5 Tr.E) [cv3, cv1, cv32, cv45, 0xffffffffffcccccc0000000000000000] 4 Tr.E) [cv3, cv1, cv32, cv45, 0xffffffffffccccccffffffffffcccccc, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv1, cv45, 0xffffffffffccccccffffccccffcccccc, cv2] 4 Tr.E) [cv3, cv36, cv56, cv5, cv6, cv2, cv49] 6 Tr.E)))
def u233 : Tr := Tr.N t231 [cv3, cv1, cv22, cv20, cv24, cv6, cv2] 6 t232
def u234 : Tr := Tr.N u230 [cv3, cv1, cv26, cv14, cv57, cv2] 5 u233
def u235 : Tr := Tr.N u227 [cv3, cv0, cv5, cv34, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 6 u234
def t236 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv36, cv30, cv6, cv31, cv29] 5 Tr.E) [cv3, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv25, cv6, cv2] 5 (Tr.N Tr.E [cv3, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, cv6, cv2] 6 Tr.E)) [cv3, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv27, cv2] 4 (Tr.N (Tr.N Tr.E [cv3, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv6, cv2, cv29] 5 Tr.E) [cv3, 0xffcceeccffcceeccffcceeccffcceecc, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv6, cv39] 4 Tr.E)) [cv3, cv18, cv32, cv45, cv6, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv18, cv16, cv45, cv6, cv2] 5 Tr.E) [cv3, cv30, cv26, cv14, cv31] 4 (Tr.N Tr.E [cv3, cv30, cv5, cv14, cv28, cv31] 5 Tr.E)) [cv3, cv30, cv32, cv45, cv6, cv2] 5 (Tr.N (Tr.N Tr.E [cv3, cv32, cv45, cv38, cv6, cv2] 5 Tr.E) [cv3, cv32, cv45, 0xffffffccffccffccffffffccffccffcc, cv6, cv2] 5 Tr.E)))
def t237 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv32, 0xfffffaf0fff0faf0fffffaf0fff0faf0, cv6, cv2] 4 Tr.E) [cv3, 0xffffeeccffcceeccffffeeccffcceecc, cv45, cv6, cv2] 4 (Tr.N Tr.E [cv48, cv47, cv1, cv5, cv6, cv2] 6 Tr.E)) [cv48, cv0, cv61, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv48, cv0, cv1, cv18, cv5, cv6, cv2] 7 Tr.E) [cv48, cv0, cv1, cv18, cv5, cv75, cv2] 6 Tr.E)) [cv48, cv0, cv70, cv5, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv48, cv0, cv70, cv5, 0xffffffff88888888ffffffff88888888, cv2] 5 Tr.E) [cv48, cv0, cv70, cv5, cv75, cv2] 5 Tr.E) [cv48, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv5, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv48, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv5, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv2] 5 Tr.E) [cv48, cv0, cv18, cv26, cv6, cv2] 5 Tr.E)))
def u238 : Tr := Tr.N t236 [cv3, cv32, cv45, 0xfffffff0fff0fff0fffffff0fff0fff0, cv6, cv2] 5 t237
def t239 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv48, cv0, cv18, cv5, cv43, cv2] 5 Tr.E) [cv48, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 6 (Tr.N Tr.E [cv50, cv0, cv1, cv5, cv6, cv17, cv73] 6 Tr.E)) [cv50, cv0, cv1, cv67, cv6, cv17, cv2] 6 (Tr.N (Tr.N Tr.E [cv50, cv0, cv26, cv35, cv6, cv2] 5 Tr.E) [cv50, cv54, cv1, cv5, cv6, cv17, cv2] 6 Tr.E)) [cv50, cv35, cv45, cv6, cv2] 4 (Tr.N (Tr.N (Tr.N Tr.E [0xeeeceeeceeeceeeceeeceeeceeeceeec, cv60, cv1, cv5, cv6, cv2] 6 Tr.E) [0xeeeceeeceeeceeeceeeceeeceeeceeec, cv60, cv26, cv6, cv2] 4 Tr.E) [0xeeeceeeceeeceeeceeeceeeceeeceeec, cv60, cv5, cv6, cv28, cv2] 5 (Tr.N (Tr.N Tr.E [cv40, cv60, cv61, cv1, cv5, cv6, cv2] 7 Tr.E) [0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv21, cv20, cv6, cv2] 6 Tr.E)))
def t240 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv41, cv1, cv33, cv34, cv2] 5 Tr.E) [cv0, cv62, cv21, cv20, cv6, cv2] 5 (Tr.N Tr.E [cv0, cv62, cv35, cv32, cv6, cv2] 5 Tr.E)) [cv0, cv62, cv33, cv34, cv2] 4 (Tr.N (Tr.N Tr.E [cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv21, cv20, cv2] 6 Tr.E) [cv0, 0xff00ff00ff00aa00ff00aa00ff00aa00, cv33, cv34, cv2] 4 Tr.E)) [cv0, cv1, cv15, cv36, cv25, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv15, cv36, cv5, cv6, cv2] 7 Tr.E) [cv0, cv1, cv15, cv36, cv27, cv2] 5 Tr.E) [cv0, cv1, cv15, cv36, cv6, cv2, cv29] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv15, cv36, cv6, cv39] 5 Tr.E) [cv0, cv1, cv15, cv25, cv20, cv6, cv2] 6 Tr.E)))
def u241 : Tr := Tr.N t239 [cv0, cv41, cv1, cv21, cv20, cv6, cv2] 6 t240
def u242 : Tr := Tr.N u238 [cv48, cv0, cv18, cv5, cv6, cv28, cv2] 6 u241
def t243 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv15, cv20, cv6, cv39] 5 Tr.E) [cv0, cv1, cv15, cv16, cv6, cv23, cv2] 6 (Tr.N Tr.E [cv0, cv1, cv15, cv16, cv66, cv2] 5 Tr.E)) [cv0, cv1, cv15, cv27, cv34, cv2] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv15, cv34, cv39] 4 Tr.E) [cv0, cv1, cv36, cv25, cv21, cv6, cv2] 6 Tr.E)) [cv0, cv1, cv36, cv21, cv6, cv39] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv18, cv21, cv16, cv6, cv2] 6 Tr.E) [cv0, cv1, cv25, cv5, cv21, cv20, cv6, cv2] 7 (Tr.N Tr.E [cv0, cv1, cv25, cv5, cv14, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 5 Tr.E)) [cv0, cv1, cv26, cv35, cv32, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv26, cv14, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 4 Tr.E) [cv0, cv1, cv5, cv21, cv20, cv6, cv2] 7 Tr.E)))
def t244 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv21, cv20, cv17, cv2] 6 Tr.E) [cv0, cv1, cv5, cv21, cv20, cv23, cv2] 6 (Tr.N Tr.E [cv0, cv1, cv5, cv21, cv20, 0xffffffffffff0000ffffffffffff0000, cv2] 6 Tr.E)) [cv0, cv1, cv5, cv21, cv16, cv23, cv2] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv21, cv34, cv2] 5 Tr.E) [cv0, cv1, cv5, cv22, cv20, cv17, cv2] 6 Tr.E)) [cv0, cv1, cv5, cv20, cv37, cv39] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv20, cv33, cv2] 5 Tr.E) [cv0, cv1, cv5, cv20, cv17, cv73] 5 Tr.E) [cv0, cv1, cv5, cv6, cv37, cv14, cv49] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv6, cv14, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 6 Tr.E) [cv0, cv1, cv5, cv33, cv34, cv2] 6 Tr.E)))
def u245 : Tr := Tr.N t243 [cv0, cv1, cv5, cv21, cv20, cv6, cv39] 6 t244
def t246 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv33, cv34, cv31] 5 Tr.E) [cv0, cv1, cv5, cv33, cv34, cv39] 5 (Tr.N Tr.E [cv0, cv1, cv5, cv33, cv34, 0xffffffffffffffffffffaaaaaaaaaaaa] 5 Tr.E)) [cv0, cv1, cv5, cv17, cv14, cv73] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv17, cv34, cv19] 5 Tr.E) [cv0, cv1, cv5, cv14, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, cv28] 5 Tr.E)) [cv0, cv1, cv5, cv34, 0xffffffffeeeeeeeeffffaaaaaaaaaaaa] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv67, cv20, cv17, cv2] 5 Tr.E) [cv0, cv1, cv35, cv32, cv6, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv0, cv1, cv35, cv32, cv23, cv2] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv35, cv32, cv43, cv2] 5 Tr.E) [cv0, cv1, cv35, cv32, 0xffffffffffccccccffffffffffcccccc, cv2] 5 Tr.E)))
def t247 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv35, 0xffffffffffccccccffffccccffcccccc, cv2] 4 Tr.E) [cv0, cv1, cv22, cv16, cv17, cv23, cv2] 6 (Tr.N Tr.E [cv0, cv15, 0xffcceeccffcceeccffcceeccffcceecc, cv6, cv39] 4 Tr.E)) [cv54, cv35, cv32, cv6, cv2] 4 (Tr.N (Tr.N Tr.E [cv1, cv15, cv36, cv24, cv6, cv2] 5 Tr.E) [cv1, cv15, cv20, cv24, cv6, cv2] 5 Tr.E)) [cv1, cv15, cv24, cv14, cv2] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv1, cv15, cv34, cv46, cv2] 4 Tr.E) [cv1, cv36, cv21, cv24, cv6, cv2] 5 Tr.E) [cv1, cv5, cv21, cv20, cv24, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv1, cv5, cv33, cv34, cv46, cv2] 5 Tr.E) [cv1, cv5, cv33, cv34, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 4 Tr.E)))
def u248 : Tr := Tr.N t246 [cv0, cv1, cv35, cv16, cv23, cv2] 5 t247
def u249 : Tr := Tr.N u245 [cv0, cv1, cv5, cv33, cv34, cv19] 5 u248
def u250 : Tr := Tr.N u242 [cv0, cv1, cv15, cv20, cv6, cv2] 6 u249
def u251 : Tr := Tr.N u235 [cv3, cv36, cv30, cv5, cv6, cv2, cv31] 6 u250
def u252 : Tr := Tr.N u220 [cv3, cv0, cv1, cv22, cv20, cv6, cv2] 7 u251
def u253 : Tr := Tr.N u189 [cv3, cv4, 0xfaf0f0f0faf0f0f0faf0f0f0faf0f0f0, cv1, cv5, cv6, cv2] 7 u252
def tree : Tr := Tr.N u126 [cv3, cv4, cv0, cv0, cv1, cv5, cv6, cv2] 9 u253
def st255 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x0, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [0x0, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N Tr.E [0x0, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv7, cv12, cv8, cv3, cv4, cv0, cv6] 7 (Tr.N (Tr.N Tr.E [cv7, cv8, cv13, cv4, cv0, cv5, cv6] 7 Tr.E) [cv7, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)) [0xff00ff0000000000ff00ff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xff00ff00ff00ff00ff00ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0xffffff0000000000ffffff, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [cv10, cv12, cv8, cv3, cv4, cv0, cv2] 7 (Tr.N (Tr.N Tr.E [cv10, cv12, cv13, cv4, cv0, cv1, cv2] 7 Tr.E) [cv10, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E)))
def st256 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv10, cv8, cv11, cv3, cv0, cv5, cv2] 7 Tr.E) [cv10, cv8, cv13, cv4, cv0, cv5, cv2] 7 (Tr.N Tr.E [cv10, cv8, cv3, cv4, cv0, cv1, cv5, cv2] 8 Tr.E)) [cv10, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv10, cv8, cv3, cv4, cv0, cv5, cv2] 8 Tr.E) [0xff000000ff000000ff000000ff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xff00ff00ff000000ff00ff00ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0xf0f00000f0f00000f0f00000f0f, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xf0f000f0f0f00000f0f000f0f0f, cv3, cv1, cv32, cv6, cv2] 5 Tr.E) [0x3333000033330000333300003333, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x3333000033330000333300003333, cv4, cv0, cv1, cv21, cv6, cv2] 6 Tr.E) [0x3333000033330000ffff0000ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E)))
def su257 : Tr := Tr.N st255 [cv10, cv8, cv9, cv3, cv4, cv5, cv2] 7 st256
def st258 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x3333003333330000333300333333, cv0, cv1, cv35, cv6, cv2] 5 Tr.E) [0x3f3f00003f3f00003f3f00003f3f, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N Tr.E [0x5555000055550000555500005555, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x5555000055550000ffff0000ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x5555005555550000555500555555, cv0, cv1, cv32, cv6, cv2] 5 Tr.E) [0x5555555555550000555555555555, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0x5555555555550000555555555555, cv4, cv0, cv1, cv16, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [0x5555555555550000555555555555, cv0, cv1, cv5, cv20, cv6, cv2] 6 Tr.E) [0x55ff000055ff000055ff000055ff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0x5f5f00005f5f00005f5f00005f5f, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x7777000077770000777700007777, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0xaaaa0000aaaa0000aaaa0000aaaa, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E)))
def st259 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xcccc0000cccc0000cccc0000cccc, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [0xcccc0000cccc0000cccc0000cccc, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xcccccccccccc0000cccccccccccc, cv3, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xf0f00000f0f00000f0f00000f0f0, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [0xf0f00000f0f00000f0f00000f0f0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xff000000ff000000ff000000ff00, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xff000000ff000000ff000000ff00, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xffaa0000ffaa0000ffaa0000ffaa, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0xffff000000000000ffff00000000, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xffff000000000000ffff00000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xffff0000f0f00000ffff0000f0f0, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E)))
def su260 : Tr := Tr.N st258 [0xaaaa0000aaaa0000aaaa0000aaaa, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 st259
def su261 : Tr := Tr.N su257 [0x3333003333330000333300333333, cv3, cv1, cv45, cv6, cv2] 5 su260
def st262 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffff0000ffff0000000000000000, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [0xffff0000ffff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [0xffff0000ffff0000ffff00000000, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E)) [cv12, cv12, cv3, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv8, cv9, cv3, cv4, cv6, cv2] 7 Tr.E) [cv12, cv8, cv11, cv3, cv0, cv6, cv2] 7 Tr.E)) [cv12, cv8, cv13, cv4, cv0, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv8, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv12, cv8, cv3, cv4, cv0, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv9, cv11, cv3, cv1, cv6, cv2] 7 Tr.E) [cv12, cv9, cv13, cv4, cv1, cv6, cv2] 7 Tr.E)))
def st263 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv12, cv9, cv3, cv4, cv1, cv6, cv2] 8 Tr.E) [cv12, cv11, cv13, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv11, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv12, cv11, cv3, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv13, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv12, cv13, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, 0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv52, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E)))
def su264 : Tr := Tr.N st262 [cv12, cv9, cv3, cv4, cv0, cv1, cv6, cv2] 8 st263
def st265 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv58, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N Tr.E [cv12, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv1, cv6, cv2] 7 Tr.E)) [cv12, 0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, 0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv3, cv4, cv0, cv1, cv6, cv2] 8 Tr.E)) [cv12, cv3, 0xaaaaffffaaaaffffaaaaffffaaaaffff, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv53, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv6, cv2] 7 Tr.E) [cv12, cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv6, cv2] 8 Tr.E)))
def st266 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, 0xcccccccccccccccc0000cccc0000cccc, cv0, cv1, cv6, cv2] 7 Tr.E) [cv12, cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv4, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, 0xccccffffccccffff0000000000000000, cv0, cv1, cv6] 7 Tr.E) [cv12, cv3, cv4, 0xccccffffccccffffccccffffccccffff, cv0, cv1, cv6, cv2] 8 Tr.E)) [cv12, cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv40, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv6, cv2] 7 Tr.E)))
def su267 : Tr := Tr.N st265 [cv12, cv3, cv59, cv4, cv0, cv1, cv6, cv2] 8 st266
def su268 : Tr := Tr.N su264 [cv12, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv1, cv6, cv2] 7 su267
def su269 : Tr := Tr.N su261 [0xffff0000ff000000ffff0000ff00, cv3, cv4, cv0, cv1, cv6, cv2] 7 su268
def st270 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv0, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, 0xf0f0fffff0f0fffff0f0fffff0f0ffff, cv1, cv6, cv2] 8 (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv60, cv1, cv6, cv2] 8 Tr.E)) [cv12, cv3, cv4, cv0, cv61, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv41, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv62, cv6, cv2] 7 Tr.E)) [cv12, cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv1, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, 0xff00ffffff00ffffff00ffffff00ffff, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv6, cv2] 8 Tr.E)))
def st271 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv30, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv25, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv22, cv6, cv2] 8 Tr.E)) [cv12, cv3, cv4, cv0, cv1, cv16, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, 0xfffff0f000000000fffff0f000000000, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv63, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, 0xffffff0000000000ffffff0000000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv42, cv6, cv2] 8 Tr.E)))
def su272 : Tr := Tr.N st270 [cv12, cv3, cv4, cv0, cv1, cv18, cv6, cv2] 8 st271
def st273 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv27, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv6, cv2] 8 (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, 0xffffffff0000ffffffffffff0000ffff, cv2] 8 Tr.E)) [cv12, cv3, cv4, cv0, cv1, cv6, cv17, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv65] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv23, cv2] 8 Tr.E)) [cv12, cv3, cv4, cv0, cv1, cv6, cv64, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv28, cv2] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, 0xffffffffffff00000000000000000000] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv2] 9 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv2, cv2] 8 Tr.E)))
def st274 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv2, cv19] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv2, cv31] 8 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv2, cv49] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv2, cv29] 8 Tr.E)) [cv12, cv3, cv4, cv0, cv1, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv2, 0xffffffffffffffffffffffffffffffff] 8 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv72] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv73] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E)))
def su275 : Tr := Tr.N st273 [cv12, cv3, cv4, cv0, cv1, cv6, cv2, 0xffffffffffffffff0000ffff0000ffff] 8 st274
def su276 : Tr := Tr.N su272 [cv12, cv3, cv4, cv0, cv1, 0xffffffff00000000cccccccc00000000, cv2] 7 su275
def st277 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, 0xfffffffffffffffff0f00000f0f00000] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv6, cv69] 7 (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv6, cv39] 7 Tr.E)) [cv12, cv3, cv4, cv0, cv1, 0xffffffff0000aaaaffffffff0000aaaa, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, 0xffffffff0000ccccffffffff0000cccc, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E)) [cv12, cv3, cv4, cv0, cv1, cv74, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv75, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv1, cv66, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv1, cv43, cv2] 7 Tr.E)))
def st278 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, 0xff00fff0ff00fff0ff00fff0ff00fff0, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, 0xff00ffffff00ffffff00ff00ff00ff00, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv70, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv78, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv6, cv2] 7 Tr.E)) [cv12, cv3, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv71, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv0, cv38, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv0, cv6, cv68, cv2] 7 Tr.E) [cv12, cv3, cv4, 0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0, cv1, cv6, cv2] 7 Tr.E)))
def su279 : Tr := Tr.N st277 [cv12, cv3, cv4, cv0, 0xff00ffccff00ffccff00ffccff00ffcc, cv6, cv2] 7 st278
def st280 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv54, cv1, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv55, cv1, cv6, cv2] 7 (Tr.N Tr.E [cv12, cv3, cv4, cv1, cv56, cv6, cv2] 7 Tr.E)) [cv12, cv3, cv4, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv4, cv1, cv24, cv6, cv2] 7 Tr.E) [cv12, cv3, cv4, cv1, cv6, cv57, cv2] 7 Tr.E)) [cv12, cv3, cv47, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv3, cv50, cv0, cv1, cv6, cv2] 7 Tr.E) [cv12, cv3, cv0, cv1, cv36, cv6, cv2] 7 Tr.E) [cv12, cv3, cv0, cv1, cv20, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv3, cv0, cv1, cv20, cv17, cv2] 6 Tr.E) [cv12, cv3, cv0, cv1, cv6, cv14, cv2] 7 Tr.E)))
def st281 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv4, cv51, cv0, cv1, cv6, cv2] 7 Tr.E) [cv12, cv4, cv0, cv1, cv15, cv6, cv2] 7 Tr.E) [cv12, cv4, cv0, cv1, cv21, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv12, cv4, cv0, cv1, cv6, cv37, cv2] 7 Tr.E) [cv12, cv4, cv1, cv33, cv46, cv2] 5 Tr.E)) [cv12, cv0, cv1, cv21, cv20, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv12, cv0, cv1, cv33, cv34, cv2] 5 Tr.E) [0xffff0000ffff0000ffffffffffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0xffff00ffffff0000ffff00ffffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xffff0f0fffff0000ffff0f0fffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0xffffffffffff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)))
def su282 : Tr := Tr.N st280 [cv12, cv4, cv48, cv0, cv1, cv6, cv2] 7 st281
def su283 : Tr := Tr.N su279 [cv12, cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv6, cv2] 7 su282
def su284 : Tr := Tr.N su276 [cv12, cv3, cv4, cv0, cv1, cv6, cv79] 7 su283
def su285 : Tr := Tr.N su269 [cv12, cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv6, cv2] 8 su284
def st286 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xf000f00ff00ff000f000f00ff00ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0xf0f0f000f0f0f000f0f0f000f0f0f, cv3, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [0x330033003300330033003300330033, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x3300330033003300ff00ff00ff00ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x33003300ff00ff0033003300ff00ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0x333333003333330033333300333333, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0x3f003f003f003f003f003f003f003f, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x550055005500550055005500550055, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x555555005555550055555500555555, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x55ffff0055ffff0055ffff0055ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x5f005f005f005f005f005f005f005f, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0x770077007700770077007700770077, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)))
def st287 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xaa00aa00aa00aa00aa00aa00aa00aa, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xaaaaaa00aaaaaa00aaaaaa00aaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xcc00cc00cc00cc00cc00cc00cc00cc, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xcc00cc00cc00cc00cc00cc00cc00cc, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xcccccc00cccccc00cccccc00cccccc, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0xf000f000f000f000f000f000f000f0, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xf000f000f000f000f000f000f000f0, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xf0f0f000f0f0f000f0f0f000f0f0f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0xff000000ff000000ff000000ff0000, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xff000000ff000000ff000000ff0000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xff00aa00ff00aa00ff00aa00ff00aa, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)))
def su288 : Tr := Tr.N st286 [0xaa00aa00aa00aa00aa00aa00aa00aa, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 st287
def st289 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xff00ff0000000000ff00ff00000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xff00ff00ff000000ff00ff00ff0000, cv3, cv4, cv0, cv5, cv6, cv2] 7 (Tr.N Tr.E [0xff00ff00ff00ff0000000000000000, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)) [0xff00ff00ff00ff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv9, cv11, cv3, cv5, cv6, cv2] 7 Tr.E)) [cv8, cv9, cv13, cv4, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv9, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv8, cv9, cv3, cv4, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv11, cv13, cv0, cv5, cv6, cv2] 7 Tr.E) [cv8, cv11, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)))
def st290 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv11, cv3, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv13, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv13, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, 0x88888888888888888888888888888888, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)) [cv8, cv52, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [cv8, cv58, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv3, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [cv8, 0xaaaaaaaa00000000aaaaaaaa00000000, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)))
def su291 : Tr := Tr.N st289 [cv8, cv11, cv3, cv0, cv1, cv5, cv6, cv2] 8 st290
def su292 : Tr := Tr.N su288 [0xff00ff0000000000ff00ff00000000, cv8, cv3, cv4, cv0, cv5, cv6, cv2] 8 su291
def st293 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv3, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, 0xaaffaaffaaffaaffaaffaaffaaffaaff, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv8, cv3, cv53, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)) [cv8, cv3, 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc, cv0, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0, cv4, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv5, cv6, cv2] 7 Tr.E)) [cv8, cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv59, cv4, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv4, cv0, cv5, cv6, cv2] 8 Tr.E)))
def st294 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv40, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv5, cv6, cv2] 8 Tr.E)) [cv8, cv3, cv4, 0xf0f0f0f000f000f0f0f0f0f000f000f0, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv0, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, 0xf0fff0ff00000000f0fff0ff00000000, cv5, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, 0xf0fff0fff0fff0fff0fff0fff0fff0ff, cv5, cv6, cv2] 8 Tr.E)))
def su295 : Tr := Tr.N st293 [cv8, cv3, cv4, 0xccffccffccffccffccffccffccffccff, cv0, cv5, cv6, cv2] 8 st294
def st296 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv61, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv41, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv8, cv3, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv5, cv6, cv2] 8 Tr.E)) [cv8, cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv8, cv3, cv4, cv0, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6, cv2] 7 Tr.E)) [cv8, cv3, cv4, cv0, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv18, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv30, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv25, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv26, cv6, cv2] 7 Tr.E)))
def st297 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv5, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, 0xffff00ffffff00ffffff00ffffff00ff, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv22, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv16, cv6, cv2] 8 Tr.E)) [cv8, cv3, cv4, cv0, cv5, 0xfffff0f000000000fffff0f000000000, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv63, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, 0xffffff0000000000ffffff0000000000, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv42, cv6, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, 0xffffffff0000000000ff00ff00000000, cv2] 7 Tr.E)))
def su298 : Tr := Tr.N st296 [cv8, cv3, cv4, cv0, 0xffff0000ffff00000000000000000000, cv5, cv6, cv2] 8 st297
def su299 : Tr := Tr.N su295 [cv8, cv3, cv4, cv0, cv60, cv5, cv6, cv2] 8 su298
def su300 : Tr := Tr.N su292 [cv8, 0xaaaaaaaaaaaaaaaa0000000000000000, cv3, cv4, cv0, cv5, cv6, cv2] 8 su299
def st301 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv27, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv6, cv2] 8 (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffff00ff00ff0000000000000000] 7 Tr.E)) [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffff00ff00ffffffffff00ff00ff, cv2] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv17, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv65] 7 Tr.E)) [cv8, cv3, cv4, cv0, cv5, cv6, cv23, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv64, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv28, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffffffff00000000000000000000] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv2] 9 Tr.E)))
def st302 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv2, 0xffffffffffffffff00ff00ff00ff00ff] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv2, cv19] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv2, cv31] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv2, cv49] 8 Tr.E)) [cv8, cv3, cv4, cv0, cv5, cv6, cv2, cv29] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv2, 0xffffffffffffffffffffffffffffffff] 8 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffffffffffff00f000f000f000f0] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv72] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E)))
def su303 : Tr := Tr.N st301 [cv8, cv3, cv4, cv0, cv5, cv6, cv2, cv2] 8 st302
def st304 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv6, cv79] 7 (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, 0xfffffffffffffffff0f00000f0f00000] 7 Tr.E)) [cv8, cv3, cv4, cv0, cv5, cv6, cv69] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv6, cv39] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E)) [cv8, cv3, cv4, cv0, cv5, cv74, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv75, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv5, cv66, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv5, cv43, cv2] 7 Tr.E)))
def st305 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, 0xffff00f0ffff00f0ffff00f0ffff00f0, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, 0xffff00ffffff00ffffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv76, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv67, cv6, cv2] 7 Tr.E)) [cv8, cv3, cv4, cv0, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv0, cv77, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv0, cv6, cv44, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, cv54, cv5, cv6, cv2] 7 Tr.E)))
def su306 : Tr := Tr.N st304 [cv8, cv3, cv4, cv0, 0xffff00ccffff00ccffff00ccffff00cc, cv6, cv2] 7 st305
def su307 : Tr := Tr.N su303 [cv8, cv3, cv4, cv0, cv5, cv6, cv73] 7 su306
def st308 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv4, cv56, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, cv4, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv8, cv3, cv4, cv5, cv24, cv6, cv2] 7 Tr.E)) [cv8, cv3, cv4, cv5, cv6, cv57, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv47, cv0, cv5, cv6, cv2] 7 Tr.E) [cv8, cv3, cv50, cv0, cv5, cv6, cv2] 7 Tr.E)) [cv8, cv3, cv0, cv36, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv3, cv0, cv5, cv20, cv6, cv2] 7 Tr.E) [cv8, cv3, cv0, cv5, cv20, cv17, cv2] 6 Tr.E) [cv8, cv3, cv0, cv5, cv6, cv14, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv3, cv32, cv45, cv6, cv2] 5 Tr.E) [cv8, 0xaaffaaffaaaaaaaaaaffaaffaaaaaaaa, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)))
def st309 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv4, cv51, cv0, cv5, cv6, cv2] 7 Tr.E) [cv8, cv4, cv0, cv15, cv5, cv6, cv2] 7 Tr.E) [cv8, cv4, cv0, cv5, cv21, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv8, cv4, cv0, cv5, cv6, cv37, cv2] 7 Tr.E) [cv8, cv4, cv0, cv21, cv16, cv6, cv2] 6 Tr.E)) [cv8, cv4, cv5, cv33, cv46, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv8, cv0, cv5, cv21, cv20, cv6, cv2] 6 Tr.E) [cv8, cv0, cv5, cv33, cv34, cv2] 5 Tr.E) [cv8, cv0, cv35, cv32, cv6, cv2] 5 (Tr.N (Tr.N Tr.E [0xff00ff00ffffff00ff00ff00ffffff, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [0xff00ffffffffff00ff00ffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su310 : Tr := Tr.N st308 [cv8, cv4, cv48, cv0, cv5, cv6, cv2] 7 st309
def st311 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0xffffff0000000000ffffff00000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0xffffff00ffffff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 (Tr.N Tr.E [0xffffff00ffffff00ffffff00ffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x5050505050505050505050505050505, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x50f050f050f050f050f050f050f050f, cv3, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)) [0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0xf0f0f0f000000000f0f0f0f00000000, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [0xf0f0f0f000000000f0f0f0f00000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0xf0f0f0f0f0f0f0f0000000000000000, cv9, cv3, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0xf0f0f0f0f0f0f0f0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv13, cv3, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)))
def st312 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv13, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv53, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv9, cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv59, cv4, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, 0xcccccccccccccccccccccccc00000000, cv1, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, cv4, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, 0xcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su313 : Tr := Tr.N st311 [cv9, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 st312
def su314 : Tr := Tr.N su310 [0xff55ff00ff55ff00ff55ff00ff55ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 su313
def su315 : Tr := Tr.N su307 [cv8, cv3, cv4, cv55, cv5, cv6, cv2] 7 su314
def su316 : Tr := Tr.N su300 [cv8, cv3, cv4, cv0, cv5, 0xffffffff00000000cccccccc00000000, cv2] 7 su315
def su317 : Tr := Tr.N su285 [0xf000f000f000f000f000f000f000f, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 su316
def st318 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv61, cv1, cv5, cv6, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, 0xff0fff0fff0fff0f0000000000000000, cv5, cv6] 7 (Tr.N Tr.E [cv9, cv3, cv4, cv1, 0xffff0000ffff00000000000000000000, cv5, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv42, cv6, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv5, 0xffffffff000000000f0f0f0f00000000, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv27, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, 0xffffffff0f0f0f0f0000000000000000] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, 0xffffffff0f0f0f0fffffffff0f0f0f0f, cv2] 8 Tr.E)))
def st319 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv65] 7 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv23, cv2] 8 (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv64, cv2] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv5, cv6, 0xffffffffffff00000000000000000000] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv2, cv2] 8 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv2, 0xffffffffffffffff0f0f0f0f0f0f0f0f] 8 Tr.E)) [cv9, cv3, cv4, cv1, cv5, cv6, cv2, cv19] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv2, cv31] 8 Tr.E) [cv9, cv3, cv4, cv1, cv5, cv6, cv2, cv29] 8 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 Tr.E) [cv9, cv3, cv4, cv1, 0xffff0f0fffff0f0fffff0000ffff0000, cv6, cv2] 7 Tr.E)))
def su320 : Tr := Tr.N st318 [cv9, cv3, cv4, cv1, cv5, cv6, cv17, cv2] 8 st319
def st321 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, cv76, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv67, cv6, cv2] 7 (Tr.N Tr.E [cv9, cv3, cv4, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 7 Tr.E)) [cv9, cv3, cv4, cv1, cv77, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, cv1, cv6, cv44, cv2] 7 Tr.E)) [cv9, cv3, cv4, cv70, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv78, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv71, cv5, cv6, cv2] 7 Tr.E) [cv9, cv3, cv4, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6, cv2] 7 Tr.E)))
def st322 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv3, cv4, cv5, cv6, cv68, cv2] 7 Tr.E) [cv9, 0xafafafafafafafafaaaaaaaaaaaaaaaa, cv4, cv1, cv5, cv6, cv2] 7 Tr.E) [cv9, cv4, cv48, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv9, cv4, cv51, cv1, cv5, cv6, cv2] 7 Tr.E) [cv9, cv4, cv1, cv15, cv5, cv6, cv2] 7 Tr.E)) [cv9, cv4, cv1, cv5, cv21, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv9, cv4, cv1, cv5, cv6, cv37, cv2] 7 Tr.E) [cv9, cv4, cv1, cv21, cv16, cv6, cv2] 6 Tr.E) [cv9, cv1, cv35, cv32, cv6, cv2] 5 (Tr.N (Tr.N Tr.E [0xf0fffff0f0fffff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0xf0fffff0f0fffff0f0fffff0f0fffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su323 : Tr := Tr.N st321 [cv9, cv3, cv4, cv5, cv38, cv6, cv2] 7 st322
def su324 : Tr := Tr.N su320 [cv9, cv3, cv4, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 7 su323
def st325 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x11331133113311331133113311331133, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x15151515151515151515151515151515, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv11, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x44444444444444444444444444444444, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x44444444444444444444444444444444, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x44cc44cc44cc44cc44cc44cc44cc44cc, cv3, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [0x4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c4c, cv3, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x50505050505050505050505050505050, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x50505050505050505050505050505050, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x50f050f050f050f050f050f050f050f0, cv3, cv4, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x54545454545454545454545454545454, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x55005500550055005500550055005500, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def st326 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x55550000555500005555000055550000, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x55550000555500005555000055550000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x5555000055550000ffff0000ffff0000, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0x55555500555555005555550055555500, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x55555555000000005555555500000000, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x55555555000000005555555500000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [0x55555555555555550000000000000000, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x55555555555555550000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv13, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, 0x88888888888888888888888888888888, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv52, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su327 : Tr := Tr.N st325 [0x55005500550055005500550055005500, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 st326
def st328 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, 0xaaaa0000aaaa0000aaaa0000aaaa0000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, 0xaaaaaaaa00000000aaaaaaaa00000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv13, 0xaaaaaaaaaaaaaaaa0000000000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv13, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv13, cv53, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv13, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv13, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv59, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def st329 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv40, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, 0xf000f000f000f000f000f000f000f000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, 0xf0f00000f0f00000f0f00000f0f00000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv13, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, 0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv60, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv61, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su330 : Tr := Tr.N st328 [cv13, cv4, 0xdddddddddddddddddddddddddddddddd, cv0, cv1, cv5, cv6, cv2] 8 st329
def su331 : Tr := Tr.N su327 [cv13, cv58, cv4, cv0, cv1, cv5, cv6, cv2] 8 su330
def su332 : Tr := Tr.N su324 [0xfff0fff0fff0fff0fff0fff0fff0fff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 su331
def st333 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv62, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, 0xff00ff0000000000ff00ff0000000000, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv13, cv4, cv0, 0xff00ff00ff000000ff00ff00ff000000, cv5, cv6, cv2] 7 Tr.E)) [cv13, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv1, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, 0xff55ff55ff55ff55ff55ff55ff55ff55, cv5, cv6, cv2] 8 Tr.E)) [cv13, cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv18, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv30, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv25, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, 0xffff000055550000ffff000055550000, cv6, cv2] 7 Tr.E)))
def st334 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv26, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv5, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, 0xffff555500000000ffff555500000000, cv2] 7 Tr.E)) [cv13, cv4, cv0, cv1, cv5, 0xffff5555ffff5555ffff5555ffff5555, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv22, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv16, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv63, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv2] 7 Tr.E)))
def su335 : Tr := Tr.N st333 [cv13, cv4, cv0, cv1, 0xffff0000f0f00000ffff0000f0f00000, cv6, cv2] 7 st334
def st336 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv42, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, 0xffffffff000000005555555500000000, cv2] 7 (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv2] 7 Tr.E)) [cv13, cv4, cv0, cv1, cv5, cv27, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, cv6, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, 0xffffffff555555550000000000000000] 7 Tr.E)) [cv13, cv4, cv0, cv1, cv5, cv6, 0xffffffff55555555ffffffff55555555, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, cv17, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv65] 7 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv23, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, cv64, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv28, cv2] 8 Tr.E)))
def st337 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv2, cv2] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff5555555555555555] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv2, cv19] 8 Tr.E)) [cv13, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, cv2, cv31] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv2, cv49] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv2, cv29] 8 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffffffffff] 8 Tr.E)))
def su338 : Tr := Tr.N st336 [cv13, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff00000000000000000000] 7 st337
def su339 : Tr := Tr.N su335 [cv13, cv4, cv0, cv1, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 su338
def st340 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 7 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv73] 7 (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 7 Tr.E)) [cv13, cv4, cv0, cv1, cv5, cv6, cv79] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffffffff0f00000f0f00000] 7 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv6, cv69] 7 Tr.E)) [cv13, cv4, cv0, cv1, cv5, cv6, cv39] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, cv5, cv74, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, cv5, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv75, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 7 Tr.E)))
def st341 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv5, cv43, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, cv76, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, cv67, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 7 Tr.E)) [cv13, cv4, cv0, cv1, cv77, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, cv1, cv6, cv44, cv2] 7 Tr.E) [cv13, cv4, cv0, 0xff55ff55ff00ff00ff55ff55ff00ff00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv70, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, cv78, cv5, cv6, cv2] 7 Tr.E)))
def su342 : Tr := Tr.N st340 [cv13, cv4, cv0, cv1, cv5, cv66, cv2] 7 st341
def st343 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv0, cv71, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv13, cv4, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6, cv2] 7 Tr.E)) [cv13, cv4, cv0, cv5, cv38, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv0, cv5, cv6, cv68, cv2] 7 Tr.E) [cv13, cv4, 0xf5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv13, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv4, cv54, cv1, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv55, cv1, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv1, cv56, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv4, cv1, 0xfff0fff0fff0fff0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 7 Tr.E) [cv13, cv4, cv1, cv5, cv24, cv6, cv2] 7 Tr.E)))
def st344 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv47, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv13, cv50, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv13, cv0, cv1, cv36, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv13, cv0, cv1, cv5, cv20, cv6, cv2] 7 Tr.E) [cv13, cv0, cv1, cv5, cv20, cv17, cv2] 6 Tr.E)) [cv13, cv0, cv1, cv5, cv6, cv14, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv13, cv1, cv32, cv45, cv6, cv2] 5 Tr.E) [0x5555555555555555ffffffffffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x55555555ffffffff55555555ffffffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x555555ff555555ff555555ff555555ff, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x5555ffff5555ffff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)))
def su345 : Tr := Tr.N st343 [cv13, cv4, cv1, cv5, cv6, cv57, cv2] 7 st344
def su346 : Tr := Tr.N su342 [cv13, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 7 su345
def su347 : Tr := Tr.N su339 [cv13, cv4, cv0, cv1, cv5, cv6, cv72] 7 su346
def su348 : Tr := Tr.N su332 [cv13, cv4, cv0, cv41, cv1, cv5, cv6, cv2] 8 su347
def st349 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x55ff000055ff000055ff000055ff0000, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0x55ff55ff0000000055ff55ff00000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N Tr.E [0x55ff55ff55ff55ff0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)) [0x55ff55ff55ff55ff55ff55ff55ff55ff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x57575757575757575757575757575757, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0x5f005f005f005f005f005f005f005f00, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E)) [0x5f5f00005f5f00005f5f00005f5f0000, cv3, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x5f5f5f5f000000005f5f5f5f00000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x5f5f5f5f5f5f5f5f0000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [0x5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x77777777000000007777777700000000, cv3, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [0x77777777777777770000000000000000, cv3, cv4, cv0, cv1, cv5, cv6] 7 Tr.E)))
def st350 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0x88888888888888880000000000000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x88888888888888888888888888888888, cv3, cv53, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [0x88888888888888888888888888888888, cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [0x88888888888888888888888888888888, cv3, cv4, cv0, cv70, cv5, cv6, cv2] 8 Tr.E) [0x88888888888888888888888888888888, cv4, cv40, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [0x88888888888888888888888888888888, cv47, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [0x8888ffff8888ffff8888ffff8888ffff, cv3, cv4, cv0, cv1, cv6, cv2] 7 Tr.E) [0x88ff88ff88ff88ff88ff88ff88ff88ff, cv3, cv4, cv0, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xc000c000c000c000c000c000c000c000, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, 0xc0c00000c0c00000c0c00000c0c00000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xc0c0c0c000000000c0c0c0c000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su351 : Tr := Tr.N st349 [0x88888888000000008888888800000000, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 st350
def st352 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv53, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, cv53, cv4, cv0, cv1, cv5, cv6, cv79] 8 (Tr.N Tr.E [cv3, cv53, cv4, cv0, cv1, cv5, cv75, cv2] 8 Tr.E)) [cv3, cv53, cv4, cv0, cv1, cv77, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv53, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 8 Tr.E) [cv3, cv53, cv4, cv61, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv53, cv4, cv1, cv30, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv53, cv4, cv78, cv5, cv6, cv2] 7 Tr.E) [cv3, cv53, cv47, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv53, cv0, cv61, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv53, cv0, cv1, cv18, cv5, cv6, cv2] 8 Tr.E) [cv3, cv53, cv0, cv1, cv18, cv5, cv75, cv2] 7 Tr.E)))
def st353 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv53, cv0, cv70, cv5, 0xffffffff88888888ffffffff88888888, cv2] 6 Tr.E) [cv3, cv53, cv0, cv70, cv5, cv75, cv2] 6 Tr.E) [cv3, cv53, cv0, cv18, cv26, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv53, cv0, cv18, cv5, cv6, cv28, cv2] 7 Tr.E) [cv3, cv53, cv0, cv18, cv5, cv43, cv2] 6 Tr.E)) [cv3, cv53, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xc0c0c0c0c0c0c0c0ffffffffffffffff, cv4, cv0, cv1, cv5, cv6] 7 Tr.E) [cv3, 0xc0c0c0c0ffffffffc0c0c0c0ffffffff, cv4, cv0, cv1, cv5, cv2] 7 Tr.E) [cv3, 0xc0c0ffffc0c0ffffc0c0ffffc0c0ffff, cv4, cv0, cv1, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0cc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xc0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0, cv4, cv1, cv5, cv6, cv2] 7 Tr.E)))
def su354 : Tr := Tr.N st352 [cv3, cv53, cv0, cv70, cv5, cv6, cv2] 7 st353
def su355 : Tr := Tr.N su351 [cv3, 0xc0c0c0c0c0c0c0c00000000000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 su354
def st356 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv60, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv26, cv6, cv2] 6 Tr.E)) [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv6, cv28, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv6, 0xffffffffffffffffc8c8c8c8c8c8c8c8] 7 Tr.E)) [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, cv5, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, cv1, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, cv6, cv2] 7 Tr.E) [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv5, 0xffffffffc8c8c8c8ffffffffc8c8c8c8, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, 0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xcc000000cc000000cc000000cc000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def st357 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcc00cc00cc00cc000000000000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv1, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv4, cv0, cv18, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcc00cc00cc00cc00cc00cc00cc00cc00, cv0, cv1, cv18, cv5, cv6, cv2] 8 Tr.E)) [cv3, 0xcc00cc00ffffffffcc00cc00ffffffff, cv4, cv0, cv1, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcc88cc88cc88cc88cc88cc88cc88cc88, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xccc0ccc0ccc0ccc0ccc0ccc0ccc0ccc0, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xccc8ccc8ccc8ccc8ccc8ccc8ccc8ccc8, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xcccc000000000000cccc000000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccc0000cccc00000000000000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su358 : Tr := Tr.N st356 [cv3, 0xcc00cc0000000000cc00cc0000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 st357
def st359 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv1, cv16, cv6, cv2] 8 Tr.E) [cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv0, cv1, cv5, cv16, cv6, cv2] 8 (Tr.N Tr.E [cv3, 0xcccc8888cccc8888cccc8888cccc8888, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, 0xccccc0c0ccccc0c0ccccc0c0ccccc0c0, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, 0xccccc8c8ccccc8c8ccccc8c8ccccc8c8, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xcccccc00cccccc00cccccc00cccccc00, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, 0xcccccc88cccccc88cccccc88cccccc88, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcccccccc000000000000000000000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccccccc00000000cccccccc00000000, cv59, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv5, cv42, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, cv1, cv5, cv23, cv2] 8 Tr.E)))
def st360 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcccccccc00000000cccccccc00000000, cv0, cv1, cv5, cv6, cv23, cv2] 8 Tr.E) [cv3, 0xcccccccc00000000cccccccc00000000, cv0, cv1, cv5, cv14, cv2] 7 Tr.E) [cv3, 0xcccccccc00000000cccccccc00000000, cv0, cv1, cv5, cv66, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xcccccccc88888888cccccccc88888888, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xccccccccc0c0c0c0ccccccccc0c0c0c0, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, 0xccccccccc8c8c8c8ccccccccc8c8c8c8, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccc00cc00cccccccccc00cc00, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccccccccccc0000cccccccccccc0000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xccccccccccccc0c0ccccccccccccc0c0, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccccccc00cccccccccccccc00, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv59, cv4, cv0, cv1, cv5, cv42, cv6] 8 Tr.E)))
def su361 : Tr := Tr.N st359 [cv3, 0xcccccccc00000000cccccccc00000000, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6, cv2] 8 st360
def su362 : Tr := Tr.N su358 [cv3, 0xcccc0000cccc0000cccc0000cccc0000, cv4, cv0, cv1, cv5, cv6, cv2] 9 su361
def su363 : Tr := Tr.N su355 [cv3, 0xc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ff, cv4, cv0, cv5, cv6, cv2] 7 su362
def st364 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv59, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E) [cv3, cv59, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N Tr.E [cv3, cv59, cv4, cv0, cv1, cv5, cv6, cv29] 8 Tr.E)) [cv3, cv59, cv4, cv0, cv1, cv5, cv66, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv59, cv4, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 8 Tr.E) [cv3, cv59, cv4, cv0, cv1, cv6, cv44] 7 Tr.E)) [cv3, cv59, cv4, cv0, cv71, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv59, cv4, cv55, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv59, cv0, cv1, cv5, cv16, cv6, cv2] 8 Tr.E) [cv3, cv59, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv3, cv59, cv0, cv1, cv22, cv16, cv6, cv2] 7 Tr.E) [cv3, 0xcccccccccccccccc0000cccc0000cccc, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def st365 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xccccccccccccccccc0c0c0c0c0c0c0c0, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xccccccccccccccccc0c0c0c0c0c0c0c0, cv61, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xccccccccccccccccc8c8c8c8c8c8c8c8, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccccccccccc00cc00cc00cc00, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccccccccccccccccc88cc88cc88cc88, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, 0xcccccccccccccccccccc0000cccc0000, cv4, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccccccccccccccccc00000000, cv4, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, 0xffff0000ffff0000ffff000000000000, cv6, cv2] 7 Tr.E) [cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv22, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffff00000000] 8 Tr.E)))
def su366 : Tr := Tr.N st364 [cv3, 0xcccccccccccccccc8888888888888888, cv4, cv0, cv1, cv5, cv6, cv2] 8 st365
def st367 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccccccccccccccccc00000000, cv0, 0xffccffccffccffccffccffccff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, 0xcccccccccccccccccccccccc88888888, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, 0xccccccccccccccccccccccccc0c0c0c0, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, 0xcccccccccccccccccccccccccc00cc00, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, 0xcccccccccccccccccccccccccccc0000, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv4, cv0, cv1, cv5, cv6, cv2] 9 Tr.E)) [cv3, cv4, 0xccccccccccccccccffffffffffffffff, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xccccccccffffffff00000000ffffffff, cv0, cv1, cv5, cv2] 7 Tr.E) [cv3, cv4, 0xccccccccffffffffccccccccffffffff, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xccccffffccccffff0000000000000000, cv0, cv1, cv5, cv6] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xccccffffccccffff0000ffff0000ffff, cv0, cv1, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xccccffffccccffffccccffffccccffff, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def st368 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xccffccffccffccff00ff00ff00ff00ff, cv0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xccffccffccffccffccffccffccffccff, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0f, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcf, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xdddddddddddddddddddddddddddddddd, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv1, 0xffffe0e0ffffe0e0ffffe0e0ffffe0e0, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, 0xffe0ffe0ffe0ffe0ffe0ffe0ffe0ffe0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv47, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xeeeeeeee00000000eeeeeeee00000000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xeeeeeeeecccccccceeeeeeeecccccccc, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su369 : Tr := Tr.N st367 [cv3, cv4, 0xccffccff00ff00ffccffccff00ff00ff, cv0, cv5, cv6, cv2] 7 st368
def su370 : Tr := Tr.N su366 [cv3, 0xcccccccccccccccccccccccc00000000, cv0, cv1, cv5, cv66, cv2] 7 su369
def st371 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv51, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xeeeeeeeeeeeeeeeecccccccccccccccc, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv2] 7 Tr.E)) [cv3, cv4, cv40, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv1, cv5, cv27, cv2] 7 Tr.E) [cv3, cv4, cv40, cv0, cv1, cv5, cv6, cv2, cv29] 8 Tr.E)) [cv3, cv4, cv40, cv0, cv1, cv6, cv44, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv40, cv0, cv5, cv38, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf0f00000f0f000000000000000000000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0000000000000000000000000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv25, cv5, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv6, cv2] 9 Tr.E)))
def st372 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv28, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv5, cv38, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv1, cv30, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv1, cv5, cv6, cv64, cv2] 8 Tr.E)) [cv3, cv4, 0xf0f0f0f000f000f0f0f0f0f000f000f0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0e0e0e0e0f0f0f0f0e0e0e0e0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f00000f0f0f0f0f0f00000, cv1, cv5, cv6, 0xffffffffffff00000000000000000000] 7 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f0c0c0f0f0f0f0f0f0c0c0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def su373 : Tr := Tr.N st371 [cv3, cv4, 0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv64, cv2] 8 st372
def st374 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv5, cv6, cv31] 8 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv1, cv5, cv6, cv2, cv31] 8 (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f0f0f0e0e0e0e0e0e0e0e0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f0f0f0f0f00000f0f00000, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, 0xf0f0f0f0f0f0f0f0f0f0f0f000000000, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xf0f0fffff0f0fffff0f0fffff0f0ffff, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xf0fff0ff00000000f0fff0ff00000000, cv1, cv5, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xf0fff0ff00ff00fff0fff0ff00ff00ff, cv5, cv6, cv2] 7 Tr.E)))
def st375 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfc00fc00fc00fc00fc00fc00fc00fc00, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfcccfcccfcccfcccfcccfcccfcccfccc, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfcfc0000fcfc0000fcfc0000fcfc0000, cv1, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xfcfcccccfcfcccccfcfcccccfcfccccc, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfcfcfcfc00000000fcfcfcfc00000000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfcfcfcfcccccccccfcfcfcfccccccccc, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xfcfcfcfcfcfcfcfc0000000000000000, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su376 : Tr := Tr.N st374 [cv3, cv4, cv0, 0xf0fff0fff0fff0fff0fff0fff0fff0ff, cv1, cv5, cv6, cv2] 8 st375
def su377 : Tr := Tr.N su373 [cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv0, cv1, cv5, cv6, cv2] 9 su376
def su378 : Tr := Tr.N su370 [cv3, cv4, 0xeeeeeeeeeeeeeeee0000000000000000, cv0, cv1, cv5, cv6, cv2] 8 su377
def su379 : Tr := Tr.N su363 [cv3, cv59, cv4, cv0, cv1, cv5, cv27] 7 su378
def su380 : Tr := Tr.N su348 [0x5555ffff5555ffff5555ffff5555ffff, cv3, cv4, cv0, cv1, cv5, cv6, cv2] 8 su379
def su381 : Tr := Tr.N su317 [cv9, cv3, cv4, 0xf0f0f0f0f0f0f0f00000000000000000, cv1, cv5, cv6, cv2] 8 su380
def st382 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv55, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv61, cv1, cv26, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv61, cv1, cv5, cv6, cv28, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv61, cv1, cv5, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv61, cv1, cv5, cv43, cv2] 7 Tr.E) [cv3, cv4, cv0, cv61, cv5, cv38, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xfefefefe00000000fefefefe00000000, cv1, cv5, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfefefefefefefefe0000000000000000, cv1, cv5, cv6] 7 Tr.E) [cv3, cv4, cv0, 0xff00ff00000000000000000000000000, cv1, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv30, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff000000000000000000, cv5, cv6, cv2, cv49] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xff0fff0fff0fff0f0000000000000000, cv5, cv6] 7 Tr.E)))
def st383 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffccffccffccffcc0000000000000000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffccffccffccffcccccccccccccccccc, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffeeffeeffeeffee0000000000000000, cv5, cv6] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xfff0fff0fff0fff00000000000000000, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000000000000000000000000000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv25, 0xffff0000ffff00000000000000000000, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv25, cv5, cv42, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv25, cv5, cv65] 7 Tr.E) [cv3, cv4, cv0, cv1, cv25, cv22, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv25, cv16, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv25, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv25, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 8 Tr.E)))
def su384 : Tr := Tr.N st382 [cv3, cv4, cv0, cv1, 0xffaaffaaffaaffaa0000000000000000, cv5, cv6, cv2] 8 st383
def st385 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv26, cv65] 6 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv42, cv6] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv6, cv2] 9 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv5, cv6, cv29] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv6, cv44] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv6, cv2, cv29] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000ffff00000000000000000000, cv6, cv39] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff0000aaaa0000aaaa0000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000cccc0000cccc0000, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff0000f0f00000f0f00000, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffff333300000000ffff333300000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffff555500000000ffff555500000000, cv2] 7 Tr.E)))
def st386 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffaaaaffffaaaa0000000000000000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv22, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv22, cv6, cv2, cv31] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffcccc00000000ffffcccc00000000, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv20, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffccccffffcccc0000000000000000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffccccffffccccaaaa8888aaaa8888, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffccccffffcccccccccccccccccccc, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv16, cv6, cv2, cv19] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xfffff00000000000fffff00000000000, cv2] 7 Tr.E)))
def su387 : Tr := Tr.N st385 [cv3, cv4, cv0, cv1, cv5, 0xffffaaaa00000000ffffaaaa00000000, cv6, cv2] 8 st386
def su388 : Tr := Tr.N su384 [cv3, cv4, cv0, cv1, cv26, cv42, cv2] 7 su387
def st389 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv63, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xfffff0f0fffff0f00000000000000000, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv63, cv6, cv2, cv19] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xfffffafa00000000fffffafa00000000, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffffcfc00000000fffffcfc00000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffff0000000000ffff000000000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, 0xffffff00ffffff00ffffff00ffffff00, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffff0000000000ffffff0000000000, cv2] 8 Tr.E)))
def st390 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffaa00000000ffffffaa00000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffaaffffffaa0000000000000000, cv6] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffcc00000000ffffffcc00000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xfffffff000000000fffffff000000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv42, cv6, cv2] 9 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv42, cv6, cv19] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv42, cv6, cv31] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv42, cv6, cv49] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv42, cv6, 0xffffffffffffffffffffffff00000000] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv42, cv17, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv42, cv64, cv2] 8 Tr.E)))
def su391 : Tr := Tr.N st389 [cv3, cv4, cv0, cv1, cv5, 0xffffff00ffffff000000000000000000, cv6, cv2] 8 st390
def st392 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv42, cv2, 0xffffffffffffffffffffffff00000000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff0000000000ff00ff00000000, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff000000000f0f0f0f00000000, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffff000000005555555500000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000aaaaaaaa00000000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000cccc000000000000, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000cccccccc00000000, cv2, 0xffffffffffffffffcccccccccccccccc] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000eeeeeeee00000000, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000f0f0f0f000000000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000fcfcfcfc00000000, cv2] 7 Tr.E)))
def st393 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffccffcc00000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv27, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv27, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv27, cv2, cv29] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffaaaa00000000, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffcccc00000000, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000fffff0f000000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ffffff0000000000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv6, cv2] 9 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff00000000ffffffffffffffff, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff0000ffffffffffff0000ffff, cv2] 8 Tr.E)))
def su394 : Tr := Tr.N st392 [cv3, cv4, cv0, cv1, cv5, 0xffffffff00000000ff00ff0000000000, cv6, cv2] 8 st393
def su395 : Tr := Tr.N su391 [cv3, cv4, cv0, cv1, cv5, cv42, cv28, cv2] 8 su394
def su396 : Tr := Tr.N su388 [cv3, cv4, cv0, cv1, cv5, 0xfffff0f000000000ffff000000000000, cv2] 7 su395
def st397 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff00ff00ffffffffff00ff00ff, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff0f0f0f0f0000000000000000] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff0f0f0f0fffffffff0f0f0f0f, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff33333333ffffffff33333333, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff555555550000000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff55555555ffffffff55555555, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff88888888ffffffff88888888, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv74, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffaa00aa00ffffffffaa00aa00, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffaaaa0000ffffffffaaaa0000, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffaaaaaaaa0000000000000000, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv37, cv2] 8 Tr.E)))
def st398 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv17, cv2] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv75, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffcccc00000000000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffcccc0000ffffffffcccc0000, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv65] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv65, cv23] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv65, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv14, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv66, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv23, cv2] 9 Tr.E)))
def su399 : Tr := Tr.N st397 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffaaaaaaaaffffffff00000000, cv2] 8 st398
def st400 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffff000f000fffffffff000f000, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffff0f00000fffffffff0f00000, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffff0f0f0f00000000000000000, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv57, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffff0f0f0f0ffffffff00000000, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv64, cv2] 9 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffafafafafffffffffafafafa, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffcfcfcfc0000000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffcfcfcfcfffffffffcfcfcfc, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffff00ff000000000000000000, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffff00ff00ffffffff00000000, cv2] 8 Tr.E)))
def st401 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff00000000000000000000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff00000000000000000000, 0xffffffffffff0000ffffffffffff0000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff00000000000000000000, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv44, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffff0000ffffffff00000000, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffaaaa0000000000000000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffcccc0000000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffccccffffffffffffcccc, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, 0xfffffffffffff0f00000000000000000] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffffff000000000000000000] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv2] 9 Tr.E)))
def su402 : Tr := Tr.N st400 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffffccffcc0000000000000000] 7 st401
def su403 : Tr := Tr.N su399 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffffeeeeeeee0000000000000000] 7 su402
def st404 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff0000ffff0000ffff] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff00ff00ff00ff00ff] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff0f0f0f0f0f0f0f0f] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff3333333333333333] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff5555555555555555] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv72] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffa0a0a0a0a0a0a0a0] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv73] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffaaaa0000aaaa0000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffaaaaaaaa00000000] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv19] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv79] 8 Tr.E)))
def st405 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccc0000cccc0000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccccccc00000000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 9 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffeeeeeeeeeeeeeeee] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffff000f000f000f000] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffff0f00000f0f00000] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffff0f0f0f000000000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv31] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffffafafafafafafafa] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffffcfcfcfcfcfcfcfc] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv69] 8 Tr.E)))
def su406 : Tr := Tr.N st404 [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffcc00cc00cc00cc00] 8 st405
def st407 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffccffccffccffcc] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv39] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, cv29] 9 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffaaaaffffaaaa] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffccccffffcccc] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffeeeeffffeeee] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffffffff0f0fffff0f0] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffffffffafafffffafa] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffff00000000] 9 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffaaaaaaaa] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffcccccccc] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xfffffffffffffffffffffffff0f0f0f0] 8 Tr.E)))
def st408 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffffff0000] 8 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv65, cv66] 7 Tr.E) [cv3, cv4, cv0, cv1, cv5, cv65, cv28] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffff0000ffff0000ffffffff, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffff00ffffff0000ffff00ff, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff0000ffff0f0fffff0000ffff0f0f, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0000ffffaaaaffff0000ffffaaaa, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0000ffffccccffff0000ffffcccc, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff0055ffff0055ffff0055ffff0055, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff00ccffff00ccffff00ccffff00cc, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff00f0ffff00f0ffff00f0ffff00f0, cv6, cv2] 7 Tr.E)))
def su409 : Tr := Tr.N st407 [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffffffffffff00ff00] 8 st408
def su410 : Tr := Tr.N su406 [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffffff00ff0000000000] 8 su409
def su411 : Tr := Tr.N su403 [cv3, cv4, cv0, cv1, cv5, cv6, cv2, 0xffffffffffffffff00000000ffffffff] 8 su410
def su412 : Tr := Tr.N su396 [cv3, cv4, cv0, cv1, cv5, cv6, 0xffffffff00ff00ff0000000000000000] 7 su411
def st413 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff0f0fffff0f0fffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff8080ffff8080ffff8080ffff8080, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff8800ffff8800ffff8800ffff8800, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff8888ffff0000ffff8888ffff0000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2, cv19] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2, cv49] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffa000ffffa000ffffa000ffffa000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffa0a0ffff0000ffffa0a0ffff0000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffa0a0ffffa0a0ffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv76, cv6, cv2] 8 Tr.E)))
def st414 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffaa00ffff0000ffffaa00ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffaa00ffffaa00ffff0000ffff0000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv67, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffffaa88ffffaa88ffffaa88ffffaa88, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xffffaaa0ffffaaa0ffffaaa0ffffaaa0, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv21, cv16, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffaaaaffff0000ffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffff8888ffff8888, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffffa0a0ffffa0a0, cv6, cv2] 7 Tr.E)))
def su415 : Tr := Tr.N st413 [cv3, cv4, cv0, cv1, cv76, cv6, cv2, cv19] 7 st414
def st416 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv22, cv16, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv22, cv63, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv22, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, cv1, cv22, cv27, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv22, cv6, cv2, cv29] 8 Tr.E) [cv3, cv4, cv0, cv1, cv22, cv6, cv2, 0xffffffffffffffffffffccccffffcccc] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv22, cv6, cv2, 0xfffffffffffffffffffff0f0fffff0f0] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffc000ffffc000ffffc000ffffc000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffc0c0ffff0000ffffc0c0ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffc0c0ffffc0c0ffff0000ffff0000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv77, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv77, cv6, cv2, cv19] 7 Tr.E)))
def st417 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffc8c8ffffc8c8ffffc8c8ffffc8c8, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffcc00ffffcc00ffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffccccffff0000ffff0000ffff0000, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv66, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, 0xffffccccffffccccffff8888ffff8888, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffccccffffccccffffc0c0ffffc0c0, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv16, cv63, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv16, cv6, cv2, cv29] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv16, cv6, cv2, 0xffffffffffffffffffffaaaaffffaaaa] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xffffe0e0ffffe0e0ffffe0e0ffffe0e0, cv6, cv2] 7 Tr.E)))
def su418 : Tr := Tr.N st416 [cv3, cv4, cv0, cv1, cv77, cv75, cv2] 7 st417
def su419 : Tr := Tr.N su415 [cv3, cv4, cv0, cv1, 0xffffaaaaffffaaaaffffaa00ffffaa00, cv6, cv2] 7 su418
def st420 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv6, cv2, cv29] 7 Tr.E) [cv3, cv4, cv0, cv1, 0xfffff0f0ffff0000ffff0000ffff0000, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv1, 0xffffff00ffff0000ffff0000ffff0000, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv42, cv6, cv44, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv27, cv44, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv6, 0xffffffff0000ffff0000ffff0000ffff, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv1, cv6, cv65, 0xffffffffffffccccffff0000ffff0000] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv6, 0xffffffffffff00000000000000000000, cv44] 7 Tr.E) [cv3, cv4, cv0, cv1, cv6, cv44, cv2] 8 Tr.E) [cv3, cv4, cv0, cv1, cv6, 0xffffffffffff0000ffffffffffff0000, cv2, cv29] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv1, cv6, 0xffffffffffffaaaaffff0000ffff0000, cv2] 7 Tr.E) [cv3, cv4, cv0, cv1, cv6, 0xffffffffffffccccffff0000ffff0000, cv2] 7 Tr.E)))
def st421 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ff00ff00ff00fff0fff0fff0fff0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff00ff00ff00ffffff00ff00ff00ffff, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff00ff55ff00ff55ff00ff55ff00ff55, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff00ffccff00ffccff00ffccff00ffcc, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff00fff0ff00fff0ff00fff0ff00fff0, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xff00ffffff00ffffff00ff00ff00ff00, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff55ff55ff00ff00ff55ff55ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff80ff80ff80ff80ff80ff80ff80ff80, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff88ff00ff88ff00ff88ff00ff88ff00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xff88ff88ff00ff00ff88ff88ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xff88ff88ff88ff88ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E)))
def su422 : Tr := Tr.N st420 [cv3, cv4, cv0, cv1, cv28, cv44, cv2] 7 st421
def st423 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv70, cv5, 0xffffffff88888888ffffffff88888888, cv2] 7 Tr.E) [cv3, cv4, cv0, cv70, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, 0xffa0ff00ffa0ff00ffa0ff00ffa0ff00, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xffa0ffa0ff00ff00ffa0ffa0ff00ff00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffa0ffa0ffa0ffa0ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv78, cv5, cv6, cv23, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv78, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv78, cv5, cv74, cv2] 7 Tr.E) [cv3, cv4, cv0, cv78, cv76, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffaaff00ff00ff00ffaaff00ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffaaffaaff00ff00ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E)))
def st424 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv30, cv5, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, 0xffc0ff00ffc0ff00ffc0ff00ffc0ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffc0ffc0ff00ff00ffc0ffc0ff00ff00, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 8 Tr.E)) [cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv79] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv75, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv77, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffc8ffc8ffc8ffc8ffc8ffc8ffc8ffc8, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffccff00ff00ff00ffccff00ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffccff00ffccff00ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E)))
def su425 : Tr := Tr.N st423 [cv3, cv4, cv0, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv18, cv5, cv6, cv2] 8 st424
def su426 : Tr := Tr.N su422 [cv3, cv4, cv0, cv70, cv5, cv6, cv2] 8 su425
def su427 : Tr := Tr.N su419 [cv3, cv4, cv0, cv1, 0xffffeeeeffffeeeeffff0000ffff0000, cv6, cv2] 7 su426
def st428 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv42, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv3, cv4, cv0, 0xffccffccff00ff00ffccffccff00ff00, cv5, cv23, cv2] 7 Tr.E)) [cv3, cv4, cv0, 0xffccffccff88ff88ffccffccff88ff88, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffccffccffc0ffc0ffccffccffc0ffc0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv71, cv5, cv42, cv6] 7 Tr.E)) [cv3, cv4, cv0, cv71, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv71, cv5, cv66, cv2] 7 Tr.E) [cv3, cv4, cv0, cv71, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffccffccffccffccff88ff88ff88ff88, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xffccffccffccffccffc0ffc0ffc0ffc0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffccffccffccffccffccffccff00ff00, cv5, cv6, cv2] 7 Tr.E)))
def st429 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv18, cv26, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv18, cv5, cv6, cv28, cv2] 8 Tr.E) [cv3, cv4, cv0, cv18, cv5, cv6, 0xffffffffffaaffaaffffffffffaaffaa, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv18, cv5, cv6, 0xfffffffffff0fff0fffffffffff0fff0, cv2] 7 Tr.E) [cv3, cv4, cv0, cv18, cv5, cv6, cv2, cv49] 8 Tr.E)) [cv3, cv4, cv0, cv18, cv5, cv17, cv28, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv18, cv5, 0xffffffffcc00cc00ffffffffcc00cc00, cv2] 7 Tr.E) [cv3, cv4, cv0, cv18, cv5, cv43, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xffe0ffe0ffe0ffe0ffe0ffe0ffe0ffe0, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfff0ff00ff00ff00fff0ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfff0fff0ff00ff00ff00ff00ff00ff00, cv5, cv6, cv2] 7 Tr.E)))
def su430 : Tr := Tr.N st428 [cv3, cv4, cv0, cv18, cv30, cv5, cv6, cv2] 8 st429
def st431 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfff0fff0ffa0ffa0fff0fff0ffa0ffa0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfff0fff0ffc0ffc0fff0fff0ffc0ffc0, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv30, cv26, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv30, cv26, cv23, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv30, cv5, cv6, cv28, cv2] 8 Tr.E) [cv3, cv4, cv0, cv30, cv5, cv6, 0xffffffffffccffccffffffffffccffcc, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv30, cv5, cv23, cv28, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv30, cv5, cv43, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfffcfffcff00ff00fffcfffcff00ff00, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfffcfffcfffcfffcfffcfffcfffcfffc, cv26, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, 0xfffcfffcfffcfffcfffcfffcfffcfffc, cv5, cv6, cv28, cv2] 7 Tr.E) [cv3, cv4, cv0, 0xfffcfffcfffcfffcfffcfffcfffcfffc, cv5, cv43, cv2] 6 Tr.E)))
def st432 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv26, cv38, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, 0xffff00ff00ff00ffffff00ff00ff00ff, cv6, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, 0xfffff0f000000000fffff0f000000000, 0xfffffff0ff00ff00fffffff0ff00ff00, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, 0xffffff0000000000ffffff0000000000, cv38, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, 0xffffff00ff00ff00ff00ff00ff00ff00, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv5, cv38, cv42, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv38, cv6, cv2] 8 Tr.E) [cv3, cv4, cv0, cv5, cv38, cv17, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, cv38, cv65] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv38, cv23, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, cv38, 0xffffffffeeeeeeeeffffffffeeeeeeee, cv2] 6 Tr.E)))
def su433 : Tr := Tr.N st431 [cv3, cv4, cv0, cv25, cv5, cv38, cv6, cv2] 8 st432
def su434 : Tr := Tr.N su430 [cv3, cv4, cv0, 0xfff0fff0ff00ff00fff0fff0ff00ff00, cv5, cv6, cv2] 8 su433
def st435 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv28, cv2] 8 Tr.E) [cv3, cv4, cv0, cv5, 0xffffff00ffffff00ffffff00ffffff00, cv43, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv0, cv5, 0xffffffccff00ff00ffffffccff00ff00, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv5, 0xfffffff0ff00ff00fffffff0ff00ff00, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv42, cv6, cv68, cv2] 8 Tr.E) [cv3, cv4, cv0, cv5, 0xffffffff00000000cccccccc00000000, 0xffffffffff00ff00ffccffccff00ff00, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv5, cv27, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv6, 0xffffffff00ff00ff00ff00ff00ff00ff, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, cv6, cv65, 0xffffffffffccffccff00ff00ff00ff00] 7 Tr.E) [cv3, cv4, cv0, cv5, cv6, cv68, cv2] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv6, cv68, cv19] 7 Tr.E) [cv3, cv4, cv0, cv5, cv6, 0xffffffffff00ff00ffccffccff00ff00, cv2] 7 Tr.E)))
def st436 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv6, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, cv6, cv28, cv2, cv49] 8 Tr.E) [cv3, cv4, cv0, cv5, cv6, cv28, cv73] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv6, 0xffffffffffccffccff00ff00ff00ff00, cv2] 7 Tr.E) [cv3, cv4, cv0, cv5, cv17, cv68, cv2] 7 Tr.E)) [cv3, cv4, cv0, cv5, cv43, cv2, cv49] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv5, cv43, cv73] 6 Tr.E) [cv3, cv4, cv0, 0xffffaa00ff00aa00ffffaa00ff00aa00, cv6, cv2] 6 Tr.E) [cv3, cv4, cv0, cv67, cv6, cv28, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv67, 0xffffffffff00aa00ffffffffff00aa00, cv2] 6 Tr.E) [cv3, cv4, cv0, cv22, cv38, cv6, cv2] 7 Tr.E)))
def su437 : Tr := Tr.N st435 [cv3, cv4, cv0, cv5, cv6, 0xffffffffff00ff00fff0fff0ff00ff00, cv2] 7 st436
def st438 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv0, cv6, cv68, cv44, cv2] 7 Tr.E) [cv3, cv4, cv0, cv6, 0xffffffffffccffccff00ff00ff00ff00, 0xffffffffffffccccffff0000ffff0000] 6 (Tr.N Tr.E [cv3, cv4, cv0, 0xffffffffff00aa00ffffaa00ff00aa00, cv2] 5 Tr.E)) [cv3, cv4, cv0, 0xffffffffff00ff00ffffff00ff00ff00, cv44, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, 0xf8f8f8f8f0f0f0f0f8f8f8f8f0f0f0f0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xf8f8f8f8f8f8f8f8f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv70, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, 0xfcf0f0f0fcf0f0f0fcf0f0f0fcf0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xfcf0fcf0fcf0fcf0f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def st439 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, 0xfcfcf0f0fcfcf0f0f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, 0xfcfcfcfcf0f0f0f0f0f0f0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv55, cv1, cv5, cv22, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv55, cv1, cv5, cv42, cv6] 7 Tr.E) [cv3, cv4, cv55, cv1, cv5, cv27] 6 Tr.E)) [cv3, cv4, cv55, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv55, cv1, cv5, cv6, 0xffffffffffffffffcccccccccccccccc] 7 Tr.E) [cv3, cv4, cv55, cv1, cv5, cv6, cv29] 7 Tr.E) [cv3, cv4, cv55, cv1, cv5, cv66, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv55, cv1, cv22, cv27] 5 Tr.E) [cv3, cv4, cv55, cv1, cv22, cv6, cv29] 6 Tr.E)))
def su440 : Tr := Tr.N st438 [cv3, cv4, 0xfcfcf0f0f0f0f0f0fcfcf0f0f0f0f0f0, cv1, cv5, cv6, cv2] 7 st439
def su441 : Tr := Tr.N su437 [cv3, cv4, cv0, cv22, cv38, cv23, cv2] 6 su440
def su442 : Tr := Tr.N su434 [cv3, cv4, cv0, cv5, cv38, 0xffffffffffff0000ffffffffffff0000, cv2] 7 su441
def su443 : Tr := Tr.N su427 [cv3, cv4, cv0, 0xffccffccff00ff00ff00ff00ff00ff00, cv5, cv6, cv2] 7 su442
def su444 : Tr := Tr.N su412 [cv3, cv4, cv0, cv1, 0xffff00ffffff00ffffff0000ffff0000, cv6, cv2] 7 su443
def st445 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv55, cv1, cv6, cv44] 6 Tr.E) [cv3, cv4, cv55, cv71, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv3, cv4, 0xfcfcfcfcfcfcfcfcf8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv61, cv1, cv5, cv6, cv2, cv31] 8 (Tr.N (Tr.N Tr.E [cv3, cv4, cv61, cv1, cv5, cv6, cv79] 7 Tr.E) [cv3, cv4, cv1, cv56, cv5, cv6, cv2, cv19] 7 Tr.E)) [cv3, cv4, cv1, 0xfff0fff0f0f0f0f0f0f0f0f0f0f0f0f0, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, 0xfffcfffcfffcfffcf0f0f0f0f0f0f0f0, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv1, cv5, 0xfffff0f000000000fffff0f000000000, cv24, cv2] 7 Tr.E) [cv3, cv4, cv1, cv5, 0xfffff0f0f0f0f0f0f0f0f0f0f0f0f0f0, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv24, cv42, cv2] 7 Tr.E) [cv3, cv4, cv1, cv5, cv24, cv42, cv19] 6 Tr.E)))
def st446 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv42, cv6, cv57, cv2] 8 Tr.E) [cv3, cv4, cv1, cv5, cv27, cv46, cv2] 7 (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv6, 0xffffffff0f0f0f0f0f0f0f0f0f0f0f0f, cv2] 7 Tr.E)) [cv3, cv4, cv1, cv5, cv6, cv65, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv6, cv57, cv2] 8 Tr.E) [cv3, cv4, cv1, cv5, cv6, cv46, cv2] 7 Tr.E)) [cv3, cv4, cv1, cv5, cv6, cv64, cv2, cv31] 8 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv6, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0, cv2] 7 Tr.E) [cv3, cv4, cv1, cv5, cv6, 0xfffffffffff0fff0f0f0f0f0f0f0f0f0, cv2] 7 Tr.E) [cv3, cv4, cv1, cv5, cv74, cv2, cv31] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv5, cv17, cv57, cv2] 7 Tr.E) [cv3, cv4, cv1, cv22, cv24, cv42, cv2] 6 Tr.E)))
def su447 : Tr := Tr.N st445 [cv3, cv4, cv1, cv5, cv24, cv6, cv2, cv19] 7 st446
def st448 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv22, cv27, cv46, cv2] 6 Tr.E) [cv3, cv4, cv1, cv32, cv45, cv6, cv2] 6 (Tr.N Tr.E [cv3, cv4, cv1, cv16, cv24, cv6, cv2] 7 Tr.E)) [cv3, cv4, cv1, 0xffffeeeeffffeeeeffffeeeeffffeeee, cv24, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv1, cv6, cv57, cv44, cv2] 7 Tr.E) [cv3, cv4, cv1, cv17, cv57, cv44, cv2] 6 Tr.E)) [cv3, cv4, cv78, cv5, cv6, cv2, cv31] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv18, cv56, cv5, cv6, cv2] 7 Tr.E) [cv3, cv4, cv18, cv56, cv5, cv43, cv2] 6 Tr.E) [cv3, cv4, cv18, cv26, cv45, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv3, cv4, cv18, cv5, cv45, cv6, cv2] 6 Tr.E) [cv3, cv4, 0xffe0ffe0ffe0ffe0ffe0ffe0ffe0ffe0, 0xffffe0e0ffffe0e0ffffe0e0ffffe0e0, cv6, cv2] 6 Tr.E)))
def st449 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv3, cv4, cv5, cv24, cv38, cv6, cv2] 7 Tr.E) [cv3, cv4, cv5, cv24, cv38, cv23, cv2] 6 Tr.E) [cv3, cv4, cv5, cv6, cv57, cv68, cv2] 7 (Tr.N (Tr.N Tr.E [cv3, cv4, cv5, cv6, cv57, cv68, cv19] 6 Tr.E) [cv3, cv4, cv5, cv17, cv57, cv68, cv2] 6 Tr.E)) [cv3, cv4, cv16, cv24, cv38, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [0xaaaaaaffaaaaaaffaaaaaaffaaaaaaff, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xaaffaaffaaaaaaaaaaffaaffaaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [0xabababababababababababababababab, cv4, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [0xafafafafafafafafaaaaaaaaaaaaaaaa, cv4, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv53, cv4, cv48, cv0, cv1, cv5, cv6, cv2] 8 Tr.E)))
def su450 : Tr := Tr.N st448 [cv3, cv4, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, 0xffffffffff00aa00ffffffffff00aa00, cv2] 6 st449
def su451 : Tr := Tr.N su447 [cv3, cv4, cv1, cv22, cv24, cv6, cv2] 7 su450
def st452 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv59, cv4, cv51, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv59, cv4, cv1, cv5, cv33, cv46] 5 (Tr.N Tr.E [cv59, cv51, cv0, cv1, cv5, cv16, cv6, cv2] 7 Tr.E)) [cv59, cv0, cv1, cv15, cv16, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv59, cv0, cv1, cv5, cv33, cv34] 5 Tr.E) [cv59, cv0, cv1, cv21, cv16, cv6, cv2] 6 Tr.E)) [cv4, 0xd5d5d5d5d5d5d5d5d5d5d5d5d5d5d5d5, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, 0xdddddddddddddddd5555555555555555, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0, cv48, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, 0xeaaaeaaaeaaaeaaaeaaaeaaaeaaaeaaa, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, 0xeaeaaaaaeaeaaaaaeaeaaaaaeaeaaaaa, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, 0xeaeaeaeaaaaaaaaaeaeaeaeaaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 Tr.E)))
def st453 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv48, cv0, cv1, cv5, cv27, cv2] 6 Tr.E) [cv4, cv48, cv0, cv1, cv5, cv6, cv2] 8 Tr.E) [cv4, cv48, cv0, cv1, cv5, cv6, cv2, cv29] 7 (Tr.N (Tr.N Tr.E [cv4, cv48, cv0, cv1, cv5, cv6, cv79] 7 Tr.E) [cv4, cv48, cv0, cv1, cv5, cv75, cv2] 7 Tr.E)) [cv4, cv48, cv0, cv1, cv77, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv48, cv0, 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0, cv5, cv6, cv2] 7 Tr.E) [cv4, cv48, cv61, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, cv48, cv1, cv30, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv48, cv78, cv5, cv6, cv2] 6 Tr.E) [cv4, cv48, 0xffe0ffe0ffe0ffe0ffe0ffe0ffe0ffe0, cv5, cv6, cv2] 6 Tr.E)))
def su454 : Tr := Tr.N st452 [cv4, 0xeaeaeaeaeaeaeaeaaaaaaaaaaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 st453
def st455 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, 0xeeaaeeaaeeaaeeaaaaaaaaaaaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, 0xeeeeaaaaaaaaaaaaeeeeaaaaaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N Tr.E [cv4, 0xeeeeaaaaaaaaaaaaeeeeaaaaaaaaaaaa, cv0, cv1, cv16, cv6, cv2] 6 Tr.E)) [cv4, 0xeeeeaaaaeeeeaaaaaaaaaaaaaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, 0xeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, cv51, cv0, cv1, cv5, cv16, cv6, cv2] 7 Tr.E)) [cv4, cv51, cv0, cv1, cv5, cv63, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv51, cv0, cv1, cv5, cv42, cv6] 7 Tr.E) [cv4, cv51, cv0, cv1, cv5, cv27] 6 Tr.E) [cv4, cv51, cv0, cv1, cv5, cv6, cv2] 8 (Tr.N (Tr.N Tr.E [cv4, cv51, cv0, cv1, cv5, cv6, 0xffffffffffffffffcccccccccccccccc] 7 Tr.E) [cv4, cv51, cv0, cv1, cv5, cv6, cv29] 7 Tr.E)))
def st456 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv51, cv0, cv1, cv5, cv66, cv2] 7 Tr.E) [cv4, cv51, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 Tr.E) [cv4, cv51, cv0, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, 0xffffffffffffffffcccccccccccccccc] 6 (Tr.N (Tr.N Tr.E [cv4, cv51, cv0, cv1, cv16, cv6, cv29] 6 Tr.E) [cv4, cv51, cv0, cv1, cv6, cv44] 6 Tr.E)) [cv4, cv51, cv0, cv71, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv51, cv55, cv1, cv5, cv27] 5 Tr.E) [cv4, cv51, cv55, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, cv51, cv55, cv1, cv5, cv6, cv29] 6 (Tr.N (Tr.N Tr.E [cv4, cv51, cv1, cv5, cv27, cv46] 5 Tr.E) [cv4, 0xeeeeeeeeeeeeeeeeeaeaeaeaeaeaeaea, cv0, cv1, cv5, cv27] 5 Tr.E)))
def su457 : Tr := Tr.N st455 [cv4, cv51, cv0, cv1, cv5, cv6, 0xffffffffffffffffffffccccffffcccc] 6 st456
def su458 : Tr := Tr.N su454 [cv4, 0xeeaaaaaaeeaaaaaaeeaaaaaaeeaaaaaa, cv0, cv1, cv5, cv6, cv2] 7 su457
def su459 : Tr := Tr.N su451 [0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8, cv48, cv0, cv1, cv5, cv6, cv2] 7 su458
def st460 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, 0xeeeeeeeeeeeeeeeeeaeaeaeaeaeaeaea, cv0, cv1, cv5, cv6, cv29] 6 Tr.E) [cv4, cv40, cv0, cv60, cv1, cv5, cv6, cv2] 8 (Tr.N Tr.E [cv4, cv40, cv0, cv1, cv5, cv27, cv19] 6 Tr.E)) [cv4, cv40, cv0, cv1, cv5, cv6, cv2, cv19] 8 (Tr.N (Tr.N Tr.E [cv4, cv40, cv0, cv1, cv5, cv6, cv72] 7 Tr.E) [cv4, cv40, cv0, cv1, cv5, cv6, cv19, cv29] 7 Tr.E)) [cv4, cv40, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv72] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv40, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, 0xffffffff88888888ffffffff88888888, cv2] 6 Tr.E) [cv4, cv40, cv0, cv1, 0xffffaaaaffffaaaaffff0000ffff0000, cv6, cv19] 6 Tr.E) [cv4, cv40, cv0, cv1, cv6, cv44, cv19] 6 (Tr.N (Tr.N Tr.E [cv4, cv40, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, cv0, 0xfaaaaaaafaaaaaaafaaaaaaafaaaaaaa, cv1, cv5, cv6, cv2] 7 Tr.E)))
def st461 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, 0xfafafafaaaaaaaaaaaaaaaaaaaaaaaaa, cv1, cv5, cv6, cv2] 7 Tr.E) [cv4, cv0, cv41, cv1, cv15, cv5, cv6, cv2] 8 Tr.E) [cv4, cv0, cv62, cv15, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, 0xff555555ff555555ff555555ff555555, cv5, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, 0xffaa0000ffaa0000ffaa0000ffaa0000, cv15, cv6, cv2] 7 Tr.E)) [cv4, cv0, cv1, 0xffaaaaaaaaaaaaaaffaaaaaaaaaaaaaa, cv5, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, 0xffaaaaaaffaaaaaaaaaaaaaaaaaaaaaa, cv5, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv15, cv25, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv15, cv25, cv23, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv5, cv6, cv23, cv2] 7 Tr.E) [cv4, cv0, cv1, cv15, cv5, cv6, cv2] 8 Tr.E)))
def su462 : Tr := Tr.N st460 [cv4, cv0, 0xfafaaaaaaaaaaaaafafaaaaaaaaaaaaa, cv1, cv5, cv6, cv2] 7 st461
def st463 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv5, cv6, cv2, cv31] 7 Tr.E) [cv4, cv0, cv1, cv15, cv5, cv6, cv69] 7 (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv5, cv43, cv2] 7 Tr.E)) [cv4, cv0, cv1, cv15, cv16, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv16, cv6, cv69] 6 Tr.E) [cv4, cv0, cv1, cv15, cv16, cv43, cv2] 6 Tr.E)) [cv4, cv0, cv1, cv15, cv63, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv63, cv6, cv69] 6 Tr.E) [cv4, cv0, cv1, cv15, 0xffffff00ffffff00ffffff00ffffff00, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv15, cv27, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv27, cv31] 5 Tr.E) [cv4, cv0, cv1, cv15, cv6, cv2, cv29] 7 Tr.E)))
def st464 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv6, cv2, 0xfffffffffffffffffffff0f0fffff0f0] 6 Tr.E) [cv4, cv0, cv1, cv15, cv6, 0xffffffffffffffffaaaa0000aaaa0000] 6 Tr.E) [cv4, cv0, cv1, cv15, cv6, cv31, cv29] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv15, cv6, 0xffffffffffffffffffaa0000ffaa0000] 6 Tr.E) [cv4, cv0, cv1, cv15, cv6, cv39] 6 Tr.E)) [cv4, cv0, cv1, cv15, cv23, cv39] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, 0xffaaffaaaaaaaaaaaaaaaaaaaaaaaaaa, cv5, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv5, cv22, cv6, cv2] 8 Tr.E) [cv4, cv0, cv1, 0xffaaffaaffaaffaaffaaffaaffaaffaa, cv67, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv18, cv5, cv21, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv18, cv5, cv6, cv37, cv2] 7 Tr.E)))
def su465 : Tr := Tr.N st463 [cv4, cv0, cv1, cv15, cv6, cv2, 0xffffffffffffffffffffccccffffcccc] 6 st464
def su466 : Tr := Tr.N su462 [cv4, cv0, cv1, cv15, cv5, cv6, cv2, 0xffffffffffffffffcccccccccccccccc] 7 su465
def st467 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv25, cv5, cv21, cv23, cv2] 7 Tr.E) [cv4, cv0, cv1, cv25, cv5, cv37, cv2] 7 (Tr.N Tr.E [cv4, cv0, cv1, cv25, cv5, cv37, cv31] 6 Tr.E)) [cv4, cv0, cv1, cv25, cv21, cv16, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv26, cv35, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv26, cv35, cv23, cv2] 6 Tr.E)) [cv4, cv0, cv1, cv5, 0xffff555555555555ffff555555555555, cv6, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, 0xffffaaaaaaaaaaaaaaaaaaaaaaaaaaaa, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv21, cv20, cv6, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv21, cv16, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv21, cv42, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv21, cv6, cv2] 8 Tr.E)))
def st468 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv21, cv23, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv21, cv23, cv39] 6 Tr.E) [cv4, cv0, cv1, cv5, cv35, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv35, cv23, cv2] 6 Tr.E) [cv4, cv0, cv1, cv5, cv22, cv6, cv17, cv2] 8 Tr.E)) [cv4, cv0, cv1, cv5, cv22, cv17, cv23, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv16, cv6, cv37, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv42, cv6, cv37, cv2] 8 Tr.E) [cv4, cv0, cv1, cv5, cv27, cv33, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv27, cv33, cv31] 6 Tr.E) [cv4, cv0, cv1, cv5, cv6, 0xffffffff555555555555555555555555, cv2] 7 Tr.E)))
def su469 : Tr := Tr.N st467 [cv4, cv0, cv1, cv5, cv21, cv6, cv39] 7 st468
def st470 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv6, cv37, cv31] 7 Tr.E) [cv4, cv0, cv1, cv5, cv6, cv37, cv49] 7 (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv6, cv37, 0xfffffffffffffffffff0fff0fff0fff0] 6 Tr.E)) [cv4, cv0, cv1, cv5, cv6, cv33, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv6, cv17, cv2, cv19] 8 Tr.E) [cv4, cv0, cv1, cv5, cv6, cv17, cv73] 7 Tr.E)) [cv4, cv0, cv1, cv5, cv6, cv65, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv6, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, 0xffffffffa0a0a0a0ffffa0a0a0a0a0a0, cv19] 5 Tr.E) [cv4, cv0, cv1, cv5, cv74, cv2, cv19] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv74, cv19, cv49] 6 Tr.E) [cv4, cv0, cv1, cv5, cv74, cv19, cv29] 6 Tr.E)))
def st471 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 6 Tr.E) [cv4, cv0, cv1, cv5, cv37, cv64, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv37, cv64, cv49] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv37, cv28, cv2] 7 Tr.E) [cv4, cv0, cv1, cv5, cv37, cv28, cv31] 6 Tr.E)) [cv4, cv0, cv1, cv5, cv33, cv34, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv5, cv33, cv46, cv2] 6 Tr.E) [cv4, cv0, cv1, cv5, cv17, cv23, cv73] 6 Tr.E) [cv4, cv0, cv1, cv5, cv17, cv64, cv73] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv76, cv74, cv2, cv19] 6 Tr.E) [cv4, cv0, cv1, cv76, cv74, cv72] 5 Tr.E)))
def su472 : Tr := Tr.N st470 [cv4, cv0, cv1, cv5, 0xffffffffa8a8a8a8ffffa8a8a8a8a8a8, cv2] 5 st471
def su473 : Tr := Tr.N su469 [cv4, cv0, cv1, cv5, cv6, cv37, cv2] 8 su472
def su474 : Tr := Tr.N su466 [cv4, cv0, cv1, cv25, cv5, cv21, cv6, cv2] 8 su473
def su475 : Tr := Tr.N su459 [cv4, 0xeeeeeeeeeeeeeeeeeaeaeaeaeaeaeaea, cv0, cv1, cv5, cv6, cv2] 7 su474
def st476 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 5 Tr.E) [cv4, cv0, cv1, cv67, cv6, cv17, cv2] 7 (Tr.N Tr.E [cv4, cv0, cv1, cv67, cv17, cv23, cv2] 6 Tr.E)) [cv4, cv0, cv1, cv21, cv16, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv21, cv16, cv6, cv39] 6 Tr.E) [cv4, cv0, cv1, cv35, cv32, cv6, cv2] 6 Tr.E)) [cv4, cv0, cv1, cv35, cv16, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv35, cv6, 0xffffffffffffffffffff0000ff000000] 6 Tr.E) [cv4, cv0, cv1, cv35, cv23, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv4, cv0, cv1, cv22, cv16, cv6, cv17, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv16, cv6, cv33, cv2] 6 Tr.E) [cv4, cv0, cv1, cv6, cv37, cv44, cv2] 7 Tr.E)))
def st477 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv1, cv6, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xffffffffffffccccffff0000ffff0000] 6 Tr.E) [cv4, cv0, cv1, cv74, cv44, cv19] 5 Tr.E) [cv4, cv0, cv1, cv37, cv64, cv44, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv78, cv5, cv74, cv2, cv19] 6 Tr.E) [cv4, cv0, cv78, cv76, cv6, cv2, cv19] 6 Tr.E)) [cv4, cv0, cv78, cv76, cv6, cv72] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv6, cv2] 6 Tr.E) [cv4, cv0, 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv6, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 5 Tr.E) [cv4, cv0, cv15, cv18, cv25, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv15, cv18, cv5, cv6, cv2] 7 Tr.E) [cv4, cv0, cv15, cv18, cv5, cv6, cv69] 6 Tr.E)))
def su478 : Tr := Tr.N st476 [cv4, cv0, cv1, cv6, cv37, cv44, cv31] 6 st477
def st479 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv15, cv18, cv27, cv2] 5 Tr.E) [cv4, cv0, cv15, cv18, cv6, cv2, cv29] 6 (Tr.N Tr.E [cv4, cv0, cv15, cv18, cv6, cv39] 5 Tr.E)) [cv4, cv0, cv15, cv30, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv0, cv15, cv30, cv5, cv6, cv69] 6 Tr.E) [cv4, cv0, cv15, cv30, cv27, cv2] 5 Tr.E)) [cv4, cv0, cv15, cv30, cv6, cv2, cv29] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv15, cv30, cv6, cv39] 5 Tr.E) [cv4, cv0, cv18, cv26, cv35, cv6, cv2] 6 Tr.E) [cv4, cv0, cv18, cv5, cv35, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv18, cv5, cv6, cv37, cv49] 6 Tr.E) [cv4, cv0, cv18, cv5, cv37, cv28, cv2] 6 Tr.E)))
def st480 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv30, cv35, cv6, 0xffffffffffffffffffff0000ff000000] 5 Tr.E) [cv4, cv0, cv5, cv21, cv38, cv6, cv2] 7 Tr.E) [cv4, cv0, cv5, cv21, cv38, cv23, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv5, cv38, cv37, cv2] 6 Tr.E) [cv4, cv0, cv5, cv38, cv37, cv31] 5 Tr.E)) [cv4, cv0, cv5, cv6, cv37, cv68, cv2] 7 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv5, cv6, cv37, cv68, cv31] 6 Tr.E) [cv4, cv0, cv5, cv6, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xffffffffffccffccff00ff00ff00ff00] 6 Tr.E) [cv4, cv0, cv5, cv37, cv64, cv68, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv0, cv5, cv33, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 6 Tr.E) [cv4, cv0, cv5, cv33, 0xffffffffff00ff00ffffff00ff00ff00, cv31] 5 Tr.E)))
def su481 : Tr := Tr.N st479 [cv4, cv0, cv18, cv35, cv6, 0xffffffffffffffffffff0000ff000000] 5 st480
def su482 : Tr := Tr.N su478 [cv4, cv0, cv15, cv18, cv5, cv43, cv2] 6 su481
def st483 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv0, cv35, cv38, cv6, cv2] 6 Tr.E) [cv4, cv0, cv35, cv38, cv23, cv2] 5 (Tr.N Tr.E [cv4, cv0, cv35, 0xffffffccffccffccffffffccffccffcc, cv6, cv2] 5 Tr.E)) [cv4, cv54, cv1, cv5, cv6, cv17, cv73] 6 (Tr.N (Tr.N Tr.E [cv4, cv55, cv1, cv5, cv27, cv33] 5 Tr.E) [cv4, cv55, cv5, cv33, 0xffffffffff00ff00ffffff00ff00ff00] 4 Tr.E)) [cv4, cv41, cv1, cv33, cv46, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv62, cv33, cv46, cv2] 4 Tr.E) [cv4, 0xff00ff00ff00aa00ff00aa00ff00aa00, cv33, cv46, cv2] 4 Tr.E) [cv4, cv1, cv15, cv56, cv5, cv6, cv2] 7 (Tr.N (Tr.N Tr.E [cv4, cv1, cv15, cv56, cv27, cv2] 5 Tr.E) [cv4, cv1, cv15, cv56, cv6, cv2, cv29] 6 Tr.E)))
def st484 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv15, cv24, cv6, cv2] 6 Tr.E) [cv4, cv1, cv15, cv24, cv23, cv2] 5 Tr.E) [cv4, cv1, cv15, cv27, cv46, cv2] 5 (Tr.N (Tr.N Tr.E [cv4, cv1, cv30, cv5, cv6, cv37, cv31] 6 Tr.E) [cv4, cv1, cv25, cv5, cv37, cv57, cv2] 6 Tr.E)) [cv4, cv1, cv25, cv5, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv26, cv37, cv57, cv2] 5 Tr.E) [cv4, cv1, cv26, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 4 Tr.E) [cv4, cv1, cv5, cv21, cv24, cv42, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv21, cv24, cv6, cv2] 7 Tr.E) [cv4, cv1, cv5, cv21, cv24, cv65] 5 Tr.E)))
def su485 : Tr := Tr.N st483 [cv4, cv1, cv15, cv24, cv42, cv2] 5 st484
def st486 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv24, cv42, cv37, cv2] 6 Tr.E) [cv4, cv1, cv5, cv24, cv37, cv2] 6 (Tr.N Tr.E [cv4, cv1, cv5, cv24, cv17, cv2, cv19] 6 Tr.E)) [cv4, cv1, cv5, cv27, cv33, cv46, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv6, cv37, cv57, cv2] 7 Tr.E) [cv4, cv1, cv5, cv6, cv37, cv57, cv49] 6 Tr.E)) [cv4, cv1, cv5, cv6, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv37, cv57, cv28, cv2] 6 Tr.E) [cv4, cv1, cv5, cv37, cv46, cv2] 5 Tr.E) [cv4, cv1, cv5, cv33, cv46, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv33, cv46, cv19] 5 Tr.E) [cv4, cv1, cv5, cv33, cv46, cv31] 5 Tr.E)))
def st487 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv33, cv46, 0xffffffffffffffffffffaaaaaaaaaaaa] 5 Tr.E) [cv4, cv1, cv5, cv33, cv46, 0xfffffffffffffffffffff0f0f0f0f0f0] 5 Tr.E) [cv4, cv1, cv5, cv33, 0xfffffffffcfcfcfcfffff0f0f0f0f0f0] 4 (Tr.N (Tr.N Tr.E [cv4, cv1, cv5, cv17, cv46, cv19] 5 Tr.E) [cv4, cv1, cv5, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0, cv28] 5 Tr.E)) [cv4, cv1, cv5, 0xffffffffeeeeeeeeffffaaaaaaaaaaaa, cv46] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv21, cv16, cv24, cv6, cv2] 6 Tr.E) [cv4, cv1, cv35, cv45, cv42, cv2] 5 Tr.E) [cv4, cv1, cv35, cv45, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv4, cv1, cv35, cv45, cv65] 4 Tr.E) [cv4, cv1, cv35, cv45, cv23, cv2] 5 Tr.E)))
def su488 : Tr := Tr.N st486 [cv4, cv1, cv5, cv33, cv46, cv39] 5 st487
def su489 : Tr := Tr.N su485 [cv4, cv1, cv5, cv21, cv24, cv23, cv2] 6 su488
def su490 : Tr := Tr.N su482 [cv4, cv0, cv21, cv16, cv38, cv6, cv2] 6 su489
def st491 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv1, cv33, cv46, cv44, cv2] 5 Tr.E) [cv4, cv1, cv33, cv46, 0xffffffffffffaaaaffffaaaaffffaaaa, cv2] 5 (Tr.N Tr.E [cv4, cv1, cv46, 0xffffffffffaaaaaaffffaaaaffaaaaaa, cv2] 4 Tr.E)) [cv4, cv15, cv18, cv24, cv6, cv2] 5 (Tr.N (Tr.N Tr.E [cv4, cv15, cv56, cv5, cv6, cv2, cv49] 6 Tr.E) [cv4, cv15, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv5, cv6, cv2] 6 Tr.E)) [cv4, cv15, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv27, cv2] 4 (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv15, 0xfff0faf0fff0faf0fff0faf0fff0faf0, cv6, cv2, cv29] 5 Tr.E) [cv4, cv15, cv30, cv5, cv6, cv2, cv31] 6 Tr.E) [cv4, cv15, cv30, cv27, cv31] 4 (Tr.N (Tr.N Tr.E [cv4, cv15, cv30, cv6, cv31, cv29] 5 Tr.E) [cv4, cv18, cv35, cv45, cv6, cv2] 5 Tr.E)))
def st492 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv4, cv5, cv24, cv37, cv68, cv2] 5 Tr.E) [cv4, cv5, cv38, cv37, cv57, cv2] 5 Tr.E) [cv4, cv5, cv38, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa, 0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0] 4 (Tr.N (Tr.N Tr.E [cv4, cv5, cv33, cv46, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 5 Tr.E) [cv47, cv0, cv60, cv1, cv5, cv6, cv2] 7 Tr.E)) [cv47, cv0, cv1, cv5, cv27, cv19] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv47, cv0, cv1, cv5, cv6, cv2, cv19] 7 Tr.E) [cv47, cv0, cv1, cv5, cv6, cv72] 6 Tr.E) [cv47, cv0, cv1, cv5, cv6, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 6 (Tr.N (Tr.N Tr.E [cv47, cv0, cv1, cv5, cv6, cv19, cv29] 6 Tr.E) [cv47, cv0, cv1, 0xffff8888ffff8888ffff8888ffff8888, cv6, cv72] 5 Tr.E)))
def su493 : Tr := Tr.N st491 [cv4, cv30, cv5, cv37, cv28, cv31] 5 st492
def st494 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv47, cv0, cv1, cv76, cv6, cv72] 5 Tr.E) [cv47, cv0, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, cv6, 0xffffffffffffffffa8a8a8a8a8a8a8a8] 5 (Tr.N Tr.E [cv47, cv0, cv1, cv6, cv44, cv19] 5 Tr.E)) [cv47, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, cv1, cv5, cv6, cv2] 6 (Tr.N (Tr.N Tr.E [cv51, cv0, cv1, cv5, cv16, cv66, cv2] 6 Tr.E) [cv51, cv0, cv1, cv5, cv27, cv34] 5 Tr.E)) [cv51, cv0, cv71, cv5, cv16, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv51, cv55, cv1, cv5, cv16, cv6, cv2] 6 Tr.E) [cv51, cv1, cv5, cv34, cv46] 4 Tr.E) [0xeeeeeeeeeeeeeeeeeaeaeaeaeaeaeaea, cv61, cv1, cv5, cv27] 4 (Tr.N (Tr.N Tr.E [0xeeeeeeeeeeeeeeeeeaeaeaeaeaeaeaea, cv61, cv1, cv5, cv6, cv2] 6 Tr.E) [0xeeeeeeeeeeeeeeeeeaeaeaeaeaeaeaea, cv61, cv1, cv5, cv6, cv29] 5 Tr.E)))
def st495 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv25, cv5, cv21, cv14, cv2] 6 Tr.E) [cv0, cv1, cv25, cv5, cv20, cv37, cv2] 6 Tr.E) [cv0, cv1, cv25, cv5, cv37, cv14, cv2] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv26, cv35, cv14, cv2] 5 Tr.E) [cv0, cv1, cv26, cv37, cv14, cv2] 5 Tr.E)) [cv0, cv1, 0xffff0000ffff00000000000000000000, cv21, cv20, cv6, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv21, cv20, cv42, cv2] 6 Tr.E) [cv0, cv1, cv5, cv21, cv20, cv65] 5 Tr.E) [cv0, cv1, cv5, cv21, cv14, cv2] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv22, cv17, cv14, cv2] 6 Tr.E) [cv0, cv1, cv5, cv20, cv17, cv2, cv19] 6 Tr.E)))
def su496 : Tr := Tr.N st494 [0xf0f0f0f000000000f0f0f0f000000000, cv0, cv1, cv5, cv21, cv20, cv2] 6 st495
def su497 : Tr := Tr.N su493 [cv47, cv0, cv1, cv76, cv6, cv2, cv19] 6 su496
def st498 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv5, cv6, cv37, cv14, cv2] 7 Tr.E) [cv0, cv1, cv5, cv37, cv14, cv28, cv2] 6 (Tr.N Tr.E [cv0, cv1, cv5, cv33, cv65, cv34] 5 Tr.E)) [cv0, cv1, cv67, cv17, cv14, cv2] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv21, cv22, cv20, cv6, cv2] 6 Tr.E) [cv0, cv1, cv21, cv20, cv16, cv6, cv2] 6 Tr.E)) [cv0, cv1, cv21, cv20, cv6, 0xffffffffffff0000ffffffffffff0000, cv2] 6 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv21, cv32, cv6, cv2] 5 Tr.E) [cv0, cv1, cv21, cv16, cv6, cv23, cv2] 6 Tr.E) [cv0, cv1, cv21, cv16, cv66, cv2] 5 (Tr.N (Tr.N Tr.E [cv0, cv1, cv35, cv20, cv6, cv2] 5 Tr.E) [cv0, cv1, cv35, cv32, cv42, cv2] 5 Tr.E)))
def st499 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv35, cv32, cv65] 4 Tr.E) [cv0, cv1, cv35, cv32, 0xffffffffffcccccc0000000000000000] 4 Tr.E) [cv0, cv1, cv22, cv20, cv6, cv17, cv2] 6 (Tr.N (Tr.N Tr.E [cv0, cv1, cv22, cv33, cv34, cv2] 5 Tr.E) [cv0, cv1, cv22, cv17, cv34, cv2] 5 Tr.E)) [cv0, cv1, cv33, cv34, cv44, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv1, cv33, cv34, 0xffffffffffffaaaaffffaaaaffffaaaa, cv2] 5 Tr.E) [cv0, cv1, cv34, 0xffffffffffaaaaaaffffaaaaffaaaaaa, cv2] 4 Tr.E) [cv0, cv15, cv36, cv5, cv6, cv2, cv49] 6 (Tr.N (Tr.N Tr.E [cv0, cv15, 0xffcceeccffcceeccffcceeccffcceecc, cv25, cv6, cv2] 5 Tr.E) [cv0, cv15, 0xffcceeccffcceeccffcceeccffcceecc, cv5, cv6, cv2] 6 Tr.E)))
def su500 : Tr := Tr.N st498 [cv0, cv1, cv35, cv32, cv6, cv2] 6 st499
def st501 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv15, 0xffcceeccffcceeccffcceeccffcceecc, cv6, cv2, cv29] 5 Tr.E) [cv0, cv15, cv71, cv16, cv6, cv2] 5 (Tr.N Tr.E [cv0, cv36, cv21, cv38, cv6, cv2] 5 Tr.E)) [cv0, cv71, cv21, cv16, cv6, cv2] 5 (Tr.N (Tr.N Tr.E [cv0, cv18, cv35, cv32, cv6, cv2] 5 Tr.E) [cv0, cv18, cv35, cv16, cv6, cv2] 5 Tr.E)) [cv0, cv30, cv35, cv32, cv6, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv5, cv21, cv20, cv38, cv6, cv2] 6 Tr.E) [cv0, cv5, cv21, cv38, cv14, cv2] 5 Tr.E) [cv0, cv5, cv20, cv38, cv37, cv2] 5 (Tr.N (Tr.N Tr.E [cv0, cv5, cv38, cv37, cv14, cv2] 5 Tr.E) [cv0, cv5, cv38, cv14, 0xffffffffeeeeeeeeaaaaaaaaaaaaaaaa] 4 Tr.E)))
def st502 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [cv0, cv35, cv32, cv38, cv6, cv2] 5 Tr.E) [cv0, cv35, cv32, 0xffffffccffccffccffffffccffccffcc, cv6, cv2] 5 Tr.E) [cv0, cv35, 0xffffeeccffcceeccffffeeccffcceecc, cv6, cv2] 4 (Tr.N (Tr.N Tr.E [cv0, cv35, cv38, cv14, cv2] 4 Tr.E) [cv55, cv1, cv5, cv33, cv34] 4 Tr.E)) [cv1, cv5, cv21, cv24, cv14, cv2] 5 (Tr.N (Tr.N (Tr.N Tr.E [cv1, cv5, cv20, cv24, cv37, cv2] 5 Tr.E) [cv1, cv5, cv24, cv37, cv14, cv2] 5 Tr.E) [cv1, cv35, cv32, cv45, cv6, cv2] 5 (Tr.N (Tr.N Tr.E [cv1, cv35, cv45, cv14, cv2] 4 Tr.E) [0xfff0faf0fff0faf0fff0faf0fff0faf0, cv35, cv32, cv6, cv2] 4 Tr.E)))
def su503 : Tr := Tr.N st501 [cv0, cv5, cv33, cv34, 0xffffffffff00ff00ffffff00ff00ff00, cv2] 5 st502
def su504 : Tr := Tr.N su500 [cv0, cv15, 0xffcceeccffcceeccffcceeccffcceecc, cv27, cv2] 4 su503
def su505 : Tr := Tr.N su497 [cv0, cv1, cv5, cv27, cv33, cv34, cv2] 6 su504
def su506 : Tr := Tr.N su490 [cv4, cv1, cv22, cv33, cv46, cv2] 5 su505
def su507 : Tr := Tr.N su475 [cv4, cv0, cv1, 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8, 0xffffffffa8a8a8a8ffffffffa8a8a8a8, cv2] 6 su506
def su508 : Tr := Tr.N su444 [cv3, cv4, cv55, cv1, 0xffffccccffffccccffff0000ffff0000, cv6, cv2] 7 su507
def tree2 : Tr := Tr.N su381 [cv3, cv4, cv0, 0xfcfcfcfcfcfcfcfccccccccccccccccc, cv1, cv5, cv6, cv2] 8 su508

theorem allE_N (t t2 l r : Tr) (k : List ℕ) (v : ℕ) :
    allE t t2 (Tr.N l k v r) = (chkE t t2 k v && allE t t2 l && allE t t2 r) := rfl

theorem allE_E (t t2 : Tr) : allE t t2 Tr.E = true := rfl

theorem allS_N (t l r : Tr) (k : List ℕ) (v : ℕ) :
    allS t (Tr.N l k v r) = (look t (srt (k.map (pg SG))) v && allS t l && allS t r) := rfl

theorem allS_E (t : Tr) : allS t Tr.E = true := rfl

set_option maxHeartbeats 400000000 in
theorem ok_t0 : allE tree tree2 t0 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t1 : allE tree tree2 t1 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u2 : allE tree tree2 u2 = true := by
  unfold u2
  rw [allE_N, ok_t0, ok_t1, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t3 : allE tree tree2 t3 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t4 : allE tree tree2 t4 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u5 : allE tree tree2 u5 = true := by
  unfold u5
  rw [allE_N, ok_t3, ok_t4, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u6 : allE tree tree2 u6 = true := by
  unfold u6
  rw [allE_N, ok_u2, ok_u5, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t7 : allE tree tree2 t7 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t8 : allE tree tree2 t8 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u9 : allE tree tree2 u9 = true := by
  unfold u9
  rw [allE_N, ok_t7, ok_t8, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t10 : allE tree tree2 t10 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t11 : allE tree tree2 t11 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u12 : allE tree tree2 u12 = true := by
  unfold u12
  rw [allE_N, ok_t10, ok_t11, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u13 : allE tree tree2 u13 = true := by
  unfold u13
  rw [allE_N, ok_u9, ok_u12, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u14 : allE tree tree2 u14 = true := by
  unfold u14
  rw [allE_N, ok_u6, ok_u13, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t15 : allE tree tree2 t15 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t16 : allE tree tree2 t16 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u17 : allE tree tree2 u17 = true := by
  unfold u17
  rw [allE_N, ok_t15, ok_t16, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t18 : allE tree tree2 t18 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t19 : allE tree tree2 t19 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u20 : allE tree tree2 u20 = true := by
  unfold u20
  rw [allE_N, ok_t18, ok_t19, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u21 : allE tree tree2 u21 = true := by
  unfold u21
  rw [allE_N, ok_u17, ok_u20, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t22 : allE tree tree2 t22 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t23 : allE tree tree2 t23 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u24 : allE tree tree2 u24 = true := by
  unfold u24
  rw [allE_N, ok_t22, ok_t23, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t25 : allE tree tree2 t25 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t26 : allE tree tree2 t26 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u27 : allE tree tree2 u27 = true := by
  unfold u27
  rw [allE_N, ok_t25, ok_t26, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u28 : allE tree tree2 u28 = true := by
  unfold u28
  rw [allE_N, ok_u24, ok_u27, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u29 : allE tree tree2 u29 = true := by
  unfold u29
  rw [allE_N, ok_u21, ok_u28, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u30 : allE tree tree2 u30 = true := by
  unfold u30
  rw [allE_N, ok_u14, ok_u29, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t31 : allE tree tree2 t31 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t32 : allE tree tree2 t32 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u33 : allE tree tree2 u33 = true := by
  unfold u33
  rw [allE_N, ok_t31, ok_t32, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t34 : allE tree tree2 t34 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t35 : allE tree tree2 t35 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u36 : allE tree tree2 u36 = true := by
  unfold u36
  rw [allE_N, ok_t34, ok_t35, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u37 : allE tree tree2 u37 = true := by
  unfold u37
  rw [allE_N, ok_u33, ok_u36, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t38 : allE tree tree2 t38 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t39 : allE tree tree2 t39 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u40 : allE tree tree2 u40 = true := by
  unfold u40
  rw [allE_N, ok_t38, ok_t39, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t41 : allE tree tree2 t41 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t42 : allE tree tree2 t42 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u43 : allE tree tree2 u43 = true := by
  unfold u43
  rw [allE_N, ok_t41, ok_t42, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u44 : allE tree tree2 u44 = true := by
  unfold u44
  rw [allE_N, ok_u40, ok_u43, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u45 : allE tree tree2 u45 = true := by
  unfold u45
  rw [allE_N, ok_u37, ok_u44, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t46 : allE tree tree2 t46 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t47 : allE tree tree2 t47 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u48 : allE tree tree2 u48 = true := by
  unfold u48
  rw [allE_N, ok_t46, ok_t47, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t49 : allE tree tree2 t49 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t50 : allE tree tree2 t50 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u51 : allE tree tree2 u51 = true := by
  unfold u51
  rw [allE_N, ok_t49, ok_t50, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u52 : allE tree tree2 u52 = true := by
  unfold u52
  rw [allE_N, ok_u48, ok_u51, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t53 : allE tree tree2 t53 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t54 : allE tree tree2 t54 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u55 : allE tree tree2 u55 = true := by
  unfold u55
  rw [allE_N, ok_t53, ok_t54, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t56 : allE tree tree2 t56 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t57 : allE tree tree2 t57 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u58 : allE tree tree2 u58 = true := by
  unfold u58
  rw [allE_N, ok_t56, ok_t57, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u59 : allE tree tree2 u59 = true := by
  unfold u59
  rw [allE_N, ok_u55, ok_u58, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u60 : allE tree tree2 u60 = true := by
  unfold u60
  rw [allE_N, ok_u52, ok_u59, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u61 : allE tree tree2 u61 = true := by
  unfold u61
  rw [allE_N, ok_u45, ok_u60, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u62 : allE tree tree2 u62 = true := by
  unfold u62
  rw [allE_N, ok_u30, ok_u61, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t63 : allE tree tree2 t63 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t64 : allE tree tree2 t64 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u65 : allE tree tree2 u65 = true := by
  unfold u65
  rw [allE_N, ok_t63, ok_t64, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t66 : allE tree tree2 t66 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t67 : allE tree tree2 t67 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u68 : allE tree tree2 u68 = true := by
  unfold u68
  rw [allE_N, ok_t66, ok_t67, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u69 : allE tree tree2 u69 = true := by
  unfold u69
  rw [allE_N, ok_u65, ok_u68, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t70 : allE tree tree2 t70 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t71 : allE tree tree2 t71 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u72 : allE tree tree2 u72 = true := by
  unfold u72
  rw [allE_N, ok_t70, ok_t71, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t73 : allE tree tree2 t73 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t74 : allE tree tree2 t74 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u75 : allE tree tree2 u75 = true := by
  unfold u75
  rw [allE_N, ok_t73, ok_t74, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u76 : allE tree tree2 u76 = true := by
  unfold u76
  rw [allE_N, ok_u72, ok_u75, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u77 : allE tree tree2 u77 = true := by
  unfold u77
  rw [allE_N, ok_u69, ok_u76, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t78 : allE tree tree2 t78 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t79 : allE tree tree2 t79 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u80 : allE tree tree2 u80 = true := by
  unfold u80
  rw [allE_N, ok_t78, ok_t79, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t81 : allE tree tree2 t81 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t82 : allE tree tree2 t82 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u83 : allE tree tree2 u83 = true := by
  unfold u83
  rw [allE_N, ok_t81, ok_t82, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u84 : allE tree tree2 u84 = true := by
  unfold u84
  rw [allE_N, ok_u80, ok_u83, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t85 : allE tree tree2 t85 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t86 : allE tree tree2 t86 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u87 : allE tree tree2 u87 = true := by
  unfold u87
  rw [allE_N, ok_t85, ok_t86, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t88 : allE tree tree2 t88 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t89 : allE tree tree2 t89 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u90 : allE tree tree2 u90 = true := by
  unfold u90
  rw [allE_N, ok_t88, ok_t89, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u91 : allE tree tree2 u91 = true := by
  unfold u91
  rw [allE_N, ok_u87, ok_u90, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u92 : allE tree tree2 u92 = true := by
  unfold u92
  rw [allE_N, ok_u84, ok_u91, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u93 : allE tree tree2 u93 = true := by
  unfold u93
  rw [allE_N, ok_u77, ok_u92, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t94 : allE tree tree2 t94 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t95 : allE tree tree2 t95 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u96 : allE tree tree2 u96 = true := by
  unfold u96
  rw [allE_N, ok_t94, ok_t95, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t97 : allE tree tree2 t97 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t98 : allE tree tree2 t98 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u99 : allE tree tree2 u99 = true := by
  unfold u99
  rw [allE_N, ok_t97, ok_t98, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u100 : allE tree tree2 u100 = true := by
  unfold u100
  rw [allE_N, ok_u96, ok_u99, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t101 : allE tree tree2 t101 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t102 : allE tree tree2 t102 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u103 : allE tree tree2 u103 = true := by
  unfold u103
  rw [allE_N, ok_t101, ok_t102, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t104 : allE tree tree2 t104 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t105 : allE tree tree2 t105 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u106 : allE tree tree2 u106 = true := by
  unfold u106
  rw [allE_N, ok_t104, ok_t105, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u107 : allE tree tree2 u107 = true := by
  unfold u107
  rw [allE_N, ok_u103, ok_u106, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u108 : allE tree tree2 u108 = true := by
  unfold u108
  rw [allE_N, ok_u100, ok_u107, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t109 : allE tree tree2 t109 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t110 : allE tree tree2 t110 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u111 : allE tree tree2 u111 = true := by
  unfold u111
  rw [allE_N, ok_t109, ok_t110, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t112 : allE tree tree2 t112 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t113 : allE tree tree2 t113 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u114 : allE tree tree2 u114 = true := by
  unfold u114
  rw [allE_N, ok_t112, ok_t113, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u115 : allE tree tree2 u115 = true := by
  unfold u115
  rw [allE_N, ok_u111, ok_u114, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t116 : allE tree tree2 t116 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t117 : allE tree tree2 t117 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u118 : allE tree tree2 u118 = true := by
  unfold u118
  rw [allE_N, ok_t116, ok_t117, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t119 : allE tree tree2 t119 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t120 : allE tree tree2 t120 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u121 : allE tree tree2 u121 = true := by
  unfold u121
  rw [allE_N, ok_t119, ok_t120, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u122 : allE tree tree2 u122 = true := by
  unfold u122
  rw [allE_N, ok_u118, ok_u121, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u123 : allE tree tree2 u123 = true := by
  unfold u123
  rw [allE_N, ok_u115, ok_u122, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u124 : allE tree tree2 u124 = true := by
  unfold u124
  rw [allE_N, ok_u108, ok_u123, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u125 : allE tree tree2 u125 = true := by
  unfold u125
  rw [allE_N, ok_u93, ok_u124, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u126 : allE tree tree2 u126 = true := by
  unfold u126
  rw [allE_N, ok_u62, ok_u125, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t127 : allE tree tree2 t127 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t128 : allE tree tree2 t128 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u129 : allE tree tree2 u129 = true := by
  unfold u129
  rw [allE_N, ok_t127, ok_t128, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t130 : allE tree tree2 t130 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t131 : allE tree tree2 t131 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u132 : allE tree tree2 u132 = true := by
  unfold u132
  rw [allE_N, ok_t130, ok_t131, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u133 : allE tree tree2 u133 = true := by
  unfold u133
  rw [allE_N, ok_u129, ok_u132, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t134 : allE tree tree2 t134 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t135 : allE tree tree2 t135 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u136 : allE tree tree2 u136 = true := by
  unfold u136
  rw [allE_N, ok_t134, ok_t135, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t137 : allE tree tree2 t137 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t138 : allE tree tree2 t138 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u139 : allE tree tree2 u139 = true := by
  unfold u139
  rw [allE_N, ok_t137, ok_t138, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u140 : allE tree tree2 u140 = true := by
  unfold u140
  rw [allE_N, ok_u136, ok_u139, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u141 : allE tree tree2 u141 = true := by
  unfold u141
  rw [allE_N, ok_u133, ok_u140, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t142 : allE tree tree2 t142 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t143 : allE tree tree2 t143 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u144 : allE tree tree2 u144 = true := by
  unfold u144
  rw [allE_N, ok_t142, ok_t143, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t145 : allE tree tree2 t145 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t146 : allE tree tree2 t146 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u147 : allE tree tree2 u147 = true := by
  unfold u147
  rw [allE_N, ok_t145, ok_t146, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u148 : allE tree tree2 u148 = true := by
  unfold u148
  rw [allE_N, ok_u144, ok_u147, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t149 : allE tree tree2 t149 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t150 : allE tree tree2 t150 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u151 : allE tree tree2 u151 = true := by
  unfold u151
  rw [allE_N, ok_t149, ok_t150, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t152 : allE tree tree2 t152 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t153 : allE tree tree2 t153 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u154 : allE tree tree2 u154 = true := by
  unfold u154
  rw [allE_N, ok_t152, ok_t153, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u155 : allE tree tree2 u155 = true := by
  unfold u155
  rw [allE_N, ok_u151, ok_u154, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u156 : allE tree tree2 u156 = true := by
  unfold u156
  rw [allE_N, ok_u148, ok_u155, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u157 : allE tree tree2 u157 = true := by
  unfold u157
  rw [allE_N, ok_u141, ok_u156, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t158 : allE tree tree2 t158 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t159 : allE tree tree2 t159 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u160 : allE tree tree2 u160 = true := by
  unfold u160
  rw [allE_N, ok_t158, ok_t159, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t161 : allE tree tree2 t161 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t162 : allE tree tree2 t162 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u163 : allE tree tree2 u163 = true := by
  unfold u163
  rw [allE_N, ok_t161, ok_t162, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u164 : allE tree tree2 u164 = true := by
  unfold u164
  rw [allE_N, ok_u160, ok_u163, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t165 : allE tree tree2 t165 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t166 : allE tree tree2 t166 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u167 : allE tree tree2 u167 = true := by
  unfold u167
  rw [allE_N, ok_t165, ok_t166, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t168 : allE tree tree2 t168 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t169 : allE tree tree2 t169 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u170 : allE tree tree2 u170 = true := by
  unfold u170
  rw [allE_N, ok_t168, ok_t169, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u171 : allE tree tree2 u171 = true := by
  unfold u171
  rw [allE_N, ok_u167, ok_u170, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u172 : allE tree tree2 u172 = true := by
  unfold u172
  rw [allE_N, ok_u164, ok_u171, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t173 : allE tree tree2 t173 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t174 : allE tree tree2 t174 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u175 : allE tree tree2 u175 = true := by
  unfold u175
  rw [allE_N, ok_t173, ok_t174, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t176 : allE tree tree2 t176 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t177 : allE tree tree2 t177 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u178 : allE tree tree2 u178 = true := by
  unfold u178
  rw [allE_N, ok_t176, ok_t177, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u179 : allE tree tree2 u179 = true := by
  unfold u179
  rw [allE_N, ok_u175, ok_u178, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t180 : allE tree tree2 t180 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t181 : allE tree tree2 t181 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u182 : allE tree tree2 u182 = true := by
  unfold u182
  rw [allE_N, ok_t180, ok_t181, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t183 : allE tree tree2 t183 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t184 : allE tree tree2 t184 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u185 : allE tree tree2 u185 = true := by
  unfold u185
  rw [allE_N, ok_t183, ok_t184, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u186 : allE tree tree2 u186 = true := by
  unfold u186
  rw [allE_N, ok_u182, ok_u185, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u187 : allE tree tree2 u187 = true := by
  unfold u187
  rw [allE_N, ok_u179, ok_u186, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u188 : allE tree tree2 u188 = true := by
  unfold u188
  rw [allE_N, ok_u172, ok_u187, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u189 : allE tree tree2 u189 = true := by
  unfold u189
  rw [allE_N, ok_u157, ok_u188, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t190 : allE tree tree2 t190 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t191 : allE tree tree2 t191 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u192 : allE tree tree2 u192 = true := by
  unfold u192
  rw [allE_N, ok_t190, ok_t191, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t193 : allE tree tree2 t193 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t194 : allE tree tree2 t194 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u195 : allE tree tree2 u195 = true := by
  unfold u195
  rw [allE_N, ok_t193, ok_t194, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u196 : allE tree tree2 u196 = true := by
  unfold u196
  rw [allE_N, ok_u192, ok_u195, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t197 : allE tree tree2 t197 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t198 : allE tree tree2 t198 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u199 : allE tree tree2 u199 = true := by
  unfold u199
  rw [allE_N, ok_t197, ok_t198, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t200 : allE tree tree2 t200 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t201 : allE tree tree2 t201 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u202 : allE tree tree2 u202 = true := by
  unfold u202
  rw [allE_N, ok_t200, ok_t201, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u203 : allE tree tree2 u203 = true := by
  unfold u203
  rw [allE_N, ok_u199, ok_u202, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u204 : allE tree tree2 u204 = true := by
  unfold u204
  rw [allE_N, ok_u196, ok_u203, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t205 : allE tree tree2 t205 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t206 : allE tree tree2 t206 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u207 : allE tree tree2 u207 = true := by
  unfold u207
  rw [allE_N, ok_t205, ok_t206, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t208 : allE tree tree2 t208 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t209 : allE tree tree2 t209 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u210 : allE tree tree2 u210 = true := by
  unfold u210
  rw [allE_N, ok_t208, ok_t209, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u211 : allE tree tree2 u211 = true := by
  unfold u211
  rw [allE_N, ok_u207, ok_u210, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t212 : allE tree tree2 t212 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t213 : allE tree tree2 t213 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u214 : allE tree tree2 u214 = true := by
  unfold u214
  rw [allE_N, ok_t212, ok_t213, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t215 : allE tree tree2 t215 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t216 : allE tree tree2 t216 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u217 : allE tree tree2 u217 = true := by
  unfold u217
  rw [allE_N, ok_t215, ok_t216, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u218 : allE tree tree2 u218 = true := by
  unfold u218
  rw [allE_N, ok_u214, ok_u217, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u219 : allE tree tree2 u219 = true := by
  unfold u219
  rw [allE_N, ok_u211, ok_u218, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u220 : allE tree tree2 u220 = true := by
  unfold u220
  rw [allE_N, ok_u204, ok_u219, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t221 : allE tree tree2 t221 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t222 : allE tree tree2 t222 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u223 : allE tree tree2 u223 = true := by
  unfold u223
  rw [allE_N, ok_t221, ok_t222, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t224 : allE tree tree2 t224 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t225 : allE tree tree2 t225 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u226 : allE tree tree2 u226 = true := by
  unfold u226
  rw [allE_N, ok_t224, ok_t225, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u227 : allE tree tree2 u227 = true := by
  unfold u227
  rw [allE_N, ok_u223, ok_u226, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t228 : allE tree tree2 t228 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t229 : allE tree tree2 t229 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u230 : allE tree tree2 u230 = true := by
  unfold u230
  rw [allE_N, ok_t228, ok_t229, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t231 : allE tree tree2 t231 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t232 : allE tree tree2 t232 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u233 : allE tree tree2 u233 = true := by
  unfold u233
  rw [allE_N, ok_t231, ok_t232, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u234 : allE tree tree2 u234 = true := by
  unfold u234
  rw [allE_N, ok_u230, ok_u233, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u235 : allE tree tree2 u235 = true := by
  unfold u235
  rw [allE_N, ok_u227, ok_u234, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t236 : allE tree tree2 t236 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t237 : allE tree tree2 t237 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u238 : allE tree tree2 u238 = true := by
  unfold u238
  rw [allE_N, ok_t236, ok_t237, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t239 : allE tree tree2 t239 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t240 : allE tree tree2 t240 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u241 : allE tree tree2 u241 = true := by
  unfold u241
  rw [allE_N, ok_t239, ok_t240, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u242 : allE tree tree2 u242 = true := by
  unfold u242
  rw [allE_N, ok_u238, ok_u241, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t243 : allE tree tree2 t243 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t244 : allE tree tree2 t244 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u245 : allE tree tree2 u245 = true := by
  unfold u245
  rw [allE_N, ok_t243, ok_t244, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t246 : allE tree tree2 t246 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t247 : allE tree tree2 t247 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u248 : allE tree tree2 u248 = true := by
  unfold u248
  rw [allE_N, ok_t246, ok_t247, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u249 : allE tree tree2 u249 = true := by
  unfold u249
  rw [allE_N, ok_u245, ok_u248, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u250 : allE tree tree2 u250 = true := by
  unfold u250
  rw [allE_N, ok_u242, ok_u249, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u251 : allE tree tree2 u251 = true := by
  unfold u251
  rw [allE_N, ok_u235, ok_u250, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u252 : allE tree tree2 u252 = true := by
  unfold u252
  rw [allE_N, ok_u220, ok_u251, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u253 : allE tree tree2 u253 = true := by
  unfold u253
  rw [allE_N, ok_u189, ok_u252, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_tree : allE tree tree2 tree = true := by
  have h : allE tree tree2 (Tr.N u126 [cv3, cv4, cv0, cv0, cv1, cv5, cv6, cv2] 9 u253) = true := by
    rw [allE_N, ok_u126, ok_u253, Bool.and_true, Bool.and_true]
    decide +kernel
  exact h

set_option maxHeartbeats 400000000 in
theorem ok_st255 : allS tree st255 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st256 : allS tree st256 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su257 : allS tree su257 = true := by
  unfold su257
  rw [allS_N, ok_st255, ok_st256, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st258 : allS tree st258 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st259 : allS tree st259 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su260 : allS tree su260 = true := by
  unfold su260
  rw [allS_N, ok_st258, ok_st259, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su261 : allS tree su261 = true := by
  unfold su261
  rw [allS_N, ok_su257, ok_su260, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st262 : allS tree st262 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st263 : allS tree st263 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su264 : allS tree su264 = true := by
  unfold su264
  rw [allS_N, ok_st262, ok_st263, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st265 : allS tree st265 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st266 : allS tree st266 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su267 : allS tree su267 = true := by
  unfold su267
  rw [allS_N, ok_st265, ok_st266, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su268 : allS tree su268 = true := by
  unfold su268
  rw [allS_N, ok_su264, ok_su267, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su269 : allS tree su269 = true := by
  unfold su269
  rw [allS_N, ok_su261, ok_su268, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st270 : allS tree st270 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st271 : allS tree st271 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su272 : allS tree su272 = true := by
  unfold su272
  rw [allS_N, ok_st270, ok_st271, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st273 : allS tree st273 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st274 : allS tree st274 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su275 : allS tree su275 = true := by
  unfold su275
  rw [allS_N, ok_st273, ok_st274, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su276 : allS tree su276 = true := by
  unfold su276
  rw [allS_N, ok_su272, ok_su275, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st277 : allS tree st277 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st278 : allS tree st278 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su279 : allS tree su279 = true := by
  unfold su279
  rw [allS_N, ok_st277, ok_st278, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st280 : allS tree st280 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st281 : allS tree st281 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su282 : allS tree su282 = true := by
  unfold su282
  rw [allS_N, ok_st280, ok_st281, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su283 : allS tree su283 = true := by
  unfold su283
  rw [allS_N, ok_su279, ok_su282, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su284 : allS tree su284 = true := by
  unfold su284
  rw [allS_N, ok_su276, ok_su283, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su285 : allS tree su285 = true := by
  unfold su285
  rw [allS_N, ok_su269, ok_su284, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st286 : allS tree st286 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st287 : allS tree st287 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su288 : allS tree su288 = true := by
  unfold su288
  rw [allS_N, ok_st286, ok_st287, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st289 : allS tree st289 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st290 : allS tree st290 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su291 : allS tree su291 = true := by
  unfold su291
  rw [allS_N, ok_st289, ok_st290, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su292 : allS tree su292 = true := by
  unfold su292
  rw [allS_N, ok_su288, ok_su291, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st293 : allS tree st293 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st294 : allS tree st294 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su295 : allS tree su295 = true := by
  unfold su295
  rw [allS_N, ok_st293, ok_st294, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st296 : allS tree st296 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st297 : allS tree st297 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su298 : allS tree su298 = true := by
  unfold su298
  rw [allS_N, ok_st296, ok_st297, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su299 : allS tree su299 = true := by
  unfold su299
  rw [allS_N, ok_su295, ok_su298, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su300 : allS tree su300 = true := by
  unfold su300
  rw [allS_N, ok_su292, ok_su299, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st301 : allS tree st301 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st302 : allS tree st302 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su303 : allS tree su303 = true := by
  unfold su303
  rw [allS_N, ok_st301, ok_st302, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st304 : allS tree st304 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st305 : allS tree st305 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su306 : allS tree su306 = true := by
  unfold su306
  rw [allS_N, ok_st304, ok_st305, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su307 : allS tree su307 = true := by
  unfold su307
  rw [allS_N, ok_su303, ok_su306, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st308 : allS tree st308 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st309 : allS tree st309 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su310 : allS tree su310 = true := by
  unfold su310
  rw [allS_N, ok_st308, ok_st309, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st311 : allS tree st311 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st312 : allS tree st312 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su313 : allS tree su313 = true := by
  unfold su313
  rw [allS_N, ok_st311, ok_st312, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su314 : allS tree su314 = true := by
  unfold su314
  rw [allS_N, ok_su310, ok_su313, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su315 : allS tree su315 = true := by
  unfold su315
  rw [allS_N, ok_su307, ok_su314, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su316 : allS tree su316 = true := by
  unfold su316
  rw [allS_N, ok_su300, ok_su315, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su317 : allS tree su317 = true := by
  unfold su317
  rw [allS_N, ok_su285, ok_su316, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st318 : allS tree st318 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st319 : allS tree st319 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su320 : allS tree su320 = true := by
  unfold su320
  rw [allS_N, ok_st318, ok_st319, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st321 : allS tree st321 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st322 : allS tree st322 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su323 : allS tree su323 = true := by
  unfold su323
  rw [allS_N, ok_st321, ok_st322, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su324 : allS tree su324 = true := by
  unfold su324
  rw [allS_N, ok_su320, ok_su323, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st325 : allS tree st325 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st326 : allS tree st326 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su327 : allS tree su327 = true := by
  unfold su327
  rw [allS_N, ok_st325, ok_st326, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st328 : allS tree st328 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st329 : allS tree st329 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su330 : allS tree su330 = true := by
  unfold su330
  rw [allS_N, ok_st328, ok_st329, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su331 : allS tree su331 = true := by
  unfold su331
  rw [allS_N, ok_su327, ok_su330, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su332 : allS tree su332 = true := by
  unfold su332
  rw [allS_N, ok_su324, ok_su331, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st333 : allS tree st333 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st334 : allS tree st334 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su335 : allS tree su335 = true := by
  unfold su335
  rw [allS_N, ok_st333, ok_st334, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st336 : allS tree st336 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st337 : allS tree st337 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su338 : allS tree su338 = true := by
  unfold su338
  rw [allS_N, ok_st336, ok_st337, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su339 : allS tree su339 = true := by
  unfold su339
  rw [allS_N, ok_su335, ok_su338, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st340 : allS tree st340 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st341 : allS tree st341 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su342 : allS tree su342 = true := by
  unfold su342
  rw [allS_N, ok_st340, ok_st341, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st343 : allS tree st343 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st344 : allS tree st344 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su345 : allS tree su345 = true := by
  unfold su345
  rw [allS_N, ok_st343, ok_st344, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su346 : allS tree su346 = true := by
  unfold su346
  rw [allS_N, ok_su342, ok_su345, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su347 : allS tree su347 = true := by
  unfold su347
  rw [allS_N, ok_su339, ok_su346, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su348 : allS tree su348 = true := by
  unfold su348
  rw [allS_N, ok_su332, ok_su347, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st349 : allS tree st349 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st350 : allS tree st350 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su351 : allS tree su351 = true := by
  unfold su351
  rw [allS_N, ok_st349, ok_st350, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st352 : allS tree st352 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st353 : allS tree st353 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su354 : allS tree su354 = true := by
  unfold su354
  rw [allS_N, ok_st352, ok_st353, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su355 : allS tree su355 = true := by
  unfold su355
  rw [allS_N, ok_su351, ok_su354, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st356 : allS tree st356 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st357 : allS tree st357 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su358 : allS tree su358 = true := by
  unfold su358
  rw [allS_N, ok_st356, ok_st357, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st359 : allS tree st359 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st360 : allS tree st360 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su361 : allS tree su361 = true := by
  unfold su361
  rw [allS_N, ok_st359, ok_st360, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su362 : allS tree su362 = true := by
  unfold su362
  rw [allS_N, ok_su358, ok_su361, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su363 : allS tree su363 = true := by
  unfold su363
  rw [allS_N, ok_su355, ok_su362, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st364 : allS tree st364 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st365 : allS tree st365 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su366 : allS tree su366 = true := by
  unfold su366
  rw [allS_N, ok_st364, ok_st365, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st367 : allS tree st367 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st368 : allS tree st368 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su369 : allS tree su369 = true := by
  unfold su369
  rw [allS_N, ok_st367, ok_st368, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su370 : allS tree su370 = true := by
  unfold su370
  rw [allS_N, ok_su366, ok_su369, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st371 : allS tree st371 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st372 : allS tree st372 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su373 : allS tree su373 = true := by
  unfold su373
  rw [allS_N, ok_st371, ok_st372, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st374 : allS tree st374 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st375 : allS tree st375 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su376 : allS tree su376 = true := by
  unfold su376
  rw [allS_N, ok_st374, ok_st375, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su377 : allS tree su377 = true := by
  unfold su377
  rw [allS_N, ok_su373, ok_su376, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su378 : allS tree su378 = true := by
  unfold su378
  rw [allS_N, ok_su370, ok_su377, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su379 : allS tree su379 = true := by
  unfold su379
  rw [allS_N, ok_su363, ok_su378, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su380 : allS tree su380 = true := by
  unfold su380
  rw [allS_N, ok_su348, ok_su379, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su381 : allS tree su381 = true := by
  unfold su381
  rw [allS_N, ok_su317, ok_su380, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st382 : allS tree st382 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st383 : allS tree st383 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su384 : allS tree su384 = true := by
  unfold su384
  rw [allS_N, ok_st382, ok_st383, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st385 : allS tree st385 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st386 : allS tree st386 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su387 : allS tree su387 = true := by
  unfold su387
  rw [allS_N, ok_st385, ok_st386, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su388 : allS tree su388 = true := by
  unfold su388
  rw [allS_N, ok_su384, ok_su387, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st389 : allS tree st389 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st390 : allS tree st390 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su391 : allS tree su391 = true := by
  unfold su391
  rw [allS_N, ok_st389, ok_st390, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st392 : allS tree st392 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st393 : allS tree st393 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su394 : allS tree su394 = true := by
  unfold su394
  rw [allS_N, ok_st392, ok_st393, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su395 : allS tree su395 = true := by
  unfold su395
  rw [allS_N, ok_su391, ok_su394, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su396 : allS tree su396 = true := by
  unfold su396
  rw [allS_N, ok_su388, ok_su395, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st397 : allS tree st397 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st398 : allS tree st398 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su399 : allS tree su399 = true := by
  unfold su399
  rw [allS_N, ok_st397, ok_st398, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st400 : allS tree st400 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st401 : allS tree st401 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su402 : allS tree su402 = true := by
  unfold su402
  rw [allS_N, ok_st400, ok_st401, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su403 : allS tree su403 = true := by
  unfold su403
  rw [allS_N, ok_su399, ok_su402, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st404 : allS tree st404 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st405 : allS tree st405 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su406 : allS tree su406 = true := by
  unfold su406
  rw [allS_N, ok_st404, ok_st405, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st407 : allS tree st407 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st408 : allS tree st408 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su409 : allS tree su409 = true := by
  unfold su409
  rw [allS_N, ok_st407, ok_st408, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su410 : allS tree su410 = true := by
  unfold su410
  rw [allS_N, ok_su406, ok_su409, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su411 : allS tree su411 = true := by
  unfold su411
  rw [allS_N, ok_su403, ok_su410, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su412 : allS tree su412 = true := by
  unfold su412
  rw [allS_N, ok_su396, ok_su411, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st413 : allS tree st413 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st414 : allS tree st414 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su415 : allS tree su415 = true := by
  unfold su415
  rw [allS_N, ok_st413, ok_st414, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st416 : allS tree st416 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st417 : allS tree st417 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su418 : allS tree su418 = true := by
  unfold su418
  rw [allS_N, ok_st416, ok_st417, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su419 : allS tree su419 = true := by
  unfold su419
  rw [allS_N, ok_su415, ok_su418, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st420 : allS tree st420 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st421 : allS tree st421 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su422 : allS tree su422 = true := by
  unfold su422
  rw [allS_N, ok_st420, ok_st421, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st423 : allS tree st423 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st424 : allS tree st424 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su425 : allS tree su425 = true := by
  unfold su425
  rw [allS_N, ok_st423, ok_st424, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su426 : allS tree su426 = true := by
  unfold su426
  rw [allS_N, ok_su422, ok_su425, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su427 : allS tree su427 = true := by
  unfold su427
  rw [allS_N, ok_su419, ok_su426, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st428 : allS tree st428 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st429 : allS tree st429 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su430 : allS tree su430 = true := by
  unfold su430
  rw [allS_N, ok_st428, ok_st429, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st431 : allS tree st431 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st432 : allS tree st432 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su433 : allS tree su433 = true := by
  unfold su433
  rw [allS_N, ok_st431, ok_st432, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su434 : allS tree su434 = true := by
  unfold su434
  rw [allS_N, ok_su430, ok_su433, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st435 : allS tree st435 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st436 : allS tree st436 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su437 : allS tree su437 = true := by
  unfold su437
  rw [allS_N, ok_st435, ok_st436, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st438 : allS tree st438 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st439 : allS tree st439 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su440 : allS tree su440 = true := by
  unfold su440
  rw [allS_N, ok_st438, ok_st439, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su441 : allS tree su441 = true := by
  unfold su441
  rw [allS_N, ok_su437, ok_su440, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su442 : allS tree su442 = true := by
  unfold su442
  rw [allS_N, ok_su434, ok_su441, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su443 : allS tree su443 = true := by
  unfold su443
  rw [allS_N, ok_su427, ok_su442, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su444 : allS tree su444 = true := by
  unfold su444
  rw [allS_N, ok_su412, ok_su443, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st445 : allS tree st445 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st446 : allS tree st446 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su447 : allS tree su447 = true := by
  unfold su447
  rw [allS_N, ok_st445, ok_st446, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st448 : allS tree st448 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st449 : allS tree st449 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su450 : allS tree su450 = true := by
  unfold su450
  rw [allS_N, ok_st448, ok_st449, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su451 : allS tree su451 = true := by
  unfold su451
  rw [allS_N, ok_su447, ok_su450, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st452 : allS tree st452 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st453 : allS tree st453 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su454 : allS tree su454 = true := by
  unfold su454
  rw [allS_N, ok_st452, ok_st453, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st455 : allS tree st455 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st456 : allS tree st456 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su457 : allS tree su457 = true := by
  unfold su457
  rw [allS_N, ok_st455, ok_st456, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su458 : allS tree su458 = true := by
  unfold su458
  rw [allS_N, ok_su454, ok_su457, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su459 : allS tree su459 = true := by
  unfold su459
  rw [allS_N, ok_su451, ok_su458, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st460 : allS tree st460 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st461 : allS tree st461 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su462 : allS tree su462 = true := by
  unfold su462
  rw [allS_N, ok_st460, ok_st461, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st463 : allS tree st463 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st464 : allS tree st464 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su465 : allS tree su465 = true := by
  unfold su465
  rw [allS_N, ok_st463, ok_st464, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su466 : allS tree su466 = true := by
  unfold su466
  rw [allS_N, ok_su462, ok_su465, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st467 : allS tree st467 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st468 : allS tree st468 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su469 : allS tree su469 = true := by
  unfold su469
  rw [allS_N, ok_st467, ok_st468, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st470 : allS tree st470 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st471 : allS tree st471 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su472 : allS tree su472 = true := by
  unfold su472
  rw [allS_N, ok_st470, ok_st471, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su473 : allS tree su473 = true := by
  unfold su473
  rw [allS_N, ok_su469, ok_su472, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su474 : allS tree su474 = true := by
  unfold su474
  rw [allS_N, ok_su466, ok_su473, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su475 : allS tree su475 = true := by
  unfold su475
  rw [allS_N, ok_su459, ok_su474, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st476 : allS tree st476 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st477 : allS tree st477 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su478 : allS tree su478 = true := by
  unfold su478
  rw [allS_N, ok_st476, ok_st477, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st479 : allS tree st479 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st480 : allS tree st480 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su481 : allS tree su481 = true := by
  unfold su481
  rw [allS_N, ok_st479, ok_st480, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su482 : allS tree su482 = true := by
  unfold su482
  rw [allS_N, ok_su478, ok_su481, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st483 : allS tree st483 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st484 : allS tree st484 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su485 : allS tree su485 = true := by
  unfold su485
  rw [allS_N, ok_st483, ok_st484, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st486 : allS tree st486 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st487 : allS tree st487 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su488 : allS tree su488 = true := by
  unfold su488
  rw [allS_N, ok_st486, ok_st487, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su489 : allS tree su489 = true := by
  unfold su489
  rw [allS_N, ok_su485, ok_su488, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su490 : allS tree su490 = true := by
  unfold su490
  rw [allS_N, ok_su482, ok_su489, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st491 : allS tree st491 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st492 : allS tree st492 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su493 : allS tree su493 = true := by
  unfold su493
  rw [allS_N, ok_st491, ok_st492, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st494 : allS tree st494 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st495 : allS tree st495 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su496 : allS tree su496 = true := by
  unfold su496
  rw [allS_N, ok_st494, ok_st495, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su497 : allS tree su497 = true := by
  unfold su497
  rw [allS_N, ok_su493, ok_su496, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st498 : allS tree st498 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st499 : allS tree st499 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su500 : allS tree su500 = true := by
  unfold su500
  rw [allS_N, ok_st498, ok_st499, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st501 : allS tree st501 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_st502 : allS tree st502 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su503 : allS tree su503 = true := by
  unfold su503
  rw [allS_N, ok_st501, ok_st502, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su504 : allS tree su504 = true := by
  unfold su504
  rw [allS_N, ok_su500, ok_su503, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su505 : allS tree su505 = true := by
  unfold su505
  rw [allS_N, ok_su497, ok_su504, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su506 : allS tree su506 = true := by
  unfold su506
  rw [allS_N, ok_su490, ok_su505, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su507 : allS tree su507 = true := by
  unfold su507
  rw [allS_N, ok_su475, ok_su506, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_su508 : allS tree su508 = true := by
  unfold su508
  rw [allS_N, ok_su444, ok_su507, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_tree2 : allS tree tree2 = true := by
  have h : allS tree (Tr.N su381 [cv3, cv4, cv0, 0xfcfcfcfcfcfcfcfccccccccccccccccc, cv1, cv5, cv6, cv2] 8 su508) = true := by
    rw [allS_N, ok_su381, ok_su508, Bool.and_true, Bool.and_true]
    decide +kernel
  exact h


set_option maxHeartbeats 400000000 in
theorem top_ok : ∀ L ∈ XX.sublists, passes 10 L = true → lookS tree tree2 10 L = true := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem TT_eq : encL fE pts = TT := by decide +kernel

set_option maxHeartbeats 40000000 in
theorem AA_eq' : encL (fun _ => true) pts = AA := by decide +kernel

set_option maxHeartbeats 40000000 in
theorem XX_eq : (List.range 7).map (Xv pts) = XX := by decide +kernel

theorem Run.mono_le {s s' : ℕ} {L : List ℕ} (hs : s ≤ s') (h : Run TT AA s L) : Run TT AA s' L := by
  induction hs with
  | refl => exact h
  | step _ ih => exact Run.mono ih

theorem main : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hF, hsize, hf⟩
  have hsz : C.gates.length ≤ 10 := hsize
  have hf' : ∀ x, C.eval (List.ofFn x) = fE x := fun x =>
    Bool.eq_iff_iff.2 ((hf x).trans decide_eq_true_iff.symm)
  have hx0 : fE (fun i => decide (i.val = 0 ∨ i.val = 1)) = true := by decide
  obtain ⟨S, hsub, hrun⟩ := reduce pts fE _ hx0 C hF hf'
  rw [TT_eq, AA_eq'] at hrun
  rw [XX_eq] at hsub
  have hr10 : Run TT AA 10 S := Run.mono_le hsz hrun
  have hl := top_ok S (List.mem_sublists.2 hsub) (hr10.passOk (le_refl 10))
  obtain ⟨g, hg, v, hm, hv⟩ := lookS_sound ok_tree2 hl
  exact cert tree tree2 ok_tree ok_tree2 hr10 g hg v hm hv

end PEqualNP.Outside.L_meta_595

theorem PEqualNP.Outside.L_meta_595 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  PEqualNP.Outside.L_meta_595.main
