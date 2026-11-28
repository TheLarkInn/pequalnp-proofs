import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_6158

namespace PEqualNP.Outside.L_meta_27804.Lower.Strip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

theorem mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

theorem st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

theorem st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

theorem st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

theorem st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

theorem st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

theorem st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

theorem st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

theorem st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
theorem gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
theorem st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

theorem take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in

theorem st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]

          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia

            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

theorem live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in

theorem kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          ·
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in

theorem kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill

theorem induced : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K hR hK ⟨u0, hu0, v0, hv0, h0⟩ ⟨⟨gs, o⟩, hC, hs, hrep⟩
  let BL := R.filter fun a => ∃ b ∈ K, A a b = true
  let BR := K.filter fun b => ∃ a ∈ R, A a b = true
  let Z : Finset ℕ := (Finset.univ.filter fun a : Fin n => a ∉ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (Finset.univ.filter fun b : Fin m => b ∉ BR).image (fun b : Fin m => n + (b : ℕ))
  have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hC
  have hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hZl : ∀ a : Fin n, (a : ℕ) ∈ Z ↔ a ∉ BL := by
    intro a
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, _, e⟩)
      · rwa [← Fin.ext e]
      · have := a.2; omega
    · exact fun h => Or.inl ⟨a, h, rfl⟩
  have hZr : ∀ b : Fin m, n + (b : ℕ) ∈ Z ↔ b ∉ BR := by
    intro b
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, _, e⟩ | ⟨x, hx, e⟩)
      · have := x.2; omega
      · rwa [← Fin.ext (show (x : ℕ) = b by omega)]
    · exact fun h => Or.inr ⟨b, h, rfl⟩
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = true →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono gs hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hrep u v
  have hoff : ∀ P w, ¬ Live (n + m) gs o w →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = Circuit.eval ⟨gs, o⟩ (inp (n + m) (P.erase w)) := by
    intro P w hw
    have := live_dep (n + m) gs o (inp (n + m) P) (inp (n + m) (P.erase w)) (by simp [inp])
      (by simp [inp]) (fun i hi => by
        rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
        have : i ≠ w := fun e => hw (e ▸ hi)
        tauto) gs.length le_rfl o Relation.ReflTransGen.refl
    rw [List.take_length] at this
    exact this
  have hL : ∀ u ∈ forcedL A, Live (n + m) gs o (u : ℕ) := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, Live (n + m) gs o (n + (v : ℕ)) := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hBL : BL ⊆ forcedL A := by
    intro a ha
    obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
    obtain ⟨a', _, ha'⟩ := hK b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab, a', ha'⟩
  have hBR : BR ⊆ forcedR A := by
    intro b hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', _, hb'⟩ := hR a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab, b', hb'⟩
  let Z0 : Finset ℕ := (forcedL A \ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))
  have hZ0 : ∀ i ∈ Z0, i < n + m ∧ i ∈ Z ∧ Live (n + m) gs o i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ha
      exact ⟨by have := a.2; omega, (hZl a).2 h2, hL a h1⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hb
      exact ⟨by have := b.2; omega, (hZr b).2 h2, hRr b h1⟩
  have hZ0c : Z0.card = (forcedL A \ BL).card + (forcedR A \ BR).card := by
    have hdis : Disjoint ((forcedL A \ BL).image (fun a : Fin n => (a : ℕ)))
        ((forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.2
      omega
    show (_ ∪ _ : Finset ℕ).card = _
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]

  have hval : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) (({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z)) =
        (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : u ∈ BL
    · by_cases hv : v ∈ BR
      · have hu' := (Finset.mem_filter.1 hu).1
        have hv' := (Finset.mem_filter.1 hv).1
        rw [show ({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z = {(u : ℕ), n + (v : ℕ)} from by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hZl]; exact fun h => h hu
          · rw [Finset.mem_singleton.1 hi, hZr]; exact fun h => h hv, hA]
        simp [hu', hv']
      ·
        have hu' := (Finset.mem_filter.1 hu).1
        obtain ⟨b, hb, hab⟩ := hR u hu'
        have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hne
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
          exact hv (Finset.mem_filter.2 ⟨hne.2, u, hne.1.2, hne.1.1⟩)
        rw [e1]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := hmono _ {(u : ℕ), n + (b : ℕ)} (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · simp
          · rw [Finset.mem_singleton.1 h1] at h2; exact absurd ((hZr v).2 hv) h2) hne
        rw [hA, hab] at this
        exact Bool.noConfusion this
    ·
      have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hne
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
        exact hu (Finset.mem_filter.2 ⟨hne.1.2, v, hne.2, hne.1.1⟩)
      rw [e1]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      obtain ⟨b, hb, a, hab⟩ : ∃ b : Fin m, (n + (v : ℕ) ∉ Z → b = v) ∧ ∃ a : Fin n, A a b = false := by
        by_cases hv : v ∈ BR
        · obtain ⟨a, _, ha⟩ := hK v (Finset.mem_filter.1 hv).1
          exact ⟨v, fun _ => rfl, a, ha⟩
        · obtain ⟨a, _, ha⟩ := hK v0 hv0
          exact ⟨v0, fun h => absurd ((hZr v).2 hv) h, a, ha⟩
      have := hmono _ {(a : ℕ), n + (b : ℕ)} (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact absurd ((hZl u).2 hu) h2
        · rw [Finset.mem_singleton.1 h1] at h2 ⊢
          rw [hb h2]; simp) hne
      rw [hA, hab] at this
      exact Bool.noConfusion this
  obtain ⟨D, hD1, hD2, hD3⟩ := kill (n + m) Z gs hgs o Z0 hZ0 {(u0 : ℕ), n + (v0 : ℕ)}
    (by rw [hval]; simp [h0, hu0, hv0])
  refine ⟨D.size, ⟨D, hD1, le_rfl, fun u v => ?_⟩, ?_⟩
  · rw [oneEach_eq, hD3, hval]
  · have c1 := Finset.card_sdiff_add_card_eq_card hBL
    have c2 := Finset.card_sdiff_add_card_eq_card hBR
    have hs' : gs.length ≤ s := hs
    have e1 : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
      ∃ a' : Fin n, A a' b = false)).card = (forcedL A).card := by unfold forcedL; congr
    have e2 : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin m, A a b' = false)).card = (forcedR A).card := by unfold forcedR; congr
    have e3 : (R.filter (fun a => ∃ b ∈ K, A a b = true)).card = BL.card := by congr
    have e4 : (K.filter (fun b => ∃ a ∈ R, A a b = true)).card = BR.card := by congr
    rw [e1, e2]
    try rw [e3, e4]
    omega

end PEqualNP.Outside.L_meta_27804.Lower.Strip

namespace PEqualNP.Outside.L_meta_27804.Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents (oneEach Represents RepSizeAtMost)

def edge (x y : Nat) : Bool :=
  (64478 : Nat).testBit (4 * min x 3 + min y 3)

private theorem edge_spec (x y : Nat) : edge x y = !decide (x = y ∧ x < 3) := by
  have small : ∀ a b : Fin 4, (64478 : Nat).testBit (4*a.val+b.val) =
      !decide (a.val = b.val ∧ a.val < 3) := by decide
  unfold edge
  rw [small ⟨min x 3, by omega⟩ ⟨min y 3, by omega⟩]
  have h : (min x 3 = min y 3 ∧ min x 3 < 3) ↔ (x=y ∧ x<3) := by omega
  simp only [h]

private def low {n : Nat} (h : 3 ≤ n) : Finset (Fin n) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem mem_low {n : Nat} (h : 3 ≤ n) (i : Fin n) : i ∈ low h ↔ i.val < 3 := by
  simp only [low, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a,rfl⟩
    exact a.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,rfl⟩

private theorem card_low {n : Nat} (h : 3 ≤ n) : (low h).card = 3 := by simp [low]

private theorem adjacent_low {m : Nat} (h : 3 ≤ m) (x : Nat) :
    ∃ j : Fin m, j.val < 3 ∧ edge x j.val = true := by
  by_cases hx : x = 0
  · exact ⟨⟨1,by omega⟩, by change 1 < 3; decide, by simp [edge_spec,hx]⟩
  · exact ⟨⟨0,by omega⟩, by change 0 < 3; decide, by simp [edge_spec,hx]⟩

private theorem edge_symm (x y : Nat) : edge x y = edge y x := by
  rw [edge_spec,edge_spec]
  by_cases h : x=y
  · subst y; rfl
  · simp [h,Ne.symm h]

theorem saved (n m s : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (source : Represents.RepSizeAtMost (fun (i : Fin n) (j : Fin m) => edge i.val j.val) s) :
    ∃ t : Nat, Represents.RepSizeAtMost
        (fun (i : Fin n) (j : Fin m) => edge i.val j.val && decide (i.val < 3) && decide (j.val < 3)) t ∧
      t + (n+m) ≤ s + 6 := by
  let A := fun (i : Fin n) (j : Fin m) => edge i.val j.val
  have missR (i : Fin n) (hi : i ∈ low hn) : ∃ j ∈ low hm, A i j = false := by
    have h := (mem_low hn i).mp hi
    exact ⟨⟨i.val,by omega⟩, (mem_low hm _).mpr h, by simp [A,edge_spec,h]⟩
  have missK (j : Fin m) (hj : j ∈ low hm) : ∃ i ∈ low hn, A i j = false := by
    have h := (mem_low hm j).mp hj
    exact ⟨⟨j.val,by omega⟩, (mem_low hn _).mpr h, by simp [A,edge_spec,h]⟩
  have hit : ∃ i ∈ low hn, ∃ j ∈ low hm, A i j = true := by
    exact ⟨⟨0,by omega⟩, (mem_low hn _).mpr (by change 0 < 3; decide), ⟨1,by omega⟩,
      (mem_low hm _).mpr (by change 1 < 3; decide), by change edge 0 1 = true; decide⟩
  have activeR (a : Fin n) : ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false := by
    obtain ⟨b,hb,ab⟩ := adjacent_low hm a.val
    obtain ⟨a',_,zero⟩ := missK b ((mem_low hm _).mpr hb)
    exact ⟨b,ab,a',zero⟩
  have activeK (b : Fin m) : ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false := by
    obtain ⟨a,ha,ba⟩ := adjacent_low hn b.val
    obtain ⟨b',_,zero⟩ := missR a ((mem_low hn _).mpr ha)
    exact ⟨a, (edge_symm _ _).trans ba,b',zero⟩
  obtain ⟨t,rep,budget⟩ := Strip.induced n m s A (low hn) (low hm) missR missK hit source
  have r := Finset.card_filter_le (low hn) (fun a => ∃ b ∈ low hm, A a b = true)
  have c := Finset.card_filter_le (low hm) (fun b => ∃ a ∈ low hn, A a b = true)
  simp [activeR,activeK] at budget
  rw [card_low] at r c
  exact ⟨t,by simpa only [A,mem_low] using rep,by omega⟩

private def wire (n m a b dead w : Nat) : Nat :=
  if w < n then (if w < a then w else dead)
  else if w < n + m then (if w - n < b then a + (w - n) else dead)
  else a + b + (w - (n + m))

private def rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

private def prefixStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]

private theorem lengthInput {a b : Nat} (u : Fin a) (v : Fin b) : (oneEach u v).length = a + b := by
  simp [oneEach]

private theorem readInput {a b : Nat} (u : Fin a) (v : Fin b) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = a + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases hi : i < a
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff, show i ≠ a + v.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
    by_cases hj : i - a < b
    · simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff, show i ≠ u.val by omega,
        show i - a = v.val ↔ i = a + v.val by omega]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [show i ≠ u.val by omega, show i ≠ a + v.val by omega]

private theorem readPrefix {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (tail : List Bool) (ht : tail.length ≤ N) (w : Nat) :
    (oneEach u v ++ tail).getD (wire n m a b (a + b + N) w) false =
    (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail).getD w false := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases raw : w < n + m
  · conv_rhs => rw [List.getD_append _ _ _ _ (by rwa [lengthInput]), readInput]
    simp only [Fin.val_castLE]
    by_cases left : w < n
    · by_cases kept : w < a
      · simp only [wire, if_pos left, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show w ≠ a + v.val by omega, show w ≠ n + v.val by omega]
      · simp only [wire, if_pos left, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
    · by_cases kept : w - n < b
      · simp only [wire, if_neg left, if_pos raw, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show a + (w - n) ≠ u.val by omega, show w ≠ u.val by omega,
          show a + (w - n) = a + v.val ↔ w = n + v.val by omega] <;> omega
      · simp only [wire, if_neg left, if_pos raw, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
  · simp only [wire, if_neg (show ¬ w < n by omega), if_neg raw]
    rw [List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega),
      List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega), lengthInput, lengthInput]
    congr 1
    omega

private theorem simulation {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (gs : List Gate) (tail : List Bool) (h : tail.length + gs.length ≤ N) :
    let r := wire n m a b (a + b + N)
    ∃ out : List Bool, out.length ≤ N ∧
      (gs.map (rename r)).foldl prefixStep (oneEach u v ++ tail) = oneEach u v ++ out ∧
      gs.foldl prefixStep (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail) =
        oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ out := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, by simpa using h, rfl, rfl⟩
  | cons g rest ih =>
    let old := oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail
    let bit := g.op.eval (g.inputs.map fun k => old.getD k false)
    have ht : tail.length ≤ N := by omega
    have same : (rename (wire n m a b (a + b + N)) g).op.eval
        ((rename (wire n m a b (a + b + N)) g).inputs.map fun k =>
          (oneEach u v ++ tail).getD k false) = bit := by
      simp only [rename, List.map_map, Function.comp_def, readPrefix ha hb u v tail ht, bit, old]
    have bound : (tail ++ [bit]).length + rest.length ≤ N := by
      simp only [List.length_cons] at h
      simp; omega
    simpa only [List.map_cons, List.foldl_cons, prefixStep, same, List.append_assoc, bit, old]
      using ih (tail ++ [bit]) bound

theorem restrictPrefix {n m a b s : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) s := by
  obtain ⟨C, mono, size, rep⟩ := h
  let r := wire n m a b (a + b + C.size)
  let D : Circuit := ⟨C.gates.map (rename r), r C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using mono f hf
  · simpa [D, Circuit.size] using size
  · intro u v
    obtain ⟨out, len, hnew, hold⟩ :=
      simulation (N := C.size) ha hb u v C.gates [] (by simp [Circuit.size])
    simp only [List.append_nil] at hnew hold
    have val := rep (Fin.castLE ha u) (Fin.castLE hb v)
    change (C.gates.foldl prefixStep _).getD C.output false = _ at val
    change ((C.gates.map (rename r)).foldl prefixStep _).getD (r C.output) false = _
    rw [hnew, readPrefix ha hb u v out len, ← hold, val]

theorem lower (n m : Nat) (hn : 4 ≤ n) (hm : 4 ≤ m) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin m) =>
      (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)) (n + m) := by
  intro small
  obtain ⟨t, ⟨C, mono, size, rep⟩, budget⟩ :=
    saved n m (n + m) (by omega) (by omega) small
  have size6 : C.size ≤ 6 := by omega
  have restricted := restrictPrefix hn hm _ (s := 6) ⟨C, mono, size6, rep⟩
  have table : ∀ i j : Fin 4,
      (edge i.val j.val && decide (i.val < 3) && decide (j.val < 3)) =
        (854 : Nat).testBit (4 * i.val + j.val) := by decide
  apply PEqualNP.Outside.L_meta_6158.2
  simpa only [Fin.coe_castLE, table] using restricted

end PEqualNP.Outside.L_meta_27804.Lower

namespace PEqualNP.Outside.L_meta_27804.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]

private def core (n total : Nat) : List Gate :=
  [⟨.or, [0,n]⟩, ⟨.or, [1,n+1]⟩, ⟨.or, [2,n+2]⟩,
   ⟨.and, [total,total+1]⟩, ⟨.or, [total,total+1]⟩,
   ⟨.and, [total+4,total+2]⟩, ⟨.or, [total+3,total+5]⟩]

private def bits (xs : List Bool) (n : Nat) : List Bool :=
  let p := xs.getD 0 false || xs.getD n false
  let q := xs.getD 1 false || xs.getD (n+1) false
  let r := xs.getD 2 false || xs.getD (n+2) false
  [p,q,r,p && q,p || q,(p || q) && r,(p && q) || ((p || q) && r)]

private theorem core_run (xs : List Bool) (n : Nat) (h : n+2 < xs.length) :
    (core n xs.length).foldl step xs = xs ++ bits xs n := by
  have raw (ls : List Bool) (j : Nat) (hj : j < xs.length) :
      (xs ++ ls).getD j false = xs.getD j false := List.getD_append _ _ _ _ hj
  have added (ls : List Bool) (j : Nat) :
      (xs ++ ls).getD (xs.length+j) false = ls.getD j false := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega
  have first (ls : List Bool) :
      (xs ++ ls).getD xs.length false = ls.getD 0 false := by simpa using added ls 0
  simp (disch := omega) only [core, step, bits, GateOp.eval, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append, List.nil_append,
    added, first, raw, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]

private def chain (last : Nat) : List Nat → List Gate
  | [] => []
  | w :: ws => ⟨.or,[last,w]⟩ :: chain (last+1) ws

private theorem chain_len (last : Nat) (ws : List Nat) : (chain last ws).length = ws.length := by
  induction ws generalizing last with
  | nil => rfl
  | cons _ _ ih => simp [chain, ih]

private theorem chain_pos (last : Nat) (ws : List Nat) :
    ∀ g ∈ chain last ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing last with
  | nil => simp [chain]
  | cons w ws ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | keep
    · simp
    · exact ih (last+1) g keep

private theorem anyAgree (xs : List Nat) (p q : Nat → Bool)
    (agree : ∀ k ∈ xs, p k = q k) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons k rest ih =>
    rw [List.any_cons, List.any_cons, agree k (by simp), ih (fun t ht => agree t (by simp [ht]))]

private theorem chain_run (xs : List Bool) (last : Nat) (ws : List Nat)
    (len : xs.length = last+1) (early : ∀ w ∈ ws, w < xs.length) :
    ((chain last ws).foldl step xs).getD (last+ws.length) false =
      (xs.getD last false || ws.any (fun w => xs.getD w false)) := by
  induction ws generalizing xs last with
  | nil => simp [chain]
  | cons w ws ih =>
    let v := xs.getD last false || xs.getD w false
    have e : ∀ k ∈ ws, k < xs.length := fun k hk => early k (List.mem_cons_of_mem _ hk)
    have eq : step xs ⟨GateOp.or,[last,w]⟩ = xs ++ [v] := by simp [step, v, GateOp.eval]
    have lastVal : (xs ++ [v]).getD (last+1) false = v := by
      rw [← len, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      rfl
    have other : ws.any (fun k => (xs ++ [v]).getD k false) = ws.any (fun k => xs.getD k false) := by
      apply anyAgree
      intro k hk
      exact List.getD_append _ _ _ _ (e k hk)
    simp only [chain,List.foldl_cons,List.length_cons,List.any_cons,eq]
    rw [show last+(ws.length+1) = (last+1)+ws.length by omega,
      ih (xs ++ [v]) (last+1) (by simp [len]) (by intro k hk; specialize e k hk; simp; omega),
      lastVal,other]
    exact Bool.or_assoc _ _ _

private def extras (n m : Nat) : List Nat :=
  ((List.range (n-3)).map (fun t => 3+t)) ++ ((List.range (m-3)).map (fun t => n+3+t))

private theorem extras_mem (n m k : Nat) :
    k ∈ extras n m ↔ (3 ≤ k ∧ k < n) ∨ (n+3 ≤ k ∧ k < n+m) := by
  simp only [extras, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; exact ⟨k-3,by omega,by omega⟩
    · right; exact ⟨k-(n+3),by omega,by omega⟩

private theorem rawBit {n m : Nat} (i : Fin n) (j : Fin m) (w : Nat) :
    (Represents.oneEach i j).getD w false = decide (w = i.val ∨ w = n+j.val) := by
  unfold Represents.oneEach
  by_cases lw : w < n
  · rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using lw)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using lw)]
    simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]
    by_cases rw' : w-n < m
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using rw')]
      simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
      omega
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
      have neither : ¬(w=i.val ∨ w=n+j.val) := by omega
      simp [neither]

private def flag (a b k : Nat) : Bool := decide (a=k) || decide (b=k)

private def vote (a b c : Bool) : Bool := (a && b) || ((a || b) && c)

private theorem graphFormula (a b : Nat) :
    (vote (flag a b 0) (flag a b 1) (flag a b 2) || decide (3 ≤ a ∨ 3 ≤ b)) =
    (64478 : Nat).testBit (4 * min a 3 + min b 3) := by
  have control : ∀ i j : Fin 4,
      (vote (flag i.val j.val 0) (flag i.val j.val 1) (flag i.val j.val 2) ||
        decide (3 ≤ i.val ∨ 3 ≤ j.val)) = (64478 : Nat).testBit (4*i.val+j.val) := by decide
  have low (x k : Nat) (h : k < 3) : (min x 3 = k) ↔ x=k := by omega
  have high (x : Nat) : 3 ≤ min x 3 ↔ 3 ≤ x := by omega
  simpa (disch := decide) only [flag, low, high] using
    control ⟨min a 3,by omega⟩ ⟨min b 3,by omega⟩

private theorem extraValue {n m : Nat} (i : Fin n) (j : Fin m) :
    (extras n m).any (fun w => (Represents.oneEach i j).getD w false) =
      decide (3 ≤ i.val ∨ 3 ≤ j.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, extras_mem, rawBit, decide_eq_true_eq]
  constructor
  · rintro ⟨w, h, h'⟩
    omega
  · rintro (hi | hj)
    · exact ⟨i.val, Or.inl ⟨hi,i.isLt⟩, Or.inl rfl⟩
    · exact ⟨n+j.val, Or.inr ⟨by omega,by omega⟩, Or.inr rfl⟩

private theorem coreValue {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) (i : Fin n) (j : Fin m) :
    (bits (Represents.oneEach i j) n).getD 6 false =
      vote (flag i.val j.val 0) (flag i.val j.val 1) (flag i.val j.val 2) := by
  have left (k : Nat) (hk : k < 3) :
      (Represents.oneEach i j).getD k false = decide (i.val=k) := by
    rw [rawBit, decide_eq_decide]; omega
  have right (k : Nat) (hk : k < 3) :
      (Represents.oneEach i j).getD (n+k) false = decide (j.val=k) := by
    rw [rawBit, decide_eq_decide]; omega
  have right0 := right 0 (by decide)
  rw [Nat.add_zero] at right0
  simp (disch := decide) only [bits, List.getD_cons_succ, List.getD_cons_zero,
    left, right, right0, vote, flag]

theorem threeHoleUpper :
∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = n + m + 1 ∧
      PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) =>
        (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)) C := by
  intro n m hn hm
  let N := n+m
  let rest := extras n m
  let C : Circuit := ⟨core n N ++ chain (N+6) rest, N+6+rest.length⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ core n N ++ chain (N+6) rest at hg
    rcases List.mem_append.mp hg with hc | he
    · simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using chain_pos (N+6) rest g he
  · change (core n N ++ chain (N+6) rest).length = n+m+1
    simp only [List.length_append, chain_len, rest, extras, List.length_map,List.length_range]
    change 7 + ((n-3)+(m-3)) = n+m+1
    omega
  · intro i j
    let xs := Represents.oneEach i j
    have len : xs.length = N := by simp [xs, N, Represents.oneEach]
    have bLen : (bits xs n).length = 7 := rfl
    have short : ∀ w ∈ rest, w < xs.length := by
      intro w hw
      rcases (extras_mem n m w).mp hw with h | h <;> dsimp [N] at len <;> omega
    have init : (core n N).foldl step xs = xs ++ bits xs n := by
      rw [← len]; exact core_run xs n (by dsimp [N] at len; omega)
    have past : (xs ++ bits xs n).getD (N+6) false = (bits xs n).getD 6 false := by
      rw [List.getD_append_right _ _ _ _ (by omega),len]
      congr 1
      omega
    have same : rest.any (fun w => (xs ++ bits xs n).getD w false) =
        rest.any (fun w => xs.getD w false) := by
      apply anyAgree
      intro w hw
      exact List.getD_append _ _ _ _ (short w hw)
    change ((core n N ++ chain (N+6) rest).foldl step xs).getD (N+6+rest.length) false = _
    rw [List.foldl_append,init,chain_run _ _ _ (by simp [len,bLen])
      (by intro w hw; specialize short w hw; simp [bLen]; omega),past,same,
      coreValue hn hm i j,extraValue i j]
    exact graphFormula i.val j.val

end PEqualNP.Outside.L_meta_27804.Upper

theorem PEqualNP.Outside.L_meta_27804 : (∀ (n m : Nat), 4 ≤ n → 4 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)) := by
  intro n m hn hm
  obtain ⟨C, mono, size, rep⟩ :=
    PEqualNP.Outside.L_meta_27804.Upper.threeHoleUpper n m (by omega) (by omega)
  exact ⟨⟨C, mono, size.le, rep⟩, PEqualNP.Outside.L_meta_27804.Lower.lower n m hn hm⟩
