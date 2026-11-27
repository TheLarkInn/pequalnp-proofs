import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30815_aux.Signed

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 1326
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 663 := ((x >>> 663) ^^^ x).setWidth 663
def cuts (ws : List W) : BitVec 663 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 663) ++ (0 : BitVec 663)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 663) (w : W) : Prop :=
  w.getLsbD (663+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 663) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 663+i.val < 1326 := by omega
  have hi' : i.val < 1326 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 663) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 663)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && (if w ∈ a :: b :: r then false else next extra (w :: r))) ||
    ((extra != 0) && (((v ||| sep a == -1) && (if w ∈ a :: b :: r then false else next (extra - 1) (w :: a :: r))) ||
                       ((v ||| sep b == -1) && (if w ∈ a :: b :: r then false else next (extra - 1) (w :: b :: r))))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && (if w ∈ a :: b :: r then false else next (extra - 2) (w :: a :: b :: r)))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (new : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp only [if_neg new]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop
          (fun mem => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr mem))) hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 1326 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 1326)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 1326) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 1326) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 1326) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 1326 0)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
namespace Fast

def mask : Nat := 2 ^ 663 - 1
def full : Nat := 2 ^ 1326 - 1
def highGoal : Nat := mask <<< 663
def cut (w : Nat) := ((w >>> 663) ^^^ w) &&& mask
def cover : List Nat → Nat
  | [] => 0
  | x :: r => cut x ||| cover r
def mix (a b : Nat) : List Nat := [a &&& b, a ||| b, a &&& (full ^^^ b), b &&& (full ^^^ a)]
def dispatchN (extra : Nat) (next : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  let base := cover r
  (mix a b).any fun w =>
    let v := cut w ||| base
    ((v == mask) && (if w ∈ a :: b :: r then false else next extra (w :: r))) ||
    ((extra != 0) && (((v ||| cut a == mask) && (if w ∈ a :: b :: r then false else next (extra - 1) (w :: a :: r))) ||
                       ((v ||| cut b == mask) && (if w ∈ a :: b :: r then false else next (extra - 1) (w :: b :: r))))) ||
    ((extra ≥ 2) && (v ||| cut a ||| cut b == mask) && (if w ∈ a :: b :: r then false else next (extra - 2) (w :: a :: b :: r)))
def run : Nat → Nat → List Nat → Bool
  | 0, _, ws => ws == [highGoal] || ws == [mask]
  | k+1, e, ws => (ws == [highGoal] || ws == [mask]) ||
    (pairs ws).any (fun (a,b,r) => dispatchN e (run k) a b r)

def enc (ws : List W) := ws.map BitVec.toNat
lemma enc_def (ws : List W) : enc ws = ws.map BitVec.toNat := rfl
lemma enc_cons (w : W) (ws : List W) : enc (w :: ws) = w.toNat :: enc ws := rfl
lemma full_eq : full = (BitVec.allOnes 1326).toNat := by decide +kernel
lemma mask_eq : mask = (BitVec.allOnes 663).toNat := by decide +kernel
lemma high_eq : highGoal = goal.toNat := by decide +kernel
lemma low_eq : mask = (~~~goal).toNat := by decide +kernel
lemma neg_eq (w : W) : full ^^^ w.toNat = (~~~w).toNat := by
  rw [BitVec.not_def,BitVec.toNat_xor,full_eq]
lemma cut_eq (w : W) : cut w.toNat = (sep w).toNat := by
  unfold cut sep mask
  rw [Nat.and_two_pow_sub_one_eq_mod,BitVec.toNat_setWidth,BitVec.toNat_xor,BitVec.toNat_ushiftRight]
set_option maxRecDepth 16000 in
lemma cover_eq (ws : List W) : cover (enc ws) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change cut w.toNat ||| cover (enc ws) = (sep w ||| cuts ws).toNat
    rw [cut_eq, ih, BitVec.toNat_or]
lemma mix_eq (a b : W) : mix a.toNat b.toNat = enc (ops a b) := by
  simp only [mix, ops, enc, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or, neg_eq]
set_option maxRecDepth 16000 in
lemma isfull (w : BitVec 663) : (w.toNat == mask) = (w == -1) := by
  rw [mask_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.toNat_inj]
  rfl
lemma enc_mem {xs : List W} {w : W} : w.toNat ∈ enc xs ↔ w ∈ xs := by
  change w.toNat ∈ xs.map BitVec.toNat ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨u,hu,eq⟩
    exact BitVec.toNat_inj.mp eq ▸ hu
  · exact fun h => ⟨w,h,rfl⟩
lemma dis_eq (e : Nat) (f : Nat → List Nat → Bool) (g : Nat → List W → Bool)
    (eqn : ∀ j ws, f j (enc ws) = g j ws) (a b : W) (r : List W) :
    dispatchN e f a.toNat b.toNat (enc r) = dispatch e g a b r := by
  unfold dispatchN dispatch
  simp only [mix_eq, enc, List.any_map, Function.comp_def]
  apply List.any_congr rfl
  intro w
  change _ = _
  simp only [←enc_def, cover_eq, cut_eq, ←BitVec.toNat_or, isfull, ←enc_cons, enc_mem, eqn]
lemma one_map (ws : List W) :
    singles (enc ws) = (singles ws).map (fun (b,r) => (b.toNat,enc r)) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    simp only [enc_cons, singles, List.map_cons, ih, List.map_map, Function.comp_def]
lemma two_map (ws : List W) :
    pairs (enc ws) = (pairs ws).map (fun (a,b,r) => (a.toNat,b.toNat,enc r)) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    simp only [enc_cons, pairs, one_map, ih, List.map_append, List.map_map, Function.comp_def]
lemma enc_beq1 (ws : List W) (a : W) : (enc ws == [a.toNat]) = (ws == [a]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    change ws.map BitVec.toNat = [a].map BitVec.toNat at h
    exact List.map_injective_iff.mpr (fun _ _ => BitVec.toNat_inj.mp) h
  · rintro rfl; rfl
lemma run_eq : ∀ (k e : Nat) (ws : List W), run k e (enc ws) = optimized k e ws := by
  intro k; induction k with
  | zero =>
    intro e ws
    simp only [run, optimized, high_eq, low_eq, enc_beq1]
  | succ k ih =>
    intro e ws
    simp only [run, optimized, high_eq, low_eq, enc_beq1, two_map, List.any_map, Function.comp_def]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a,b,r⟩
    exact dis_eq _ _ _ ih _ _ _
end Fast
def targetFun (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 4 && x 5)
def inputs : List W := [(BitVec.ofNat 1326 ((((((((((((((((((((((4 * 1152921504606846976 + 90646007687316500) * 1152921504606846976 + 146947875816084512) * 1152921504606846976 + 725168061498532001) * 1152921504606846976 + 22661501921829125) * 1152921504606846976 + 36736968954021128) * 1152921504606846976 + 181292015374633000) * 1152921504606846976 + 293895751632169025) * 1152921504606846976 + 297414618390217026) * 1152921504606846976 + 45323003843658250) * 1152921504606846976 + 73473937908042256) * 1152921504606846976 + 362584030749266007) * 1152921504606846976 + 1151795742122182655) * 1152921504606846976 + 864726308532780992) * 1152921504606846976 + 9006099877314561) * 1152921504606846976 + 1152640063985680895) * 1152921504606846976 + 1080872705588330480) * 1152921504606846976 + 2251524969328640) * 1152921504606846976 + 576460752302375039) * 1152921504606846976 + 1134909304852217855) * 1152921504606846976 + 1152358623364514815) * 1152921504606846976 + 1008823906569814015) * 1152921504606846976 + 1148418454735290367)), (BitVec.ofNat 1326 ((((((((((((((((((((((32 * 1152921504606846976 + 400869301076828249) * 1152921504606846976 + 12527165658650882) * 1152921504606846976 + 901111399400932040) * 1152921504606846976 + 100217325269207062) * 1152921504606846976 + 291362167566374464) * 1152921504606846976 + 801738602153656498) * 1152921504606846976 + 25054331317301765) * 1152921504606846976 + 649301294195017104) * 1152921504606846976 + 200434650538414124) * 1152921504606846976 + 582724335132748929) * 1152921504606846976 + 450555699700466023) * 1152921504606846976 + 1152921367167895551) * 1152921504606846976 + 1152886320235282431) * 1152921504606846976 + 1143914305486323710) * 1152921504606846976 + 34359737856) * 1152921504606846976 + 8796092891136) * 1152921504606846976 + 2251799780130816) * 1152921504606846976 + 576390392149180288) * 1152921504606846976 + 2199023222787) * 1152921504606846976 + 1152921435887371263) * 1152921504606846976 + 1152921504606584863) * 1152921504606846976 + 1152920954918133760)), (BitVec.ofNat 1326 ((((((((((((((((((((((1 * 1152921504606846976 + 432539101899260256) * 1152921504606846976 + 49545643953315851) * 1152921504606846976 + 1548301373541120) * 1152921504606846976 + 396365151626526808) * 1152921504606846976 + 12386410988328962) * 1152921504606846976 + 865078203798520512) * 1152921504606846976 + 99091287906631702) * 1152921504606846976 + 3096602747082240) * 1152921504606846976 + 792730303253053616) * 1152921504606846976 + 24772821976657925) * 1152921504606846976 + 577234902990194055) * 1152921504606846976 + 1152921504606844928) * 1152921504606846976 + 524287) * 1152921504606846976 + 1152921504472629248) * 1152921504606846976 + 34359738367) * 1152921504606846976 + 1152912708513824768) * 1152921504606846976 + 2251799813685247) * 1152921504606846976 + 576460760893358079) * 1152921504606846976 + 1152919305583591427) * 1152921504606846976 + 1152921504606845952) * 1152921504606846976 + 17592186044384) * 1152921504606846976 + 67108863)), (BitVec.ofNat 1326 ((((((((((((((((((((((9 * 1152921504606846976 + 577797921671481728) * 1152921504606846976 + 342315358222909516) * 1152921504606846976 + 10697354944465922) * 1152921504606846976 + 432679856569582176) * 1152921504606846976 + 85578839555727379) * 1152921504606846976 + 2674338736116480) * 1152921504606846976 + 684630716445819032) * 1152921504606846976 + 21394709888931844) * 1152921504606846976 + 865359713139164352) * 1152921504606846976 + 171157679111454758) * 1152921504606846976 + 5348677472232967) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606322688) * 1152921504606846976 + 0) * 1152921504606846976 + 34359738367) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1150669704793161728) * 1152921504606846976 + 8589934591) * 1152921504606846976 + 1152921504606846972) * 1152921504606846976 + 0) * 1152921504606846976 + 17592186044415) * 1152921504606846976 + 1152921504539738112)), (BitVec.ofNat 1326 ((((((((((((((((((((((14 * 1152921504606846976 + 1970565384506880) * 1152921504606846976 + 504464738433761392) * 1152921504606846976 + 15764523076055043) * 1152921504606846976 + 576953393649550208) * 1152921504606846976 + 126116184608440348) * 1152921504606846976 + 3941130769013760) * 1152921504606846976 + 1008929476867522784) * 1152921504606846976 + 31529046152110087) * 1152921504606846976 + 985282692253440) * 1152921504606846976 + 252232369216880696) * 1152921504606846976 + 7882261538027527) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921470247108608) * 1152921504606846976 + 0) * 1152921504606846976 + 0) * 1152921504606846976 + 8589934591) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152903912420802560) * 1152921504606846976 + 0)), (BitVec.ofNat 1326 ((((((((((((((((((((((48 * 1152921504606846976 + 6756224175452161) * 1152921504606846976 + 576671884308906368) * 1152921504606846976 + 54049793403617292) * 1152921504606846976 + 1689056043863040) * 1152921504606846976 + 432398347228938336) * 1152921504606846976 + 13512448350904323) * 1152921504606846976 + 422264010965760) * 1152921504606846976 + 108099586807234584) * 1152921504606846976 + 3378112087726080) * 1152921504606846976 + 864796694457876672) * 1152921504606846976 + 27024896701808647) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921496016912384) * 1152921504606846976 + 0) * 1152921504606846976 + 0) * 1152921504606846976 + 0) * 1152921504606846976 + 0))]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sample_rows : ∀ j : Fin 1326,
    targetFun (fun i => (inputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 1326) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have width : inputs.length = 6 := rfl
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

abbrev dead (n : Nat) (ws : List W) :=
  ∀ g : W, (g = goal ∨ g = ~~~goal) → ¬live basicOps g n ws.toFinset

def insertWire (x : W) : List W → List W
  | [] => [x]
  | a::r => if x.toNat ≤ a.toNat then x::a::r else a::insertWire x r
def ordered (ws : List W) := ws.foldr insertWire []
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem insertWire_set (x : W) (ws : List W) : (insertWire x ws).toFinset = insert x ws.toFinset := by
  induction ws with
  | nil => simp [insertWire]
  | cons a r ih =>
    by_cases h : x.toNat ≤ a.toNat
    · simp [insertWire,h]
    · simp [insertWire,h,ih,Finset.insert_comm]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ordered_set (ws : List W) : (ordered ws).toFinset = ws.toFinset := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    change (insertWire a (ordered r)).toFinset = _
    rw [insertWire_set, ih, List.toFinset_cons]

def candidates (n : Nat) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z ∈ ws then [] else
      ((keepChoices a b r).filter (fun kept => decide (kept.length ≤ n) && (cuts (z::kept) == -1))).map
        (fun kept => ordered (z::kept))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem dead_split (n : Nat) (ws : List W) (nd : ws.Nodup) (h₀ : ws ≠ [goal] ∧ ws ≠ [~~~goal])
    (all : ∀ c ∈ candidates n ws, dead n c) : dead (n+1) ws := by
  intro g hg h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have he := singleton_list nd done
    rcases hg with rfl | rfl
    · exact h₀.1 he
    · exact h₀.2 he
  obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : W} (pair : (a,b,r) ∈ pairs ws) (perm : ws.Perm (a::b::r))
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
    obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm nd hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
    have hl : live basicOps g n (z :: kept).toFinset := by simpa [hfin] using tail
    have sz := live_card hl
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at sz
    have sz' : kept.length ≤ n := by omega
    have hcut := cuts_full hg hl
    have out : z ∉ ws := fun mem => hout (List.mem_toFinset.mpr mem)
    have mem : ordered (z::kept) ∈ candidates n ws := by
      refine List.mem_flatMap.mpr ⟨(a,b,r),pair,?_⟩
      refine List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩
      simpa only [out,ite_false,List.mem_map,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using
        (show ∃ w, (w ∈ keepChoices a b r ∧ w.length ≤ n ∧ cuts (z::w) = -1) ∧ ordered (z::w) = ordered (z::kept) from
          ⟨kept,⟨hk,sz',hcut⟩,rfl⟩)
    apply all _ mem g hg
    simpa only [ordered_set] using hl
  rcases hm with pair | pair
  · exact go pair hp hs hz
  · exact go pair (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem dead_leaf (n : Nat) (ws : List W) (nd : ws.Nodup)
    (h : optimized n (n+1-ws.length) ws = false) : dead n ws := by
  intro g hg run
  have sz := live_card run
  rw [List.toFinset_card_of_nodup nd] at sz
  exact Bool.noConfusion (h.symm.trans (optimized_complete hg n ws _ nd (by omega) run))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_dead_cons {n : Nat} {x : List W} {xs : List (List W)}
    (h : dead n x) (hs : ∀ y ∈ xs, dead n y) : ∀ y ∈ x::xs, dead n y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hmem
  · exact h
  · exact hs _ hmem
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem all_dead_nil (n : Nat) : ∀ y ∈ ([] : List (List W)), dead n y := by simp

def goodChild (n : Nat) (known : List (List W)) (c : List W) : Bool :=
  known.contains c || (decide c.Nodup && !(optimized n (n+1-c.length) c))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem dead_split_checked (n : Nat) (ws : List W) (listed : List (List W)) (nd : ws.Nodup)
   (noOut : ws ≠ [goal] ∧ ws ≠ [~~~goal]) (known : ∀ c ∈ listed, dead n c)
   (pass : (candidates n ws).all (goodChild n listed) = true) : dead (n+1) ws := by
  apply dead_split n ws nd noOut
  intro c hc
  have good := List.all_eq_true.mp pass c hc
  simp only [goodChild,Bool.or_eq_true,List.contains_iff_mem,Bool.and_eq_true,decide_eq_true_eq,
    Bool.not_eq_true'] at good
  rcases good with mem | ⟨hn,hr⟩
  · exact known c mem
  · exact dead_leaf n c hn hr

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem scan_block {α : Type} (xs : List α) (p : α → Bool) (i k : Nat)
    (a : ((xs.drop i).take k).all p = true) (b : (xs.drop (i+k)).all p = true) :
    (xs.drop i).all p = true := by
  rw [← List.take_append_drop k (xs.drop i),List.all_append,a,Bool.true_and,List.drop_drop]
  simpa [Nat.add_comm] using b

def essential (ws : List W) := ws.sublists.all fun sub => (cuts sub != -1) || (sub == ws)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish_impossible (n : Nat) (ws : List W) (hess : essential ws = true)
    (reject : dead n ws) (g : W) (hg : g = goal ∨ g = ~~~goal) (run : build basicOps g n ws.toFinset) : False := by
  classical
  obtain ⟨s,sub,hl⟩ := compress run
  let take := ws.filter (· ∈ s)
  have eq : take.toFinset = s := by
    ext w
    simp only [take,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun h => List.mem_toFinset.mp (sub h)
  have live' : live basicOps g n take.toFinset := eq.symm ▸ hl
  have mask := cuts_full hg live'
  have same := List.all_eq_true.mp hess take (List.mem_sublists.mpr (List.filter_sublist ..))
  simp only [mask,bne_self_eq_false,Bool.false_or,beq_iff_eq] at same
  exact reject g hg (same ▸ live')

def branch0 : List W := [((inputs.getD 0 0) &&& (inputs.getD 1 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch1 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 0 0) ||| (inputs.getD 1 0)), (inputs.getD 5 0)]
def branch2 : List W := [(inputs.getD 2 0), ((inputs.getD 0 0) &&& ~~~(inputs.getD 1 0)), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch3 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 1 0) &&& ~~~(inputs.getD 0 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch4 : List W := [((inputs.getD 0 0) &&& (inputs.getD 2 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch5 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 0 0) ||| (inputs.getD 2 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch6 : List W := [(inputs.getD 2 0), ((inputs.getD 0 0) &&& ~~~(inputs.getD 2 0)), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch7 : List W := [((inputs.getD 2 0) &&& ~~~(inputs.getD 0 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch8 : List W := [((inputs.getD 0 0) &&& (inputs.getD 3 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch9 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), ((inputs.getD 0 0) ||| (inputs.getD 3 0)), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch10 : List W := [(inputs.getD 2 0), ((inputs.getD 0 0) &&& ~~~(inputs.getD 3 0)), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch11 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 3 0) &&& ~~~(inputs.getD 0 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch12 : List W := [(inputs.getD 2 0), ((inputs.getD 0 0) &&& (inputs.getD 4 0)), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch13 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 0 0) ||| (inputs.getD 4 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch14 : List W := [((inputs.getD 0 0) &&& ~~~(inputs.getD 4 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch15 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), ((inputs.getD 4 0) &&& ~~~(inputs.getD 0 0)), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch16 : List W := [((inputs.getD 0 0) &&& (inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch17 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0), ((inputs.getD 0 0) ||| (inputs.getD 5 0))]
def branch18 : List W := [(inputs.getD 2 0), ((inputs.getD 0 0) &&& ~~~(inputs.getD 5 0)), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch19 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 5 0) &&& ~~~(inputs.getD 0 0)), (inputs.getD 5 0)]
def branch20 : List W := [((inputs.getD 1 0) &&& (inputs.getD 2 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch21 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 1 0) ||| (inputs.getD 2 0)), (inputs.getD 5 0)]
def branch22 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 1 0) &&& ~~~(inputs.getD 2 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch23 : List W := [((inputs.getD 2 0) &&& ~~~(inputs.getD 1 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch24 : List W := [((inputs.getD 1 0) &&& (inputs.getD 3 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch25 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 1 0) ||| (inputs.getD 3 0)), (inputs.getD 5 0)]
def branch26 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 1 0) &&& ~~~(inputs.getD 3 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch27 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 3 0) &&& ~~~(inputs.getD 1 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch28 : List W := [((inputs.getD 1 0) &&& (inputs.getD 4 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch29 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 1 0) ||| (inputs.getD 4 0)), (inputs.getD 5 0)]
def branch30 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 1 0) &&& ~~~(inputs.getD 4 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch31 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), ((inputs.getD 4 0) &&& ~~~(inputs.getD 1 0)), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch32 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 1 0) &&& (inputs.getD 5 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch33 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 5 0), ((inputs.getD 1 0) ||| (inputs.getD 5 0))]
def branch34 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0), ((inputs.getD 1 0) ||| (inputs.getD 5 0))]
def branch35 : List W := [((inputs.getD 1 0) &&& ~~~(inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 5 0)]
def branch36 : List W := [((inputs.getD 1 0) &&& ~~~(inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch37 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 5 0) &&& ~~~(inputs.getD 1 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch38 : List W := [((inputs.getD 2 0) &&& (inputs.getD 3 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch39 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), ((inputs.getD 2 0) ||| (inputs.getD 3 0)), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch40 : List W := [((inputs.getD 2 0) &&& ~~~(inputs.getD 3 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch41 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 3 0) &&& ~~~(inputs.getD 2 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch42 : List W := [((inputs.getD 2 0) &&& (inputs.getD 4 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch43 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 2 0) ||| (inputs.getD 4 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch44 : List W := [((inputs.getD 2 0) &&& ~~~(inputs.getD 4 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch45 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), ((inputs.getD 4 0) &&& ~~~(inputs.getD 2 0)), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch46 : List W := [((inputs.getD 2 0) &&& (inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch47 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0), ((inputs.getD 2 0) ||| (inputs.getD 5 0))]
def branch48 : List W := [((inputs.getD 2 0) &&& ~~~(inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch49 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 5 0) &&& ~~~(inputs.getD 2 0)), (inputs.getD 5 0)]
def branch50 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 3 0) &&& (inputs.getD 4 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch51 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), ((inputs.getD 3 0) ||| (inputs.getD 4 0)), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch52 : List W := [(inputs.getD 2 0), ((inputs.getD 3 0) &&& ~~~(inputs.getD 4 0)), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch53 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 4 0) &&& ~~~(inputs.getD 3 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch54 : List W := [((inputs.getD 3 0) &&& (inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch55 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0), ((inputs.getD 3 0) ||| (inputs.getD 5 0))]
def branch56 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), ((inputs.getD 3 0) &&& ~~~(inputs.getD 5 0)), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch57 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 5 0) &&& ~~~(inputs.getD 3 0)), (inputs.getD 5 0)]
def branch58 : List W := [((inputs.getD 4 0) &&& (inputs.getD 5 0)), (inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch59 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0), ((inputs.getD 4 0) ||| (inputs.getD 5 0))]
def branch60 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), ((inputs.getD 4 0) &&& ~~~(inputs.getD 5 0)), (inputs.getD 4 0), (inputs.getD 1 0), (inputs.getD 5 0)]
def branch61 : List W := [(inputs.getD 2 0), (inputs.getD 0 0), (inputs.getD 3 0), (inputs.getD 4 0), (inputs.getD 1 0), ((inputs.getD 5 0) &&& ~~~(inputs.getD 4 0)), (inputs.getD 5 0)]
def branchList : List (List W) := [branch0, branch1, branch2, branch3, branch4, branch5, branch6, branch7, branch8, branch9, branch10, branch11, branch12, branch13, branch14, branch15, branch16, branch17, branch18, branch19, branch20, branch21, branch22, branch23, branch24, branch25, branch26, branch27, branch28, branch29, branch30, branch31, branch32, branch33, branch34, branch35, branch36, branch37, branch38, branch39, branch40, branch41, branch42, branch43, branch44, branch45, branch46, branch47, branch48, branch49, branch50, branch51, branch52, branch53, branch54, branch55, branch56, branch57, branch58, branch59, branch60, branch61]
namespace Tokens
def put (x : Nat) : List Nat → List Nat
  | [] => [x]
  | a::r => if x ≤ a then x::a::r else a::put x r
def child (ns : List Nat) (t : Nat) : List Nat :=
  let (a,b,r) := (pairs ns).getD (t / 16) (0,0,[])
  let w := (Fast.mix a b).getD ((t / 4) % 4) 0
  let kept := [r,a::r,b::r,a::b::r].getD (t % 4) []
  (w::kept).foldr put []
def valid (ns : List Nat) : Bool :=
  decide ns.Nodup && !(Fast.run 7 (8-ns.length) ns)
def sliceOf (ns ts : List Nat) (i j : Nat) :=
  ((ts.drop i).take j).all (fun t => valid (child ns t))
def endOf (ns ts : List Nat) (i : Nat) :=
  (ts.drop i).all (fun t => valid (child ns t))
end Tokens
namespace Tokens
def x0 : Nat := ((((((((((((((((((((((4 * 1152921504606846976 + 90646007687316500) * 1152921504606846976 + 146947875816084512) * 1152921504606846976 + 725168061498532001) * 1152921504606846976 + 22661501921829125) * 1152921504606846976 + 36736968954021128) * 1152921504606846976 + 181292015374633000) * 1152921504606846976 + 293895751632169025) * 1152921504606846976 + 297414618390217026) * 1152921504606846976 + 45323003843658250) * 1152921504606846976 + 73473937908042256) * 1152921504606846976 + 362584030749266007) * 1152921504606846976 + 1151795742122182655) * 1152921504606846976 + 864726308532780992) * 1152921504606846976 + 9006099877314561) * 1152921504606846976 + 1152640063985680895) * 1152921504606846976 + 1080872705588330480) * 1152921504606846976 + 2251524969328640) * 1152921504606846976 + 576460752302375039) * 1152921504606846976 + 1134909304852217855) * 1152921504606846976 + 1152358623364514815) * 1152921504606846976 + 1008823906569814015) * 1152921504606846976 + 1148418454735290367)
def x1 : Nat := ((((((((((((((((((((((32 * 1152921504606846976 + 400869301076828249) * 1152921504606846976 + 12527165658650882) * 1152921504606846976 + 901111399400932040) * 1152921504606846976 + 100217325269207062) * 1152921504606846976 + 291362167566374464) * 1152921504606846976 + 801738602153656498) * 1152921504606846976 + 25054331317301765) * 1152921504606846976 + 649301294195017104) * 1152921504606846976 + 200434650538414124) * 1152921504606846976 + 582724335132748929) * 1152921504606846976 + 450555699700466023) * 1152921504606846976 + 1152921367167895551) * 1152921504606846976 + 1152886320235282431) * 1152921504606846976 + 1143914305486323710) * 1152921504606846976 + 34359737856) * 1152921504606846976 + 8796092891136) * 1152921504606846976 + 2251799780130816) * 1152921504606846976 + 576390392149180288) * 1152921504606846976 + 2199023222787) * 1152921504606846976 + 1152921435887371263) * 1152921504606846976 + 1152921504606584863) * 1152921504606846976 + 1152920954918133760)
def x2 : Nat := ((((((((((((((((((((((1 * 1152921504606846976 + 432539101899260256) * 1152921504606846976 + 49545643953315851) * 1152921504606846976 + 1548301373541120) * 1152921504606846976 + 396365151626526808) * 1152921504606846976 + 12386410988328962) * 1152921504606846976 + 865078203798520512) * 1152921504606846976 + 99091287906631702) * 1152921504606846976 + 3096602747082240) * 1152921504606846976 + 792730303253053616) * 1152921504606846976 + 24772821976657925) * 1152921504606846976 + 577234902990194055) * 1152921504606846976 + 1152921504606844928) * 1152921504606846976 + 524287) * 1152921504606846976 + 1152921504472629248) * 1152921504606846976 + 34359738367) * 1152921504606846976 + 1152912708513824768) * 1152921504606846976 + 2251799813685247) * 1152921504606846976 + 576460760893358079) * 1152921504606846976 + 1152919305583591427) * 1152921504606846976 + 1152921504606845952) * 1152921504606846976 + 17592186044384) * 1152921504606846976 + 67108863)
def x3 : Nat := ((((((((((((((((((((((9 * 1152921504606846976 + 577797921671481728) * 1152921504606846976 + 342315358222909516) * 1152921504606846976 + 10697354944465922) * 1152921504606846976 + 432679856569582176) * 1152921504606846976 + 85578839555727379) * 1152921504606846976 + 2674338736116480) * 1152921504606846976 + 684630716445819032) * 1152921504606846976 + 21394709888931844) * 1152921504606846976 + 865359713139164352) * 1152921504606846976 + 171157679111454758) * 1152921504606846976 + 5348677472232967) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606322688) * 1152921504606846976 + 0) * 1152921504606846976 + 34359738367) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1150669704793161728) * 1152921504606846976 + 8589934591) * 1152921504606846976 + 1152921504606846972) * 1152921504606846976 + 0) * 1152921504606846976 + 17592186044415) * 1152921504606846976 + 1152921504539738112)
def x4 : Nat := ((((((((((((((((((((((14 * 1152921504606846976 + 1970565384506880) * 1152921504606846976 + 504464738433761392) * 1152921504606846976 + 15764523076055043) * 1152921504606846976 + 576953393649550208) * 1152921504606846976 + 126116184608440348) * 1152921504606846976 + 3941130769013760) * 1152921504606846976 + 1008929476867522784) * 1152921504606846976 + 31529046152110087) * 1152921504606846976 + 985282692253440) * 1152921504606846976 + 252232369216880696) * 1152921504606846976 + 7882261538027527) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921470247108608) * 1152921504606846976 + 0) * 1152921504606846976 + 0) * 1152921504606846976 + 8589934591) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152903912420802560) * 1152921504606846976 + 0)
def x5 : Nat := ((((((((((((((((((((((48 * 1152921504606846976 + 6756224175452161) * 1152921504606846976 + 576671884308906368) * 1152921504606846976 + 54049793403617292) * 1152921504606846976 + 1689056043863040) * 1152921504606846976 + 432398347228938336) * 1152921504606846976 + 13512448350904323) * 1152921504606846976 + 422264010965760) * 1152921504606846976 + 108099586807234584) * 1152921504606846976 + 3378112087726080) * 1152921504606846976 + 864796694457876672) * 1152921504606846976 + 27024896701808647) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921504606846975) * 1152921504606846976 + 1152921496016912384) * 1152921504606846976 + 0) * 1152921504606846976 + 0) * 1152921504606846976 + 0) * 1152921504606846976 + 0)
def z010 := x0 &&& x1
def z011 := x0 ||| x1
def z012 := x0 &&& (Fast.full ^^^ x1)
def z013 := x1 &&& (Fast.full ^^^ x0)
def z020 := x0 &&& x2
def z021 := x0 ||| x2
def z022 := x0 &&& (Fast.full ^^^ x2)
def z023 := x2 &&& (Fast.full ^^^ x0)
def z030 := x0 &&& x3
def z031 := x0 ||| x3
def z032 := x0 &&& (Fast.full ^^^ x3)
def z033 := x3 &&& (Fast.full ^^^ x0)
def z040 := x0 &&& x4
def z041 := x0 ||| x4
def z042 := x0 &&& (Fast.full ^^^ x4)
def z043 := x4 &&& (Fast.full ^^^ x0)
def z050 := x0 &&& x5
def z051 := x0 ||| x5
def z052 := x0 &&& (Fast.full ^^^ x5)
def z053 := x5 &&& (Fast.full ^^^ x0)
def z120 := x1 &&& x2
def z121 := x1 ||| x2
def z122 := x1 &&& (Fast.full ^^^ x2)
def z123 := x2 &&& (Fast.full ^^^ x1)
def z130 := x1 &&& x3
def z131 := x1 ||| x3
def z132 := x1 &&& (Fast.full ^^^ x3)
def z133 := x3 &&& (Fast.full ^^^ x1)
def z140 := x1 &&& x4
def z141 := x1 ||| x4
def z142 := x1 &&& (Fast.full ^^^ x4)
def z143 := x4 &&& (Fast.full ^^^ x1)
def z150 := x1 &&& x5
def z151 := x1 ||| x5
def z152 := x1 &&& (Fast.full ^^^ x5)
def z153 := x5 &&& (Fast.full ^^^ x1)
def z230 := x2 &&& x3
def z231 := x2 ||| x3
def z232 := x2 &&& (Fast.full ^^^ x3)
def z233 := x3 &&& (Fast.full ^^^ x2)
def z240 := x2 &&& x4
def z241 := x2 ||| x4
def z242 := x2 &&& (Fast.full ^^^ x4)
def z243 := x4 &&& (Fast.full ^^^ x2)
def z250 := x2 &&& x5
def z251 := x2 ||| x5
def z252 := x2 &&& (Fast.full ^^^ x5)
def z253 := x5 &&& (Fast.full ^^^ x2)
def z340 := x3 &&& x4
def z341 := x3 ||| x4
def z342 := x3 &&& (Fast.full ^^^ x4)
def z343 := x4 &&& (Fast.full ^^^ x3)
def z350 := x3 &&& x5
def z351 := x3 ||| x5
def z352 := x3 &&& (Fast.full ^^^ x5)
def z353 := x5 &&& (Fast.full ^^^ x3)
def z450 := x4 &&& x5
def z451 := x4 ||| x5
def z452 := x4 &&& (Fast.full ^^^ x5)
def z453 := x5 &&& (Fast.full ^^^ x4)
def n0 : List Nat := [z010,x2,x0,x3,x4,x1,x5]
def n1 : List Nat := [x2,x0,x3,x4,x1,z011,x5]
def n2 : List Nat := [x2,z012,x0,x3,x4,x1,x5]
def n3 : List Nat := [x2,x0,x3,x4,z013,x1,x5]
def n4 : List Nat := [z020,x2,x0,x3,x4,x1,x5]
def n5 : List Nat := [x2,x0,z021,x3,x4,x1,x5]
def n6 : List Nat := [x2,z022,x0,x3,x4,x1,x5]
def n7 : List Nat := [z023,x2,x0,x3,x4,x1,x5]
def n8 : List Nat := [z030,x2,x0,x3,x4,x1,x5]
def n9 : List Nat := [x2,x0,x3,z031,x4,x1,x5]
def n10 : List Nat := [x2,z032,x0,x3,x4,x1,x5]
def n11 : List Nat := [x2,x0,z033,x3,x4,x1,x5]
def n12 : List Nat := [x2,z040,x0,x3,x4,x1,x5]
def n13 : List Nat := [x2,x0,x3,x4,z041,x1,x5]
def n14 : List Nat := [z042,x2,x0,x3,x4,x1,x5]
def n15 : List Nat := [x2,x0,x3,z043,x4,x1,x5]
def n16 : List Nat := [z050,x2,x0,x3,x4,x1,x5]
def n17 : List Nat := [x2,x0,x3,x4,x1,x5,z051]
def n18 : List Nat := [x2,z052,x0,x3,x4,x1,x5]
def n19 : List Nat := [x2,x0,x3,x4,x1,z053,x5]
def n20 : List Nat := [z120,x2,x0,x3,x4,x1,x5]
def n21 : List Nat := [x2,x0,x3,x4,x1,z121,x5]
def n22 : List Nat := [x2,x0,x3,x4,z122,x1,x5]
def n23 : List Nat := [z123,x2,x0,x3,x4,x1,x5]
def n24 : List Nat := [z130,x2,x0,x3,x4,x1,x5]
def n25 : List Nat := [x2,x0,x3,x4,x1,z131,x5]
def n26 : List Nat := [x2,x0,x3,x4,z132,x1,x5]
def n27 : List Nat := [x2,x0,z133,x3,x4,x1,x5]
def n28 : List Nat := [z140,x2,x0,x3,x4,x1,x5]
def n29 : List Nat := [x2,x0,x3,x4,x1,z141,x5]
def n30 : List Nat := [x2,x0,x3,x4,z142,x1,x5]
def n31 : List Nat := [x2,x0,x3,z143,x4,x1,x5]
def n32 : List Nat := [x2,x0,x3,x4,z150,x1,x5]
def n33 : List Nat := [x2,x0,x3,x4,x5,z151]
def n34 : List Nat := [x2,x0,x3,x4,x1,x5,z151]
def n35 : List Nat := [z152,x2,x0,x3,x4,x5]
def n36 : List Nat := [z152,x2,x0,x3,x4,x1,x5]
def n37 : List Nat := [x2,x0,x3,x4,z153,x1,x5]
def n38 : List Nat := [z230,x2,x0,x3,x4,x1,x5]
def n39 : List Nat := [x2,x0,x3,z231,x4,x1,x5]
def n40 : List Nat := [z232,x2,x0,x3,x4,x1,x5]
def n41 : List Nat := [x2,x0,z233,x3,x4,x1,x5]
def n42 : List Nat := [z240,x2,x0,x3,x4,x1,x5]
def n43 : List Nat := [x2,x0,x3,x4,z241,x1,x5]
def n44 : List Nat := [z242,x2,x0,x3,x4,x1,x5]
def n45 : List Nat := [x2,x0,x3,z243,x4,x1,x5]
def n46 : List Nat := [z250,x2,x0,x3,x4,x1,x5]
def n47 : List Nat := [x2,x0,x3,x4,x1,x5,z251]
def n48 : List Nat := [z252,x2,x0,x3,x4,x1,x5]
def n49 : List Nat := [x2,x0,x3,x4,x1,z253,x5]
def n50 : List Nat := [x2,x0,z340,x3,x4,x1,x5]
def n51 : List Nat := [x2,x0,x3,x4,z341,x1,x5]
def n52 : List Nat := [x2,z342,x0,x3,x4,x1,x5]
def n53 : List Nat := [x2,x0,z343,x3,x4,x1,x5]
def n54 : List Nat := [z350,x2,x0,x3,x4,x1,x5]
def n55 : List Nat := [x2,x0,x3,x4,x1,x5,z351]
def n56 : List Nat := [x2,x0,z352,x3,x4,x1,x5]
def n57 : List Nat := [x2,x0,x3,x4,x1,z353,x5]
def n58 : List Nat := [z450,x2,x0,x3,x4,x1,x5]
def n59 : List Nat := [x2,x0,x3,x4,x1,x5,z451]
def n60 : List Nat := [x2,x0,x3,z452,x4,x1,x5]
def n61 : List Nat := [x2,x0,x3,x4,x1,z453,x5]
end Tokens
namespace Tokens
lemma valid_dead {xs : List W} (h : valid (Fast.enc xs) = true) : dead 7 xs := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  apply dead_leaf 7 xs (List.Nodup.of_map BitVec.toNat h.1)
  rw [←Fast.run_eq]
  simpa only [Fast.enc, List.length_map] using h.2
lemma link {ns ts : List Nat} {i j : Nat} (h : sliceOf ns ts i j = true)
    (e : endOf ns ts (i+j) = true) : endOf ns ts i = true :=
  scan_block ts (fun t => valid (child ns t)) i j h e
lemma finish (b : Nat) (ns ts : List Nat) (nd : (branchList.getD b []).Nodup)
    (out : branchList.getD b [] ≠ [goal] ∧ branchList.getD b [] ≠ [~~~goal])
    (cover : (candidates 7 (branchList.getD b [])).map Fast.enc = ts.map (child ns))
    (h : endOf ns ts 0 = true) : dead 8 (branchList.getD b []) := by
  apply dead_split 7 _ nd out
  intro c hc
  have mem : Fast.enc c ∈ (candidates 7 (branchList.getD b [])).map Fast.enc :=
    List.mem_map.mpr ⟨c,hc,rfl⟩
  rw [cover] at mem
  obtain ⟨t, ht, eq⟩ := List.mem_map.mp mem
  apply valid_dead
  rw [←eq]
  exact List.all_eq_true.mp h t ht
end Tokens
namespace Tokens
def bankID : Nat → List Nat
  | 0 => n0
  | 1 => n1
  | 2 => n2
  | 3 => n3
  | 4 => n4
  | 5 => n5
  | 6 => n6
  | 7 => n7
  | 8 => n8
  | 9 => n9
  | 10 => n10
  | 11 => n11
  | 12 => n12
  | 13 => n13
  | 14 => n14
  | 15 => n15
  | 16 => n16
  | 17 => n17
  | 18 => n18
  | 19 => n19
  | 20 => n20
  | 21 => n21
  | 22 => n22
  | 23 => n23
  | 24 => n24
  | 25 => n25
  | 26 => n26
  | 27 => n27
  | 28 => n28
  | 29 => n29
  | 30 => n30
  | 31 => n31
  | 32 => n32
  | 33 => n33
  | 34 => n34
  | 35 => n35
  | 36 => n36
  | 37 => n37
  | 38 => n38
  | 39 => n39
  | 40 => n40
  | 41 => n41
  | 42 => n42
  | 43 => n43
  | 44 => n44
  | 45 => n45
  | 46 => n46
  | 47 => n47
  | 48 => n48
  | 49 => n49
  | 50 => n50
  | 51 => n51
  | 52 => n52
  | 53 => n53
  | 54 => n54
  | 55 => n55
  | 56 => n56
  | 57 => n57
  | 58 => n58
  | 59 => n59
  | 60 => n60
  | 61 => n61
  | _ => []
def page0 : List Nat := [2,3,6,7,10,11,14,15,26,27,29,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63,77,78,79,82,83,86,87,90,91,94,95,99,103,107,111,115,119,123,127,131,135,139,143,147,151,155,159,163,167,171,175,179,183,187,191]
def page1 : List Nat := [195,199,203,207,213,214,215,227,231,235,239,243,247,251,255,259,263,267,271,275,279,283,287,291,295,299,303,307,311,315,319,323,326,327,330,331,335,515,519,523,527,531,535,539,543,547,551,555,559,563,565,567,571,573,575,577,579,581,583,585,587,589,591,595]
def page2 : List Nat := [599,603,607,611,614,615,618,619,623,627,630,631,634,635,639,649,651,654,655,667,675,679,683,687,691,695,699,703,707,709,711,715,717,719,721,723,725,727,729,731,733,735,739,743,747,751,753,755,759,761,763,767,769,771,773,775,777,779,781,783,787,791,795,799]
def page3 : List Nat := [819,822,823,826,827,831,834,835,838,839,842,843,846,847,1025,1027,1029,1031,1033,1035,1037,1039,1043,1047,1051,1055,1059,1063,1067,1071,1075,1079,1083,1087,1091,1095,1099,1103,1107,1111,1115,1119,1131,1134,1138,1139,1142,1143,1146,1147,1150,1151,1154,1155,1156,1157,1158,1159,1162,1163,1164,1165,1166,1167]
def page4 : List Nat := [1174,1186,1187,1190,1191,1194,1195,1198,1199,1203,1206,1207,1210,1211,1215,1219,1222,1223,1226,1227,1231,1245,1246,1247,1251,1255,1259,1263,1267,1271,1275,1279,1283,1287,1291,1295,1299,1303,1307,1311,1315,1319,1323,1327,1331,1335,1339,1343,1347,1350,1351,1354,1355,1359,1539,1543,1547,1551,1555,1559,1563,1567,1571,1575]
def page5 : List Nat := [1579,1583,1585,1587,1589,1591,1593,1595,1597,1599,1603,1605,1607,1611,1613,1615,1619,1623,1627,1631,1635,1639,1643,1647,1651,1655,1659,1663,1667,1699,1703,1707,1711,1715,1719,1723,1727,1729,1731,1733,1735,1737,1739,1741,1743,1747,1749,1751,1755,1757,1759,1763,1767,1771,1775,1777,1779,1781,1783,1785,1787,1789,1791,1793]
def page6 : List Nat := [1795,1799,1801,1803,1807,1811,1815,1819,1823,1842,1843,1846,1847,1850,1851,1854,1855,1859,1862,1863,1866,1867,1871,2059,2061,2062,2063,2077,2078,2079,2082,2083,2084,2085,2086,2087,2090,2091,2092,2093,2094,2095,2098,2099,2100,2101,2102,2103,2106,2107,2108,2109,2110,2111,2115,2116,2117,2118,2119,2123,2124,2125,2126,2127]
def page7 : List Nat := [2130,2131,2132,2133,2134,2135,2138,2139,2140,2141,2142,2143,2149,2150,2151,2163,2167,2171,2175,2179,2183,2187,2191,2195,2199,2203,2207,2211,2215,2219,2223,2227,2231,2235,2239,2243,2247,2251,2255,2275,2279,2283,2287,2291,2295,2299,2303,2307,2311,2315,2319,2323,2327,2331,2335,2339,2343,2347,2351,2355,2359,2363,2367,2371]
def page8 : List Nat := [2374,2375,2378,2379,2383,2569,2571,2574,2575,2587,2595,2598,2599,2602,2603,2607,2611,2615,2619,2623,2627,2631,2635,2639,2643,2646,2647,2650,2651,2655,2675,2679,2683,2687,2691,2694,2695,2698,2699,2703,2723,2726,2727,2730,2731,2735,2738,2739,2742,2743,2746,2747,2750,2751,2754,2755,2758,2759,2762,2763,2766,2767,2770,2771]
def page9 : List Nat := [2775,2778,2779,2783,2786,2787,2790,2791,2794,2795,2798,2799,2803,2807,2811,2815,2819,2823,2827,2831,2835,2839,2843,2847,2851,2855,2859,2863,2867,2871,2875,2879,2883,2886,2887,2890,2891,2895,3075,3077,3097,3098,3099,3107,3111,3115,3119,3123,3127,3131,3135,3139,3143,3147,3151,3155,3159,3163,3167,3182,3186,3187,3190,3191]
def page10 : List Nat := [3194,3195,3198,3199,3202,3203,3206,3207,3210,3211,3214,3215,3219,3222,3223,3227,3230,3231,3234,3235,3238,3239,3242,3243,3246,3247,3251,3255,3259,3263,3267,3270,3271,3274,3275,3279,3299,3302,3303,3306,3307,3311,3315,3319,3323,3327,3331,3335,3339,3343,3347,3351,3355,3359,3363,3367,3371,3375,3379,3383,3387,3391,3395,3398]
def page11 : List Nat := [3399,3402,3403,3407,3595,3618,3619,3622,3623,3626,3627,3630,3631,3634,3635,3638,3639,3642,3643,3646,3647,3651,3654,3655,3659,3662,3663,3666,3667,3670,3671,3674,3675,3678,3679,3699,3702,3703,3706,3707,3711,3715,3719,3723,3727,3731,3735,3739,3743,3747,3750,3751,3754,3755,3759,3763,3767,3771,3775,3779,3783,3787,3791,3811]
def page12 : List Nat := [3815,3819,3823,3827,3831,3835,3839,3843,3847,3851,3855,3859,3863,3867,3871,3875,3879,3883,3887,3891,3895,3899,3903,3907,3910,3911,3914,3915,3919,4099,4100,4101,4102,4103,4107,4108,4109,4110,4111,4123,4125,4126,4127,4141,4142,4143,4146,4147,4148,4149,4150,4151,4154,4155,4156,4157,4158,4159,4163,4164,4165,4166,4167,4171]
def page13 : List Nat := [4172,4173,4174,4175,4178,4179,4180,4181,4182,4183,4186,4187,4188,4189,4190,4191,4211,4215,4219,4223,4227,4231,4235,4239,4243,4247,4251,4255,4259,4263,4267,4271,4277,4278,4279,4291,4294,4295,4298,4299,4303,4323,4327,4331,4335,4339,4342,4343,4346,4347,4351,4355,4359,4363,4367,4371,4375,4379,4383,4387,4391,4395,4399,4403]
def page14 : List Nat := [4407,4411,4415,4419,4422,4423,4426,4427,4431,4627,4629,4631,4635,4637,4639,4641,4643,4647,4651,4653,4655,4659,4663,4667,4671,4675,4679,4683,4687,4691,4695,4699,4703,4713,4715,4718,4719,4731,4739,4743,4747,4751,4771,4774,4775,4778,4779,4783,4803,4807,4811,4815,4819,4823,4827,4831,4835,4838,4839,4842,4843,4847,4850,4851]
def page15 : List Nat := [4854,4855,4858,4859,4862,4863,4866,4867,4871,4874,4875,4879,4882,4883,4886,4887,4890,4891,4894,4895,4899,4903,4907,4911,4915,4919,4923,4927,4931,4934,4935,4938,4939,4943,5123,5125,5127,5129,5131,5135,5155,5159,5163,5167,5171,5175,5179,5183,5187,5191,5195,5199,5203,5207,5211,5215,5227,5230,5238,5250,5251,5254,5255,5258]
def page16 : List Nat := [5259,5262,5263,5267,5270,5271,5275,5278,5279,5282,5283,5286,5287,5290,5291,5294,5295,5309,5310,5311,5315,5319,5323,5327,5347,5350,5351,5354,5355,5359,5363,5366,5367,5370,5371,5375,5379,5383,5387,5391,5395,5399,5403,5407,5411,5415,5419,5423,5427,5431,5435,5439,5443,5446,5447,5450,5451,5455,5651,5653,5655,5657,5659,5663]
def page17 : List Nat := [5667,5669,5671,5675,5677,5679,5683,5687,5691,5695,5699,5703,5707,5711,5715,5719,5723,5727,5731,5763,5766,5767,5770,5771,5775,5795,5799,5803,5807,5826,5827,5830,5831,5834,5835,5838,5839,5843,5846,5847,5851,5854,5855,5858,5859,5862,5863,5866,5867,5870,5871,5875,5879,5883,5887,5891,5895,5899,5903,5907,5910,5911,5914,5915]
def page18 : List Nat := [5919,5923,5927,5931,5935,5939,5943,5947,5951,5955,5958,5959,5962,5963,5967,6147,6149,6151,6153,6155,6159,6179,6183,6187,6191,6195,6199,6203,6207,6211,6215,6219,6223,6227,6231,6235,6239,6251,6253,6254,6255,6259,6262,6263,6267,6270,6271,6285,6286,6287,6291,6294,6295,6299,6302,6303,6306,6307,6310,6311,6314,6315,6318,6319]
def page19 : List Nat := [6341,6342,6343,6371,6375,6379,6383,6387,6391,6395,6399,6403,6407,6411,6415,6419,6423,6427,6431,6435,6439,6443,6447,6451,6455,6459,6463,6467,6470,6471,6474,6475,6479,6675,6679,6683,6687,6691,6693,6695,6699,6701,6703,6705,6707,6711,6715,6717,6719,6723,6727,6731,6735,6739,6743,6747,6751,6777,6779,6782,6783,6795,6819,6822]
def page20 : List Nat := [6823,6826,6827,6831,6835,6837,6839,6843,6845,6847,6849,6851,6855,6859,6861,6863,6867,6871,6875,6879,6883,6887,6891,6895,6914,6915,6919,6923,6926,6927,6931,6934,6935,6938,6939,6943,6946,6947,6951,6954,6955,6959,6962,6963,6966,6967,6970,6971,6974,6975,6979,6982,6983,6986,6987,6991,7171,7174,7175,7179,7182,7183,7195,7198]
def page21 : List Nat := [7203,7206,7207,7211,7214,7215,7222,7235,7236,7237,7238,7239,7243,7244,7245,7246,7247,7250,7251,7254,7255,7258,7259,7262,7263,7283,7287,7291,7295,7299,7303,7307,7311,7315,7319,7323,7327,7331,7335,7339,7343,7373,7374,7375,7395,7398,7399,7402,7403,7407,7411,7415,7419,7423,7427,7431,7435,7439,7443,7447,7451,7455,7459,7463]
def page22 : List Nat := [7467,7471,7475,7479,7483,7487,7491,7494,7495,7498,7499,7503,7699,7703,7707,7711,7715,7717,7719,7721,7723,7727,7731,7733,7735,7739,7741,7743,7747,7751,7755,7759,7763,7767,7771,7775,7795,7843,7847,7851,7855,7859,7860,7861,7862,7863,7864,7865,7866,7867,7871,7875,7877,7879,7883,7885,7887,7891,7895,7899,7903,7907,7911,7915]
def page23 : List Nat := [7919,7939,7942,7943,7947,7950,7951,7954,7955,7958,7959,7962,7963,7966,7967,7970,7971,7975,7979,7982,7983,7987,7990,7991,7994,7995,7999,8003,8006,8007,8010,8011,8015,8195,8196,8197,8198,8199,8203,8204,8205,8206,8207,8219,8221,8222,8223,8227,8228,8229,8230,8231,8235,8236,8237,8238,8239,8243,8244,8245,8246,8247,8251,8252]
def page24 : List Nat := [8253,8254,8255,8259,8260,8261,8262,8263,8267,8268,8269,8270,8271,8285,8286,8287,8307,8311,8315,8319,8323,8327,8331,8335,8339,8343,8347,8351,8355,8359,8363,8367,8421,8422,8423,8435,8439,8443,8447,8451,8455,8459,8463,8467,8471,8475,8479,8483,8487,8491,8495,8499,8503,8507,8511,8515,8518,8519,8522,8523,8527,8723,8727,8731]
def page25 : List Nat := [8735,8739,8743,8747,8751,8755,8759,8763,8767,8771,8773,8775,8779,8781,8783,8785,8787,8791,8795,8797,8799,8857,8859,8862,8863,8875,8883,8887,8891,8895,8899,8903,8907,8911,8915,8917,8919,8923,8925,8927,8929,8931,8935,8939,8941,8943,8947,8951,8955,8959,8963,8967,8971,8975,8977,8979,8983,8987,8989,8991,8995,8998,8999,9002]
def page26 : List Nat := [9003,9007,9009,9011,9015,9019,9021,9023,9219,9221,9223,9225,9227,9231,9251,9255,9259,9263,9267,9271,9275,9279,9283,9287,9291,9295,9299,9303,9307,9311,9323,9326,9331,9334,9335,9339,9342,9343,9347,9350,9351,9355,9358,9359,9363,9366,9367,9371,9374,9375,9382,9453,9454,9455,9459,9463,9467,9471,9475,9479,9483,9487,9491,9495]
def page27 : List Nat := [9499,9503,9507,9511,9515,9519,9523,9527,9531,9535,9539,9542,9543,9546,9547,9551,9747,9751,9755,9759,9763,9767,9771,9775,9779,9783,9787,9791,9795,9797,9799,9801,9803,9807,9811,9813,9815,9819,9821,9823,9875,9907,9911,9915,9919,9923,9927,9931,9935,9939,9941,9943,9945,9947,9951,9955,9957,9959,9963,9965,9967,9971,9975,9979]
def page28 : List Nat := [9983,9987,9989,9991,9993,9995,9999,10003,10007,10011,10015,10019,10020,10021,10022,10023,10024,10025,10026,10027,10031,10035,10038,10039,10042,10043,10047,10251,10253,10254,10255,10259,10262,10263,10267,10270,10271,10274,10275,10278,10279,10282,10283,10286,10287,10290,10291,10294,10295,10298,10299,10302,10303,10317,10318,10319,10322,10323,10326,10327,10330,10331,10334,10335]
def page29 : List Nat := [10355,10359,10363,10367,10371,10375,10379,10383,10389,10390,10391,10403,10407,10411,10415,10483,10487,10491,10495,10499,10503,10507,10511,10515,10519,10523,10527,10531,10535,10539,10543,10547,10551,10555,10559,10563,10566,10567,10570,10571,10575,10771,10774,10775,10778,10779,10783,10787,10790,10791,10794,10795,10799,10809,10811,10814,10815,10827,10835,10839,10843,10847,10897,10899]
def page30 : List Nat := [10903,10907,10909,10911,10931,10935,10939,10943,10945,10947,10951,10953,10955,10959,10961,10963,10965,10967,10969,10971,10973,10975,10979,10983,10987,10991,10995,10997,10999,11003,11005,11007,11009,11011,11013,11015,11017,11019,11021,11023,11027,11031,11035,11039,11059,11062,11063,11066,11067,11071,11074,11075,11078,11079,11082,11083,11086,11087,11283,11287,11291,11295,11299,11303]
def page31 : List Nat := [11307,11311,11315,11317,11337,11338,11339,11347,11351,11355,11359,11395,11397,11399,11401,11403,11407,11443,11447,11451,11455,11457,11459,11461,11463,11465,11467,11469,11471,11473,11475,11479,11481,11483,11487,11491,11495,11499,11503,11505,11507,11509,11511,11513,11515,11517,11519,11523,11525,11527,11531,11533,11535,11539,11543,11547,11551,11566,11570,11571,11574,11575,11578,11579]
def page32 : List Nat := [11582,11583,11587,11590,11591,11594,11595,11599,11787,11795,11798,11799,11803,11806,11807,11810,11811,11812,11813,11814,11815,11818,11819,11820,11821,11822,11823,11826,11827,11830,11831,11834,11835,11838,11839,11858,11859,11862,11863,11866,11867,11870,11871,11891,11894,11895,11898,11899,11903,11907,11910,11911,11914,11915,11919,11939,11943,11947,11951,12019,12023,12027,12031,12035]
def page33 : List Nat := [12039,12043,12047,12051,12055,12059,12063,12067,12071,12075,12079,12083,12087,12091,12095,12099,12102,12103,12106,12107,12111,12291,12292,12293,12294,12295,12299,12300,12301,12302,12303,12307,12308,12309,12310,12311,12315,12316,12317,12318,12319,12331,12333,12334,12335,12338,12339,12340,12341,12342,12343,12346,12347,12348,12349,12350,12351,12365,12366,12367,12370,12371,12372,12373]
def page34 : List Nat := [12374,12375,12378,12379,12380,12381,12382,12383,12403,12405,12407,12411,12413,12415,12419,12423,12427,12431,12451,12455,12459,12463,12531,12535,12539,12543,12549,12550,12551,12563,12567,12571,12575,12577,12579,12583,12585,12587,12591,12595,12599,12603,12607,12611,12614,12615,12618,12619,12623,12819,12823,12827,12831,12835,12839,12843,12847,12865,12867,12871,12875,12877,12879,12883]
def page35 : List Nat := [12887,12891,12895,12945,12947,12951,12955,12957,12959,12979,12982,12983,12986,12987,12991,13001,13003,13006,13007,13019,13027,13031,13035,13039,13043,13047,13051,13055,13057,13059,13061,13063,13065,13067,13069,13071,13075,13079,13083,13087,13107,13110,13111,13114,13115,13119,13122,13123,13126,13127,13130,13131,13134,13135,13331,13333,13335,13339,13341,13343,13347,13351,13355,13359]
def page36 : List Nat := [13363,13365,13367,13369,13371,13375,13395,13399,13403,13407,13443,13445,13447,13449,13451,13455,13491,13495,13499,13503,13507,13509,13529,13530,13531,13539,13543,13547,13551,13553,13555,13557,13559,13561,13563,13565,13567,13571,13575,13579,13583,13587,13591,13595,13599,13614,13618,13619,13622,13623,13626,13627,13630,13631,13635,13638,13639,13642,13643,13647,13843,13845,13847,13849]
def page37 : List Nat := [13851,13855,13859,13863,13867,13871,13875,13879,13883,13887,13907,13911,13915,13919,13923,13925,13927,13929,13931,13935,14011,14018,14019,14022,14023,14026,14027,14030,14031,14050,14051,14054,14055,14058,14059,14062,14063,14067,14070,14071,14074,14075,14079,14099,14103,14107,14111,14113,14115,14119,14121,14123,14127,14131,14135,14139,14143,14147,14150,14151,14154,14155,14159,14339]
def page38 : List Nat := [14340,14341,14342,14343,14347,14348,14349,14350,14351,14355,14356,14357,14358,14359,14363,14364,14365,14366,14367,14371,14372,14373,14374,14375,14379,14380,14381,14382,14383,14395,14397,14398,14399,14413,14414,14415,14418,14419,14420,14421,14422,14423,14426,14427,14428,14429,14430,14431,14451,14455,14459,14463,14467,14471,14475,14479,14499,14503,14507,14511,14579,14583,14587,14591]
def page39 : List Nat := [14611,14615,14619,14623,14629,14630,14631,14643,14647,14651,14655,14659,14662,14663,14666,14667,14671,14867,14871,14875,14879,14883,14887,14891,14895,14913,14915,14919,14923,14925,14927,14931,14935,14939,14943,14993,14995,14999,15003,15005,15007,15027,15029,15031,15035,15037,15039,15057,15059,15063,15067,15069,15071,15075,15079,15083,15087,15097,15099,15102,15103,15115,15123,15127]
def page40 : List Nat := [15131,15135,15155,15158,15159,15162,15163,15167,15170,15171,15174,15175,15178,15179,15182,15183,15379,15383,15387,15391,15395,15399,15403,15407,15411,15413,15415,15417,15419,15423,15443,15447,15451,15455,15491,15493,15495,15497,15499,15503,15539,15543,15547,15551,15555,15557,15559,15561,15563,15567,15587,15591,15595,15599,15603,15605,15625,15626,15627,15635,15639,15643,15647,15662]
def page41 : List Nat := [15666,15667,15670,15671,15674,15675,15678,15679,15683,15686,15687,15690,15691,15695,15891,15895,15899,15903,15907,15909,15911,15913,15915,15919,15923,15927,15931,15935,15955,15959,15963,15967,15987,15989,15991,15993,15995,15999,16051,16053,16055,16057,16059,16063,16067,16069,16071,16075,16077,16079,16099,16103,16107,16111,16123,16146,16147,16150,16151,16154,16155,16158,16159,16179]
def page42 : List Nat := [16183,16187,16191,16195,16198,16199,16202,16203,16207,16403,16407,16411,16415,16419,16423,16427,16431,16435,16437,16439,16441,16443,16447,16467,16471,16475,16479,16515,16517,16519,16521,16523,16527,16563,16567,16571,16575,16579,16581,16583,16585,16587,16591,16611,16615,16619,16623,16627,16629,16631,16633,16635,16639,16659,16663,16667,16671,16683,16684,16685,16686,16687,16701,16702]
def page43 : List Nat := [16703,16709,16710,16711,16915,16919,16923,16927,16931,16935,16939,16943,16947,16951,16955,16959,16963,16967,16971,16975,17027,17031,17035,17039,17043,17047,17051,17055,17059,17061,17063,17067,17069,17071,17075,17079,17083,17087,17091,17093,17095,17099,17101,17103,17107,17111,17115,17119,17131,17134,17135,17427,17431,17435,17439,17443,17447,17451,17455,17475,17479,17483,17487,17489]
def page44 : List Nat := [17491,17495,17499,17501,17503,17569,17571,17575,17579,17581,17583,17587,17591,17595,17599,17619,17621,17623,17627,17629,17631,17633,17635,17639,17643,17645,17647,17667,17669,17671,17675,17677,17679,17681,17683,17687,17691,17693,17695,17705,17707,17710,17711,17723,17923,17927,17931,17935,17939,17943,17947,17951,17955,17959,17963,17967,17971,17975,17979,17983,17987,17990,18019,18023]
def page45 : List Nat := [18027,18031,18035,18039,18043,18047,18051,18055,18059,18063,18115,18119,18123,18127,18131,18135,18139,18143,18147,18151,18155,18159,18435,18438,18439,18443,18446,18447,18451,18454,18455,18459,18462,18463,18467,18470,18471,18475,18478,18479,18483,18486,18487,18491,18494,18495,18507,18510,18518,18547,18551,18555,18559,18563,18567,18571,18575,18595,18599,18603,18607,18675,18679,18683]
def page46 : List Nat := [18687,18707,18711,18715,18719,18739,18743,18747,18751,18765,18766,18767,18963,18967,18971,18975,18979,18983,18987,18991,18995,18997,18999,19001,19003,19007,19027,19031,19035,19039,19075,19077,19079,19081,19083,19087,19123,19127,19131,19135,19139,19141,19143,19145,19147,19151,19171,19173,19175,19179,19181,19183,19187,19189,19191,19193,19195,19199,19219,19221,19223,19227,19229,19231]
def page47 : List Nat := [19235,19467,19469,19470,19471,19475,19478,19479,19483,19486,19487,19501,19502,19503,19506,19507,19510,19511,19514,19515,19518,19519,19523,19526,19527,19531,19534,19535,19538,19539,19542,19543,19546,19547,19550,19551,19573,19574,19575,19587,19591,19595,19599,19619,19623,19627,19631,19699,19703,19707,19711,19731,19735,19739,19743,19763,19767,19771,19775,19993,19995,19998,19999,20011]
def page48 : List Nat := [20018,20019,20023,20027,20030,20031,20051,20054,20055,20058,20059,20063,20081,20083,20087,20091,20093,20095,20163,20166,20167,20170,20171,20175,20195,20198,20199,20202,20203,20207,20210,20211,20214,20215,20218,20219,20222,20223,20226,20227,20231,20234,20235,20239,20242,20243,20246,20247,20250,20251,20254,20255,20275,20279,20283,20287,20491,20494,20499,20502,20503,20507,20510,20511]
def page49 : List Nat := [20518,20530,20531,20534,20535,20538,20539,20542,20543,20547,20548,20549,20550,20551,20555,20556,20557,20558,20559,20562,20563,20566,20567,20570,20571,20574,20575,20605,20606,20607,20610,20611,20615,20619,20622,20623,20643,20646,20647,20650,20651,20655,20723,20727,20731,20735,20755,20759,20763,20767,20787,20791,20795,20799,21011,21043,21047,21051,21055,21075,21079,21083,21087,21091]
def page50 : List Nat := [21093,21095,21097,21099,21103,21186,21187,21188,21189,21190,21191,21194,21195,21196,21197,21198,21199,21203,21206,21207,21211,21214,21215,21218,21219,21222,21223,21226,21227,21230,21231,21235,21238,21239,21242,21243,21247,21267,21270,21271,21274,21275,21279,21299,21303,21307,21311,21515,21517,21518,21519,21523,21524,21525,21526,21527,21531,21532,21533,21534,21535,21539,21540,21541]
def page51 : List Nat := [21542,21543,21547,21548,21549,21550,21551,21565,21566,21567,21571,21572,21573,21574,21575,21579,21580,21581,21582,21583,21586,21587,21588,21589,21590,21591,21594,21595,21596,21597,21598,21599,21637,21638,21639,21667,21671,21675,21679,21747,21749,21751,21755,21757,21759,21779,21783,21787,21791,21811,21815,21819,21823,22057,22059,22062,22063,22075,22099,22102,22103,22106,22107,22111]
def page52 : List Nat := [22145,22147,22151,22155,22157,22159,22195,22199,22203,22207,22209,22211,22215,22219,22221,22223,22243,22247,22251,22255,22291,22294,22295,22298,22299,22303,22306,22307,22311,22314,22315,22319,22322,22323,22326,22327,22330,22331,22334,22335,22539,22542,22547,22550,22551,22555,22558,22559,22563,22566,22567,22571,22574,22575,22582,22595,22598,22599,22603,22606,22607,22610,22611,22614]
def page53 : List Nat := [22615,22618,22619,22622,22623,22669,22670,22671,22691,22694,22695,22698,22699,22703,22771,22773,22775,22779,22781,22783,22803,22807,22811,22815,22835,22839,22843,22847,23075,23123,23127,23131,23135,23155,23157,23159,23161,23163,23167,23219,23221,23223,23225,23227,23231,23235,23239,23243,23247,23267,23271,23275,23279,23299,23302,23303,23307,23310,23311,23314,23315,23318,23319,23322]
def page54 : List Nat := [23323,23326,23327,23347,23350,23351,23354,23355,23359,23563,23565,23566,23567,23571,23572,23573,23574,23575,23579,23580,23581,23582,23583,23587,23588,23589,23590,23591,23595,23596,23597,23598,23599,23603,23604,23605,23606,23607,23611,23612,23613,23614,23615,23619,23620,23621,23622,23623,23627,23628,23629,23630,23631,23645,23646,23647,23717,23718,23719,23795,23799,23803,23807,23827]
def page55 : List Nat := [23831,23835,23839,23859,23863,23867,23871,24137,24139,24142,24143,24155,24225,24227,24231,24235,24237,24239,24243,24247,24251,24255,24275,24279,24283,24287,24289,24291,24295,24299,24301,24303,24323,24325,24327,24331,24333,24335,24337,24339,24343,24347,24349,24351,24369,24371,24375,24379,24381,24383,24587,24590,24595,24598,24599,24603,24606,24607,24611,24614,24615,24619,24622,24623]
def page56 : List Nat := [24627,24630,24631,24635,24638,24639,24643,24646,24647,24651,24654,24655,24662,24749,24750,24751,24819,24823,24827,24831,24851,24855,24859,24863,24883,24887,24891,24895,25155,25235,25237,25239,25241,25243,25247,25267,25271,25275,25279,25299,25301,25303,25305,25307,25311,25315,25319,25323,25327,25347,25349,25351,25353,25355,25359,25363,25365,25367,25371,25373,25375,25379,25380,25381]
def page57 : List Nat := [25382,25383,25384,25385,25386,25387,25391,25619,25621,25623,25625,25627,25631,25699,25701,25703,25705,25707,25711,25787,25789,25790,25791,25805,25806,25807,25811,25814,25815,25819,25822,25823,25826,25827,25830,25831,25834,25835,25838,25839,25845,25846,25847,25875,25879,25883,25887,25907,25911,25915,25919,26161,26163,26167,26171,26173,26175,26241,26243,26247,26251,26253,26255,26297]
def page58 : List Nat := [26299,26302,26303,26315,26339,26342,26343,26346,26347,26351,26387,26390,26391,26394,26395,26399,26400,26401,26402,26403,26407,26408,26409,26410,26411,26415,26418,26419,26422,26423,26426,26427,26430,26431,26627,26628,26629,26630,26631,26632,26633,26634,26635,26639,26723,26726,26727,26731,26734,26735,26747,26750,26758,26771,26774,26775,26779,26782,26783,26786,26787,26790,26791,26794]
def page59 : List Nat := [26795,26798,26799,26877,26878,26879,26899,26902,26903,26906,26907,26911,26931,26935,26939,26943,27155,27157,27159,27161,27163,27167,27235,27236,27237,27238,27239,27240,27241,27242,27243,27247,27315,27347,27350,27351,27355,27358,27359,27362,27363,27366,27367,27370,27371,27374,27375,27411,27415,27419,27423,27443,27446,27447,27450,27451,27455,27651,27652,27653,27654,27655,27659,27660]
def page60 : List Nat := [27661,27662,27663,27667,27668,27669,27670,27671,27675,27676,27677,27678,27679,27691,27693,27694,27695,27699,27700,27701,27702,27703,27707,27708,27709,27710,27711,27715,27716,27717,27718,27719,27723,27724,27725,27726,27727,27741,27742,27743,27925,27926,27927,27955,27959,27963,27967,28241,28243,28247,28251,28253,28255,28321,28323,28327,28331,28333,28335,28377,28379,28382,28383,28395]
def page61 : List Nat := [28419,28423,28427,28431,28433,28435,28439,28443,28445,28447,28465,28467,28471,28475,28477,28479,28691,28693,28695,28697,28699,28703,28771,28773,28775,28777,28779,28783,28859,28862,28867,28870,28871,28875,28878,28879,28883,28886,28887,28891,28894,28895,28902,28957,28958,28959,28979,28983,28987,28991,29251,29253,29255,29257,29259,29263,29331,29333,29335,29337,29339,29343,29395,29443]
def page62 : List Nat := [29445,29447,29449,29451,29455,29459,29463,29467,29471,29475,29476,29477,29478,29479,29480,29481,29482,29483,29487,29699,29700,29701,29702,29703,29707,29708,29709,29710,29711,29715,29716,29717,29718,29719,29723,29724,29725,29726,29727,29731,29732,29733,29734,29735,29739,29740,29741,29742,29743,29755,29757,29758,29759,29763,29764,29765,29766,29767,29771,29772,29773,29774,29775,29789]
def page63 : List Nat := [29790,29791,30005,30006,30007,30289,30291,30295,30299,30301,30303,30369,30371,30375,30379,30381,30383,30433,30435,30439,30443,30445,30447,30473,30475,30478,30479,30491,30513,30515,30519,30523,30525,30527,30755,30757,30759,30761,30763,30767,30835,30837,30839,30841,30843,30847,30899,30901,30903,30905,30907,30911,30971,30974,30979,30982,30983,30987,30990,30991,30998,31037,31038,31039]
def page64 : List Nat := [31299,31301,31303,31305,31307,31311,31379,31381,31383,31385,31387,31391,31443,31445,31447,31449,31451,31455,31491,31523,31524,31525,31526,31527,31528,31529,31530,31531,31535]
def codePage : Nat → List Nat
  | 0 => page0
  | 1 => page1
  | 2 => page2
  | 3 => page3
  | 4 => page4
  | 5 => page5
  | 6 => page6
  | 7 => page7
  | 8 => page8
  | 9 => page9
  | 10 => page10
  | 11 => page11
  | 12 => page12
  | 13 => page13
  | 14 => page14
  | 15 => page15
  | 16 => page16
  | 17 => page17
  | 18 => page18
  | 19 => page19
  | 20 => page20
  | 21 => page21
  | 22 => page22
  | 23 => page23
  | 24 => page24
  | 25 => page25
  | 26 => page26
  | 27 => page27
  | 28 => page28
  | 29 => page29
  | 30 => page30
  | 31 => page31
  | 32 => page32
  | 33 => page33
  | 34 => page34
  | 35 => page35
  | 36 => page36
  | 37 => page37
  | 38 => page38
  | 39 => page39
  | 40 => page40
  | 41 => page41
  | 42 => page42
  | 43 => page43
  | 44 => page44
  | 45 => page45
  | 46 => page46
  | 47 => page47
  | 48 => page48
  | 49 => page49
  | 50 => page50
  | 51 => page51
  | 52 => page52
  | 53 => page53
  | 54 => page54
  | 55 => page55
  | 56 => page56
  | 57 => page57
  | 58 => page58
  | 59 => page59
  | 60 => page60
  | 61 => page61
  | 62 => page62
  | 63 => page63
  | 64 => page64
  | _ => []
def witness (i : Nat) : List Nat :=
  let t := (codePage (i/64)).getD (i%64) 0
  child (bankID (t/512)) (t%512)
def ids0 : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,8,9,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,10,12,29,31,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100]
def ids1 : List Nat := [101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,68,69,70,143,144,145,146,8,147,30,145,146,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,8,147,11,143,144,192,193,194,195,196,197,198,199,200,201,202,203,204,205]
def ids2 : List Nat := [206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,8,234,10,235,12,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,8,234,143,256,144,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,10,12,143,144,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309]
def ids3 : List Nat := [310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,8,348,256,145,146,29,31,145,146,277,278,279,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,8,348,29,235,31,393,394,395,396,397,398,399,400,401,402,403,404,405,406]
def ids4 : List Nat := [8,407,408,409,410,8,407,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,0,438,439,440,441,442,206,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,408,410,411,413,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,40,101,214,310,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516]
def ids5 : List Nat := [460,461,462,517,518,519,520,8,521,412,519,520,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,8,521,409,517,518,542,543,544,545,546,547,548,549,550,551,41,102,215,311,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,121,576,577,578,328,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613]
def ids6 : List Nat := [8,614,615,519,520,411,413,519,520,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,8,614,411,635,413,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,4,652,653,654,212,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,43,104,217,313,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707]
def ids7 : List Nat := [8,708,408,635,410,8,708,517,615,518,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,322,725,726,727,123,728,729,730,731,732,733,734,735,736,737,738,408,410,517,518,616,617,618,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,42,103,216,312,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796]
def ids8 : List Nat := [414,797,798,799,800,801,636,802,803,804,805,806,8,807,808,809,810,8,807,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,13,826,827,828,829,830,236,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,479,542,759,666,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,808,810,811,813,867,868,869,870,871,872,60,131,265,340,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904]
def ids9 : List Nat := [480,543,760,667,905,906,907,908,909,910,911,912,560,913,713,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,864,865,866,929,930,931,932,8,933,812,931,932,934,935,936,937,61,132,133,266,267,341,938,939,940,941,942,943,8,933,809,929,930,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,164,968,969,970,363,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993]
def ids10 : List Nat := [420,994,995,996,997,998,640,999,481,544,761,668,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,8,1016,808,1017,810,8,1016,929,1018,930,1019,1020,1021,1022,1023,1024,1025,1026,17,1027,1028,1029,240,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,808,810,929,930,1041,1042,1043,1044,1045,1046,1047,62,134,135,268,269,342,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081]
def ids11 : List Nat := [482,545,762,669,709,1082,1083,1084,1085,1086,564,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,8,1106,1018,931,932,811,813,931,932,1041,1042,1043,1107,1108,1109,1110,1111,1112,63,136,270,343,1113,1114,1115,1116,8,1106,811,1017,813,1117,1118,1119,1120,1121,1122,1123,1124,357,1125,1126,1127,166,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166]
def ids12 : List Nat := [426,1167,1168,1169,1170,1171,644,1172,483,546,763,670,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,8,1189,1190,1191,1192,814,1193,1194,1195,1019,1196,1197,1198,8,1189,1199,1200,1201,21,1202,1203,1204,244,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,867,934,1044,1107,1216,1217,1218,1190,1192,1199,1201,64,137,271,344,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248]
def ids13 : List Nat := [484,547,548,764,671,672,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,568,1261,721,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,868,869,935,1045,1108,1109,1216,1217,1218,1273,1274,1275,1276,8,1277,1200,1275,1276,65,138,139,272,273,345,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,960,1292,1121,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,8,1277,1191,1273,1274,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,182,1318,1319,1320,381,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335]
def ids14 : List Nat := [432,1336,1337,1338,648,1339,1340,1341,8,1342,1190,1343,1192,820,1344,1345,1346,1023,1347,1348,1349,8,1342,1273,1350,1274,25,1351,1352,1353,1354,1355,250,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,485,549,550,765,673,674,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,870,871,936,1046,1110,1111,1190,1192,1273,1274,1385,1386,1387,66,140,141,274,275,346,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419]
def ids15 : List Nat := [486,551,766,675,1420,1421,1422,1423,717,1424,1425,1426,1427,1428,572,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,872,937,1047,1112,8,1444,1350,1275,1276,1199,1201,1275,1276,1385,1386,1387,67,142,276,347,1445,1446,1447,1448,1117,1449,1450,1451,1452,1453,1454,1455,1456,1457,964,1458,1459,1460,1461,1462,1463,1464,1465,1466,1467,1468,1469,1470,1471,1472,8,1444,1199,1343,1201,375,1473,1474,1475,184,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504]
def ids16 : List Nat := [448,1505,1506,1507,1508,1509,658,1510,1511,1512,1513,1514,8,1515,1516,1517,1518,836,1519,1520,1521,1522,1523,1033,1524,1525,1526,1527,1528,1208,1529,1530,1531,1532,1533,1361,1534,1535,1536,1537,1538,32,1539,1540,1541,1542,1543,257,1544,1545,1546,1547,1548,8,1515,1549,1550,1551,487,552,767,676,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,873,938,1048,1113,1219,1278,1388,1445,71,148,280,349,1568,1569,1570,1516,1518,1549,1551,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596]
def ids17 : List Nat := [488,553,554,768,677,678,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,582,1617,735,1618,1619,1620,874,939,940,1049,1050,1114,1220,1279,1280,1389,1390,1446,72,149,281,350,1568,1569,1570,1621,1622,1623,1624,8,1625,1550,1623,1624,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,974,1642,1135,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1324,1656,1483,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,200,1668,397,1669,1670,1671,8,1625,1517,1621,1622]
def ids18 : List Nat := [454,1672,1673,1674,1675,1676,662,1677,489,555,556,769,679,680,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,8,1694,1516,1695,1518,842,1696,1697,1698,1037,1699,1700,1701,1212,1702,1703,1704,1365,1705,1706,1707,36,1708,1709,1710,261,1711,1712,1713,8,1694,1621,1714,1622,875,941,942,1051,1052,1115,1221,1281,1282,1391,1392,1447,73,150,282,351,1516,1518,1621,1622,1715,1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743]
def ids19 : List Nat := [490,557,770,681,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,731,1756,1757,1758,1759,1760,586,1761,1762,1763,1764,1765,1766,1767,876,943,1053,1116,1222,1283,1393,1448,74,151,283,352,8,1768,1714,1623,1624,1549,1551,1623,1624,1715,1716,1717,1769,1770,1771,1772,1773,1774,1775,1776,1131,1777,1778,1779,1780,1781,978,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1479,1793,1794,1795,1796,1797,1328,1798,1799,1800,1801,1802,393,1803,1804,1805,1806,1807,1808,1809,1810,1811,204,1812,1813,1814,1815,1816,1817,1818,8,1768,1549,1695,1551]
def ids20 : List Nat := [8,1819,1820,1821,1822,0,1823,1824,1825,322,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,8,1819,1845,1846,1847,1848,1849,1850,1851,1852,1853,1854,1855,471,532,749,627,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1820,1822,1845,1847,1867,1868,1869,1870,856,921,1008,1098,1181,1265,1377,1436,52,113,226,330,1560,1605,1686,1752,1871,1872,1873,1874,1875,1876,1877,1878,1879,1880,1881,1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893,1894,1895,1896]
def ids21 : List Nat := [472,533,750,628,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906,1907,1908,1864,1865,1866,1909,1910,1911,1912,8,1913,1846,1911,1912,1914,1915,1916,1917,857,922,1009,1099,1182,1266,1378,1437,53,114,115,227,331,332,1918,1919,121,1920,212,1921,1922,1923,1561,1606,1687,1753,1924,1925,1926,1927,1928,1929,1930,1931,1932,1933,1934,1935,1936,1937,1938,1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,8,1913,1821,1909,1910,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977]
def ids22 : List Nat := [474,535,752,630,1978,1979,1980,1981,1982,1983,1984,1985,8,1986,1987,1911,1912,1845,1847,1911,1912,1988,1989,1990,1991,1992,1993,1994,859,924,1011,1101,1184,1268,1380,1439,4,1995,1996,1997,1998,1999,328,2000,55,117,118,229,334,335,1563,1608,1689,1755,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,8,1986,1845,2041,1847,2042,2043,2044,2045,2046,2047,2048,2049,2050,2051,2052,2053,2054,2055]
def ids23 : List Nat := [8,2056,1820,2041,1822,206,2057,2058,2059,123,2060,2061,2062,2063,2064,2065,2066,2067,2068,2069,2070,2071,2072,2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,8,2056,1909,1987,1910,2083,2084,2085,2086,2087,2088,2089,2090,473,534,751,629,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,1820,1822,1909,1910,1988,1989,1990,2103,2104,2105,2106,858,923,1010,1100,1183,1267,1379,1438,54,116,228,333,1562,1607,1688,1754,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119,2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132]
def ids24 : List Nat := [1829,2133,2134,2135,2136,2137,2005,2138,2139,2140,2141,2142,13,2143,2144,2145,2146,2147,357,2148,2149,2150,2151,2152,8,2153,2154,2155,2156,2157,2158,2159,2160,2161,2162,2163,2164,2165,2166,2167,2168,8,2153,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,495,592,775,686,2184,2185,2186,2187,2188,2189,2190,2191,2192,2193,1875,1928,1929,2111,2013,2014,2194,2195,2196,2197,883,948,1060,1143,1227,1296,1398,1465,79,156,288,365,1575,1630,1722,1773,2198,2199,2200,2201,2202,2203,2204,2154,2156,2169,2171,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224]
def ids25 : List Nat := [496,593,776,687,2225,2226,2227,2228,2229,2230,2231,2232,1876,1930,2112,2015,2233,2234,1936,2235,2069,2236,2237,2238,2239,2240,2241,2242,884,949,1061,1144,1228,1297,1399,1466,80,157,158,289,366,367,2243,2244,164,2245,240,2246,2247,2248,1576,1631,1723,1774,2249,2250,2251,2252,2253,2254,2202,2203,2204,2255,2256,2257,2258,8,2259,2170,2257,2258,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,8,2259,2155,2255,2256,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,2291,2292,2293]
def ids26 : List Nat := [498,595,778,689,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,1833,2304,2305,2306,2307,2308,2011,2309,1878,1933,2114,2018,2310,2311,2312,2313,886,951,1063,1146,1230,1299,1401,1468,17,2314,2315,2316,2317,2318,363,2319,82,160,161,291,369,370,1578,1633,1725,1776,2320,2321,2322,2323,8,2324,2325,2257,2258,2169,2171,2257,2258,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,8,2324,2169,2349,2171,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363]
def ids27 : List Nat := [497,594,777,688,2063,2364,2365,2366,2367,2368,1938,2369,2370,2371,2372,2373,2374,2375,2376,2377,1877,1931,1932,2113,2016,2017,2378,2379,2380,2381,236,2382,2383,2384,2385,2386,166,2387,885,950,1062,1145,1229,1298,1400,1467,81,159,290,368,1577,1632,1724,1775,8,2388,2154,2349,2156,2389,2390,2391,2392,2393,2394,2395,2396,8,2388,2255,2325,2256,2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2154,2156,2255,2256,2326,2327,2328,2411,2412,2413,2414,2415,2416,2417,2418,2419,2420,2421,2422,2423,2424,2425,2426,2427,2428,2429,2430]
def ids28 : List Nat := [1837,2431,2432,2433,2434,2435,2023,2436,2437,2438,2439,2440,21,2441,2442,2443,2444,2445,375,2446,2447,2448,2449,2450,2157,2451,2452,2453,2454,2455,2333,2456,2457,2458,2459,2460,8,2461,2462,2463,2464,8,2461,2465,2466,2467,2468,2469,2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,503,600,783,694,2480,2481,2482,2483,2484,2485,2486,2487,1883,1946,2119,2031,2488,2489,2490,2491,891,980,1068,1153,1235,1304,1305,1406,1487,1488,87,174,175,296,383,384,1583,1646,1730,1789,2492,2493,2494,2495,2209,2210,2264,2415,2416,2341,2496,2497,2498,2499,2500,2501,2502,2462,2464,2465,2467,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512]
def ids29 : List Nat := [504,601,784,695,2513,2514,2515,2516,2517,2518,2519,2520,1884,1947,1948,2120,2032,2033,2521,2522,1954,2523,2079,2524,2525,2526,2527,2528,2529,2530,892,981,1069,1154,1236,1306,1407,1489,88,176,297,385,2531,2532,182,2533,250,2534,2535,2536,1584,1647,1731,1790,2537,2538,2539,2540,2541,2542,2211,2265,2417,2342,2543,2544,2270,2545,2393,2546,2547,2548,2549,2550,2551,2552,2500,2501,2502,2553,2554,2555,2556,8,2557,2466,2555,2556,2558,2559,2560,2561,8,2557,2463,2553,2554,2562,2563,2564,2565,2566,2567,2568,2569,2570,2571,2572,2573,2574,2575]
def ids30 : List Nat := [506,603,786,697,2576,2577,2578,2579,2580,2581,2582,2583,1841,2584,2585,2586,2587,2588,2029,2589,1886,1950,1951,2122,2035,2036,2590,2591,2592,2593,894,983,1071,1156,1238,1308,1309,1409,1491,1492,25,2594,2595,2596,2597,2598,381,2599,90,179,299,388,1586,1649,1733,1792,2600,2601,2602,2603,2163,2604,2605,2606,2607,2608,2339,2609,2214,2267,2420,2344,2610,2611,2612,2613,8,2614,2615,2555,2556,2465,2467,2555,2556,2616,2617,2618,2619,2620,2621,2622,8,2614,2465,2623,2467,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637]
def ids31 : List Nat := [505,602,785,696,2638,2639,2640,2641,2075,2642,2643,2644,2645,2646,1956,2647,2648,2649,2650,2651,1885,1949,2121,2034,2652,2653,2654,2655,893,982,1070,1155,244,2656,2657,2658,2659,2660,184,2661,1237,1307,1408,1490,89,177,178,298,386,387,1585,1648,1732,1791,2389,2662,2663,2664,2665,2666,2272,2667,2668,2669,2670,2671,2672,2673,2212,2213,2266,2418,2419,2343,2674,2675,2676,2677,8,2678,2462,2623,2464,8,2678,2553,2615,2554,2679,2680,2681,2682,2683,2684,2685,2686,2462,2464,2553,2554,2616,2617,2618,2687,2688,2689,2690,2691,2692,2693,2694,2695,2696]
def ids32 : List Nat := [511,608,791,702,2697,2698,2699,2700,2701,2702,2703,2704,1848,2705,2706,2707,2708,2709,2042,2710,1891,1964,2127,2050,2711,2712,2713,2714,899,988,1076,1161,1243,1330,1414,1499,32,2715,2716,2717,2718,2719,393,2720,95,192,304,401,1591,1660,1738,1813,2721,2722,2723,2724,2172,2725,2726,2727,2728,2729,2350,2730,2219,2280,2425,2358,2731,2732,2733,2734,2468,2735,2736,2737,2738,2739,2624,2740,2507,2562,2691,2632,2741,2742,2743,2744,8,2745,2746,2747,2748,2749,8,2745,2750,2751,2752,2753,2754,2755,2747,2749,2750,2752]
def ids33 : List Nat := [512,609,792,703,2756,2757,2758,2759,2760,2761,2762,2763,2764,2765,2766,2767,2768,2769,2770,2771,900,989,1077,1162,1244,1331,1415,1500,1592,1661,1739,1814,2772,2773,2774,2775,2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791,2792,2793,2794,2795,2796,2797,2798,2799,2800,2746,2801,2802]
def ids34 : List Nat := [513,610,793,704,2803,2804,2805,2806,2807,2808,2809,2810,1892,1893,1965,1966,2128,2129,2051,2052,2811,2812,2813,2814,2815,2816,1972,2817,2087,2818,2819,2820,901,990,1078,1163,1245,1332,1416,1501,96,97,193,194,305,306,402,403,1593,1662,1740,1815,2821,2822,200,2823,261,2824,2825,2826,2827,2828,2829,2830,2220,2221,2281,2282,2426,2427,2359,2360,2831,2832,2833,2834,2835,2836,2837,2838,2288,2839,2401,2840,2841,2842,2508,2509,2563,2564,2692,2693,2633,2634,2843,2844,2845,2846,2847,2848,2849,2850,2570,2851,2683,2852,2853,2854,2753,2754,2755,2801,2855,2802,2856,2857,2858,8,2800,2859,2751,2857,2858,8,2859,2748,2855,2856]
def ids35 : List Nat := [2860,2861,2862,2863,2864,2865,2866,2867,2868,2869,2870,2871,2872,2873,2874,2875,2876,2801,2877,2802,514,611,794,705,2878,2879,2880,2881,2882,2883,2884,2885,2886,2887,2888,2889,902,991,1079,1164,1246,1333,1417,1502,1594,1663,1741,1816,2890,2891,2892,2893,2894,2895,2896,2897,2898,2899,2900,2901]
def ids36 : List Nat := [1852,2902,2903,2904,2046,2905,2906,2907,36,2908,2909,2910,397,2911,2912,2913,2178,2914,2915,2916,2354,2917,2918,2919,2474,2920,2921,2922,2628,2923,2924,2925,2876,8,2926,2747,2927,2749,8,2926,2855,2928,2856,515,612,795,706,2929,2930,2931,2932,2933,2934,2935,2936,1894,1895,1967,1968,2130,2131,2053,2054,2937,2938,2939,2940,903,992,1080,1165,1247,1334,1418,1503,98,99,195,196,307,308,404,405,1595,1664,1742,1817,2941,2942,2943,2944,2222,2223,2283,2284,2428,2429,2361,2362,2945,2946,2947,2948,2510,2511,2565,2566,2694,2695,2635,2636,2949,2950,2951,2952,2747,2749,2801,2855,2802,2856,2953,2954,2955]
def ids37 : List Nat := [516,613,796,707,2956,2957,2958,2959,2960,2961,2962,2963,2083,2964,2965,2966,2967,2968,1976,2969,1896,1969,2132,2055,2970,2971,2972,2973,904,993,1081,1166,1248,1335,1419,1504,257,2974,2975,2976,2977,2978,204,2979,100,197,309,406,1596,1665,1743,1818,2980,2981,2982,2983,2397,2984,2985,2986,2987,2988,2292,2989,2224,2285,2430,2363,2990,2991,2992,2993,2994,2995,2679,2996,2997,2998,2999,3000,2574,3001,2512,2567,2696,2637,3002,3003,3004,3005,3006,3007,8,3008,2877,2857,2928,2858,8,3008,2750,2927,2752,2750,2752,2857,2858,2953,2954,2955]
def ids38 : List Nat := [8,3009,3010,3011,3012,414,3013,3014,3015,709,3016,3017,3018,8,3009,3019,3020,3021,3022,3023,3024,3025,3026,3027,3028,3029,1829,3030,3031,3032,2063,3033,3034,3035,3036,3037,3038,3039,3040,3041,3042,3043,463,522,739,619,3044,3045,3046,3010,3012,3019,3021,3047,3048,3049,3050,1856,1897,2091,1978,3051,3052,3053,3054,848,905,1000,1088,1173,1249,1369,1420,44,105,218,314,1552,1597,1678,1744,3055,3056,3057,3058,2184,2225,2370,2294,3059,3060,3061,3062,2480,2513,2638,2576,3063,3064,3065,3066,2697,2756,2803,2878,2929,2956]
def ids39 : List Nat := [464,523,524,740,741,620,3044,3045,3046,3067,3068,3069,3070,8,3071,3020,3069,3070,3072,3073,3074,3075,3076,3077,1857,1898,1899,2092,2093,1979,3078,3079,3080,3081,3082,3083,849,906,907,1001,1089,1090,3084,3085,560,3086,640,3087,3088,3089,1174,1250,1370,1421,45,106,219,315,1553,1598,1679,1745,8,3071,3011,3067,3068,3090,3091,3092,3093,3094,3095,2185,2186,2226,2371,2295,2296,3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,1936,3112,3113,3114,2011,3115,3116,3117,3118,3119,3120,3121,3122,3123,2481,2514,2639,2577,3124,3125,3126,3127,2698,2757,2804,2879,2930,2957]
def ids40 : List Nat := [8,3128,3010,3129,3012,420,3130,3131,3132,713,3133,3134,3135,8,3128,3067,3136,3068,3137,3138,3139,3140,3141,3142,3143,3144,1833,3145,3146,3147,3148,3149,2069,3150,3151,3152,3153,3154,3155,3156,3157,3158,3159,3160,3161,3162,465,525,526,742,743,621,3010,3012,3067,3068,3163,3164,3165,3166,3167,3168,3169,3170,3171,1858,1900,1901,2094,2095,1980,3172,3173,3174,3175,3176,3177,850,908,1002,1091,1175,1251,1371,1422,46,107,220,316,1554,1599,1680,1746,3178,3179,3180,3181,2187,2227,2372,2297,3182,3183,3184,3185,2482,2515,2640,2578,3186,3187,3188,3189,2699,2758,2805,2880,2931,2958]
def ids41 : List Nat := [466,527,744,622,8,3190,3136,3069,3070,3019,3021,3069,3070,3163,3164,3165,3191,3192,3193,3194,1859,1902,2096,1981,3195,3196,3197,3198,636,3199,3200,3201,3202,3203,564,3204,851,909,910,1003,1092,1093,1176,1252,1372,1423,47,108,221,317,1555,1600,1681,1747,8,3190,3019,3129,3021,3205,3206,3207,3208,3209,3210,3211,3212,3213,3214,3215,3216,2005,3217,3218,3219,1938,3220,3221,3222,3223,3224,3225,3226,3227,3228,3229,3230,3231,3232,3233,3234,3235,3236,2188,2189,2228,2373,2298,2299,3237,3238,3239,3240,3241,3242,2483,2516,2641,2579,3243,3244,3245,3246,2700,2759,2806,2881,2932,2959]
def ids42 : List Nat := [8,3247,3248,3249,3250,426,3251,3252,3253,3254,3255,717,3256,3257,3258,3259,3260,3022,3261,3262,3263,3264,3265,3137,3266,3267,3268,3269,3270,8,3247,3271,3272,3273,1837,3274,3275,3276,3277,3278,2075,3279,3280,3281,3282,3283,3284,3285,3286,3287,3288,3289,3290,3291,3292,3293,3294,3295,467,528,745,623,3047,3072,3073,3166,3167,3191,3296,3297,3298,3248,3250,3271,3273,1860,1903,2097,1982,3299,3300,3301,3302,852,917,1004,1094,1177,1253,1373,1430,48,109,222,318,1556,1601,1682,1748,3303,3304,3305,3306,3307,3308,2190,2229,2374,2300,3309,3310,3311,3312,2484,2517,2648,2580,3313,3314,3315,3316,2701,2760,2807,2882,2933,2960]
def ids43 : List Nat := [468,529,746,624,3048,3074,3168,3192,3296,3297,3298,3317,3318,3319,3320,8,3321,3272,3319,3320,1861,1904,1905,2098,2099,1983,3322,3323,3324,3325,3326,3327,853,918,1005,1095,1178,1254,1255,1374,1431,1432,3328,3329,568,3330,648,3331,3332,3333,49,110,223,319,1557,1602,1683,1749,3334,3335,3336,3337,3338,3339,3104,3340,3211,3341,3342,3343,2191,2230,2375,2301,3344,3345,3346,3347,8,3321,3249,3317,3318,2485,2518,2649,2581,3348,3349,3350,3351,3352,3353,3354,3355,1954,3356,3357,3358,2029,3359,3360,3361,3362,3363,3364,3365,3366,3367,2702,2761,2808,2883,2934,2961]
def ids44 : List Nat := [8,3368,3248,3369,3250,432,3370,3371,3372,721,3373,3374,3375,3026,3376,3377,3378,3141,3379,3380,3381,8,3368,3317,3382,3318,1841,3383,3384,3385,2079,3386,3387,3388,3389,3390,3391,3392,3393,3394,3395,3396,469,530,747,625,3049,3075,3169,3193,3248,3250,3317,3318,3397,3398,3399,1862,1906,1907,2100,2101,1984,3400,3401,3402,3403,3404,3405,854,919,1006,1096,1179,1256,1375,1433,50,111,224,320,1558,1603,1684,1750,3406,3407,3408,3409,3410,3411,2192,2231,2376,2302,3412,3413,3414,3415,2486,2519,2650,2582,3416,3417,3418,3419,2703,2762,2809,2884,2935,2962]
def ids45 : List Nat := [470,531,748,626,3050,3076,3077,3170,3171,3194,8,3420,3382,3319,3320,3271,3273,3319,3320,3397,3398,3399,1863,1908,2102,1985,3421,3422,3423,3424,855,920,1007,1097,644,3425,3426,3427,3428,3429,572,3430,1180,1257,1258,1376,1434,1435,51,112,225,321,1559,1604,1685,1751,3205,3431,3432,3433,3434,3435,3108,3436,3437,3438,3439,3440,2193,2232,2377,2303,3441,3442,3443,3444,8,3420,3271,3369,3273,2023,3445,3446,3447,1956,3448,3449,3450,3451,3452,3453,3454,3455,3456,3457,3458,2487,2520,2651,2583,3459,3460,3461,3462,3463,3464,2704,2763,2810,2885,2936,2963]
def ids46 : List Nat := [8,3465,3466,3467,3468,448,3469,3470,3471,3472,3473,731,3474,3475,3476,3477,3478,3036,3479,3480,3481,3482,3483,3155,3484,3485,3486,3487,3488,3284,3489,3490,3491,3492,3493,3389,3494,3495,3496,3497,3498,1848,3499,3500,3501,3502,3503,2083,3504,3505,3506,3507,3508,8,3465,3509,3510,3511,475,536,753,631,3051,3078,3172,3195,3299,3322,3400,3421,1867,1914,2103,1991,3512,3513,3514,3466,3468,3509,3511,860,925,1012,1102,1185,1269,1381,1440,56,127,230,336,1564,1609,1690,1762,3515,3516,3517,3518,2194,2239,2378,2310,3519,3520,3521,3522,2488,2527,2652,2590,3523,3524,3525,3526,2711,2764,2811,2886,2937,2970]
def ids47 : List Nat := [476,537,538,754,755,632,3052,3079,3080,3173,3174,3196,3300,3323,3324,3401,3402,3422,1868,1915,2104,1992,3512,3513,3514,3527,3528,3529,3530,8,3531,3510,3529,3530,861,926,1013,1103,1186,1270,1382,1441,57,128,231,337,1565,1610,1611,1691,1763,1764,3532,3533,582,3534,662,3535,3536,3537,3538,3539,3540,3541,2195,2240,2379,2311,3542,3543,3544,3545,3546,3547,3118,3548,3227,3549,3550,3551,2489,2528,2653,2591,3552,3553,3554,3555,3556,3557,3558,3559,3362,3560,3455,3561,3562,3563,2712,2765,2812,2887,2938,2971,3564,3565,1972,3566,2046,3567,3568,3569,8,3531,3467,3527,3528]
def ids48 : List Nat := [8,3570,3466,3571,3468,454,3572,3573,3574,735,3575,3576,3577,3040,3578,3579,3580,3159,3581,3582,3583,3290,3584,3585,3586,3393,3587,3588,3589,1852,3590,3591,3592,2087,3593,3594,3595,8,3570,3527,3596,3528,477,539,540,756,757,633,3053,3081,3082,3175,3176,3197,3301,3325,3326,3403,3404,3423,1869,1916,2105,1993,3466,3468,3527,3528,3597,3598,3599,862,927,1014,1104,1187,1271,1383,1442,58,129,232,338,1566,1612,1692,1765,3600,3601,3602,3603,2196,2241,2380,2312,3604,3605,3606,3607,2490,2529,2654,2592,3608,3609,3610,3611,2713,2766,2813,2888,2939,2972]
def ids49 : List Nat := [478,541,758,634,3054,3083,3177,3198,3302,3327,3405,3424,1870,1917,2106,1994,8,3612,3596,3529,3530,3509,3511,3529,3530,3597,3598,3599,863,928,1015,1105,1188,1272,1384,1443,59,130,233,339,658,3613,3614,3615,3616,3617,586,3618,1567,1613,1614,1693,1766,1767,3619,3620,3621,3622,2197,2242,2381,2313,3223,3623,3624,3625,3626,3627,3122,3628,3629,3630,3631,3632,2491,2530,2655,2593,3451,3633,3634,3635,3636,3637,3366,3638,3639,3640,3641,3642,3643,3644,2042,3645,3646,3647,3648,3649,3650,3651,3652,3653,1976,3654,2714,2767,2814,2889,2940,2973,8,3612,3509,3571,3511]
def ids50 : List Nat := [491,588,771,682,3022,3655,3656,3657,3658,3659,3205,3660,3055,3090,3178,3231,3303,3334,3406,3437,1871,1924,2107,2001,3515,3538,3600,3619,814,3661,3662,3663,3664,3665,1117,3666,877,944,1054,1139,1223,1284,1394,1459,75,152,284,353,1571,1626,1718,1769,8,3667,3668,3669,3670,8,3667,3671,3672,3673,2157,3674,3675,3676,2389,3677,3678,3679,3680,3681,3682,3683,3684,3685,3686,3687,3688,3689,3690,3668,3670,3671,3673,2198,2249,2405,2320,3691,3692,3693,3694,2492,2537,2668,2600,3695,3696,3697,3698,2721,2776,2827,2890,2941,2980]
def ids51 : List Nat := [492,589,772,683,3056,3091,3092,3179,3232,3233,3304,3305,3335,3407,3408,3438,3699,3700,3104,3701,3141,3702,3703,3704,1872,1925,2108,2002,3516,3539,3601,3620,878,879,945,1055,1056,1140,1224,1285,1286,1395,1460,1461,3705,3706,960,3707,1023,3708,3709,3710,76,153,285,354,1572,1627,1719,1770,3688,3689,3690,3711,3712,3713,3714,8,3715,3672,3713,3714,2199,2250,2251,2406,2407,2321,3716,3717,3718,3719,3720,3721,8,3715,3669,3711,3712,2493,2538,2539,2669,2670,2601,3722,3723,3724,3725,3726,3727,3728,3729,3730,3731,2270,3732,3733,3734,3735,3736,2339,3737,3738,3739,3740,3741,3742,3743,3744,3745,2722,2777,2828,2891,2942,2981]
def ids52 : List Nat := [3026,3746,3747,3748,3749,3750,3751,3752,3753,3754,3211,3755,493,590,773,684,3057,3093,3094,3180,3234,3235,3306,3336,3409,3439,1873,1926,2109,2003,3517,3540,3602,3621,820,3756,3757,3758,1121,3759,3760,3761,8,3762,3668,3763,3670,8,3762,3711,3764,3712,2163,3765,3766,3767,2393,3768,3769,3770,3771,3772,3773,3774,3775,3776,3777,3778,880,881,946,1057,1058,1141,1225,1287,1396,1462,77,154,286,355,1573,1628,1720,1771,3668,3670,3711,3712,3779,3780,3781,2200,2252,2253,2408,2409,2322,3782,3783,3784,3785,3786,3787,2494,2540,2671,2602,3788,3789,3790,3791,2723,2778,2829,2892,2943,2982]
def ids53 : List Nat := [494,591,774,685,3137,3792,3793,3794,3795,3796,3108,3797,3058,3095,3181,3236,3307,3308,3337,3410,3411,3440,1874,1927,2110,2004,3518,3541,3603,3622,1019,3798,3799,3800,3801,3802,3803,3804,3805,3806,964,3807,882,947,1059,1142,1226,1288,1289,1397,1463,1464,78,155,287,356,1574,1629,1721,1772,8,3808,3713,3764,3714,8,3808,3671,3763,3673,2333,3809,3810,3811,2272,3812,3813,3814,3815,3816,3817,3818,3819,3820,3821,3822,3671,3673,3713,3714,3779,3780,3781,2201,2254,2410,2323,3823,3824,3825,3826,2495,2541,2542,2672,2673,2603,3827,3828,3829,3830,3831,3832,2724,2779,2830,2893,2944,2983]
def ids54 : List Nat := [3036,3833,3834,3835,3836,3837,3223,3838,3839,3840,3841,3842,836,3843,3844,3845,3846,3847,1131,3848,3849,3850,3851,3852,8,3853,3854,3855,3856,3680,3857,3858,3859,3860,3861,3771,3862,3863,3864,3865,3866,2172,3867,3868,3869,3870,3871,2397,3872,3873,3874,3875,3876,8,3853,3877,3878,3879,499,596,779,690,3059,3096,3182,3237,3309,3344,3412,3441,1879,1942,2115,2019,3519,3542,3604,3629,887,952,1064,1147,1231,1300,1402,1469,83,170,292,371,1579,1634,1726,1783,3691,3716,3782,3823,2205,2260,2411,2329,3880,3881,3882,3854,3856,3877,3879,2496,2549,2674,2610,3883,3884,3885,3886,2731,2780,2831,2894,2945,2990]
def ids55 : List Nat := [500,597,780,691,3060,3097,3098,3183,3238,3239,3310,3345,3413,3442,1880,1943,2116,2020,3520,3543,3605,3630,3887,3888,3118,3889,3159,3890,3891,3892,888,953,954,1065,1148,1149,1232,1301,1403,1470,84,171,293,372,1580,1635,1636,1727,1784,1785,3893,3894,974,3895,1037,3896,3897,3898,3692,3717,3718,3783,3784,3824,2206,2261,2412,2330,3880,3881,3882,3899,3900,3901,3902,8,3903,3878,3901,3902,2497,2550,2675,2611,3904,3905,3906,3907,3908,3909,3740,3910,3819,3911,3912,3913,2732,2781,2832,2782,2833,2895,2946,2991,2992,3914,3915,2288,3916,2354,3917,3918,3919,8,3903,3855,3899,3900]
def ids56 : List Nat := [501,598,781,692,3040,3920,3921,3922,3923,3924,3227,3925,3061,3099,3100,3184,3240,3241,3311,3346,3414,3443,1881,1944,2117,2021,3521,3544,3606,3631,842,3926,3927,3928,3929,3930,1135,3931,889,955,956,1066,1150,1151,1233,1302,1404,1471,85,172,294,373,1581,1637,1728,1786,8,3932,3854,3933,3856,3684,3934,3935,3936,3775,3937,3938,3939,2178,3940,3941,3942,2401,3943,3944,3945,8,3932,3899,3946,3900,3693,3719,3720,3785,3786,3825,2207,2262,2413,2331,3854,3856,3899,3900,3947,3948,3949,2498,2551,2676,2612,3950,3951,3952,3953,2733,2783,2834,2896,2947,2993]
def ids57 : List Nat := [502,599,782,693,3062,3101,3185,3242,3312,3347,3415,3444,1882,1945,2118,2022,3155,3954,3955,3956,3957,3958,3122,3959,3522,3545,3607,3632,890,957,1067,1152,1234,1303,1405,1472,86,173,295,374,1033,3960,3961,3962,3963,3964,978,3965,1582,1638,1639,1729,1787,1788,3694,3721,3787,3826,2208,2263,2414,2332,8,3966,3946,3901,3902,3877,3879,3901,3902,3947,3948,3949,2499,2552,2677,2613,3815,3967,3968,3969,3970,3971,3744,3972,3973,3974,3975,3976,2350,3977,3978,3979,3980,3981,3982,3983,3984,3985,2292,3986,2734,2784,2835,2785,2836,2897,2948,2994,2995,8,3966,3877,3933,3879]
def ids58 : List Nat := [3284,3987,3988,3989,3990,3991,3451,3992,3993,3994,3995,3996,1208,3997,3998,3999,4000,4001,1479,4002,4003,4004,4005,4006,3680,4007,4008,4009,4010,4011,3815,4012,4013,4014,4015,4016,8,4017,4018,4019,4020,2468,4021,4022,4023,4024,4025,2679,4026,4027,4028,4029,4030,8,4017,4031,4032,4033,507,604,787,698,3063,3124,3186,3243,3313,3348,3416,3459,1887,1960,2123,2037,3523,3552,3608,3639,895,984,1072,1157,1239,1310,1410,1493,91,188,300,389,1587,1650,1734,1799,3695,3722,3788,3827,2215,2276,2421,2345,3883,3904,3950,3973,2503,2558,2687,2619,4034,4035,4036,4018,4020,4031,4033,2741,2790,2843,2898,2949,3002]
def ids59 : List Nat := [508,605,788,699,3064,3125,3187,3244,3314,3349,3350,3417,3460,3461,1888,1961,2124,2038,3524,3553,3554,3609,3640,3641,4037,4038,3362,4039,3393,4040,4041,4042,896,985,1073,1158,1240,1311,1312,1411,1494,1495,92,189,301,390,1588,1651,1735,1800,4043,4044,1324,4045,1365,4046,4047,4048,3696,3723,3724,3789,3828,3829,2216,2277,2422,2346,3884,3905,3951,3974,4049,4050,3740,4051,3775,4052,4053,4054,2504,2559,2688,2620,4034,4035,4036,4055,4056,4057,4058,8,4059,4032,4057,4058,2742,2791,2844,2792,2845,2899,2950,3003,3004,4060,4061,2570,4062,2628,4063,4064,4065,8,4059,4019,4055,4056]
def ids60 : List Nat := [509,606,789,700,3065,3126,3188,3245,3290,4066,4067,4068,4069,4070,3455,4071,3315,3351,3352,3418,3462,3463,1889,1962,2125,2039,3525,3555,3610,3642,897,986,1074,1159,1212,4072,4073,4074,4075,4076,1483,4077,1241,1313,1314,1412,1496,1497,93,190,302,391,1589,1652,1736,1801,3684,4078,4079,4080,4081,4082,3819,4083,3697,3725,3726,3790,3830,3831,2217,2278,2423,2347,3885,3906,3952,3975,8,4084,4018,4085,4020,2474,4086,4087,4088,2683,4089,4090,4091,8,4084,4055,4092,4056,2505,2560,2689,2621,4018,4020,4055,4056,4093,4094,4095,2743,2793,2846,2900,2951,3005]
def ids61 : List Nat := [510,607,790,701,3066,3127,3189,3246,3316,3353,3419,3464,1890,1963,2126,2040,3389,4096,4097,4098,4099,4100,3366,4101,3526,3556,3557,3611,3643,3644,898,987,1075,1160,1242,1315,1413,1498,94,191,303,392,1361,4102,4103,4104,4105,4106,1328,4107,1590,1653,1737,1802,3698,3727,3791,3832,2218,2279,2424,2348,3771,4108,4109,4110,4111,4112,3744,4113,3886,3907,3953,3976,2506,2561,2690,2622,8,4114,4092,4057,4058,4031,4033,4057,4058,4093,4094,4095,2624,4115,4116,4117,4118,4119,4120,4121,4122,4123,2574,4124,2744,2794,2847,2795,2848,2901,2952,3006,3007,8,4114,4031,4085,4033]
end Tokens
namespace Tokens
def acceptID (i : Nat) := valid (witness i)
def batch (i n : Nat) := (((List.range 4125).drop i).take n).all acceptID
def remaining (i : Nat) := ((List.range 4125).drop i).all acceptID
end Tokens
namespace Tokens
lemma joinIDs {i n : Nat} (a : batch i n = true) (b : remaining (i+n) = true) :
    remaining i = true := scan_block (List.range 4125) acceptID i n a b
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma finishIDs (b : Nat) (ids : List Nat) (nd : (branchList.getD b []).Nodup)
    (out : branchList.getD b [] ≠ [goal] ∧ branchList.getD b [] ≠ [~~~goal])
    (cover : (candidates 7 (branchList.getD b [])).map Fast.enc = ids.map witness)
    (bound : ids.all (fun i => decide (i < 4125)) = true) (all : remaining 0 = true) :
    dead 8 (branchList.getD b []) := by
  apply dead_split 7 _ nd out
  intro c hc
  have mem : Fast.enc c ∈ (candidates 7 (branchList.getD b [])).map Fast.enc :=
    List.mem_map.mpr ⟨c,hc,rfl⟩
  rw [cover] at mem
  obtain ⟨i, hi, eq⟩ := List.mem_map.mp mem
  apply valid_dead
  rw [←eq]
  have lt : i < 4125 := of_decide_eq_true (List.all_eq_true.mp bound i hi)
  have checked : (List.range 4125).all acceptID = true := by simpa only [remaining,List.drop_zero] using all
  change acceptID i = true
  exact List.all_eq_true.mp checked i (List.mem_range.mpr lt)
end Tokens
namespace Tokens
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c0 : (candidates 7 branch0).map Fast.enc = ids0.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c1 : (candidates 7 branch1).map Fast.enc = ids1.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c2 : (candidates 7 branch2).map Fast.enc = ids2.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c3 : (candidates 7 branch3).map Fast.enc = ids3.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c4 : (candidates 7 branch4).map Fast.enc = ids4.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c5 : (candidates 7 branch5).map Fast.enc = ids5.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c6 : (candidates 7 branch6).map Fast.enc = ids6.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c7 : (candidates 7 branch7).map Fast.enc = ids7.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c8 : (candidates 7 branch8).map Fast.enc = ids8.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c9 : (candidates 7 branch9).map Fast.enc = ids9.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c10 : (candidates 7 branch10).map Fast.enc = ids10.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c11 : (candidates 7 branch11).map Fast.enc = ids11.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c12 : (candidates 7 branch12).map Fast.enc = ids12.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c13 : (candidates 7 branch13).map Fast.enc = ids13.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c14 : (candidates 7 branch14).map Fast.enc = ids14.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c15 : (candidates 7 branch15).map Fast.enc = ids15.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c16 : (candidates 7 branch16).map Fast.enc = ids16.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c17 : (candidates 7 branch17).map Fast.enc = ids17.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c18 : (candidates 7 branch18).map Fast.enc = ids18.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c19 : (candidates 7 branch19).map Fast.enc = ids19.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c20 : (candidates 7 branch20).map Fast.enc = ids20.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c21 : (candidates 7 branch21).map Fast.enc = ids21.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c22 : (candidates 7 branch22).map Fast.enc = ids22.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c23 : (candidates 7 branch23).map Fast.enc = ids23.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c24 : (candidates 7 branch24).map Fast.enc = ids24.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c25 : (candidates 7 branch25).map Fast.enc = ids25.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c26 : (candidates 7 branch26).map Fast.enc = ids26.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c27 : (candidates 7 branch27).map Fast.enc = ids27.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c28 : (candidates 7 branch28).map Fast.enc = ids28.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c29 : (candidates 7 branch29).map Fast.enc = ids29.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c30 : (candidates 7 branch30).map Fast.enc = ids30.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c31 : (candidates 7 branch31).map Fast.enc = ids31.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c32 : (candidates 7 branch32).map Fast.enc = ids32.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c33 : (candidates 7 branch33).map Fast.enc = ids33.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c34 : (candidates 7 branch34).map Fast.enc = ids34.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c35 : (candidates 7 branch35).map Fast.enc = ids35.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c36 : (candidates 7 branch36).map Fast.enc = ids36.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c37 : (candidates 7 branch37).map Fast.enc = ids37.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c38 : (candidates 7 branch38).map Fast.enc = ids38.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c39 : (candidates 7 branch39).map Fast.enc = ids39.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c40 : (candidates 7 branch40).map Fast.enc = ids40.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c41 : (candidates 7 branch41).map Fast.enc = ids41.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c42 : (candidates 7 branch42).map Fast.enc = ids42.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c43 : (candidates 7 branch43).map Fast.enc = ids43.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c44 : (candidates 7 branch44).map Fast.enc = ids44.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c45 : (candidates 7 branch45).map Fast.enc = ids45.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c46 : (candidates 7 branch46).map Fast.enc = ids46.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c47 : (candidates 7 branch47).map Fast.enc = ids47.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c48 : (candidates 7 branch48).map Fast.enc = ids48.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c49 : (candidates 7 branch49).map Fast.enc = ids49.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c50 : (candidates 7 branch50).map Fast.enc = ids50.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c51 : (candidates 7 branch51).map Fast.enc = ids51.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c52 : (candidates 7 branch52).map Fast.enc = ids52.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c53 : (candidates 7 branch53).map Fast.enc = ids53.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c54 : (candidates 7 branch54).map Fast.enc = ids54.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c55 : (candidates 7 branch55).map Fast.enc = ids55.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c56 : (candidates 7 branch56).map Fast.enc = ids56.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c57 : (candidates 7 branch57).map Fast.enc = ids57.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c58 : (candidates 7 branch58).map Fast.enc = ids58.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c59 : (candidates 7 branch59).map Fast.enc = ids59.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c60 : (candidates 7 branch60).map Fast.enc = ids60.map witness := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem c61 : (candidates 7 branch61).map Fast.enc = ids61.map witness := by decide +kernel
end Tokens
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf0 (done : Tokens.remaining 0 = true) : dead 8 branch0 := Tokens.finishIDs 0 Tokens.ids0 (by decide +kernel) (by decide +kernel) Tokens.c0 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf1 (done : Tokens.remaining 0 = true) : dead 8 branch1 := Tokens.finishIDs 1 Tokens.ids1 (by decide +kernel) (by decide +kernel) Tokens.c1 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf2 (done : Tokens.remaining 0 = true) : dead 8 branch2 := Tokens.finishIDs 2 Tokens.ids2 (by decide +kernel) (by decide +kernel) Tokens.c2 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf3 (done : Tokens.remaining 0 = true) : dead 8 branch3 := Tokens.finishIDs 3 Tokens.ids3 (by decide +kernel) (by decide +kernel) Tokens.c3 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf4 (done : Tokens.remaining 0 = true) : dead 8 branch4 := Tokens.finishIDs 4 Tokens.ids4 (by decide +kernel) (by decide +kernel) Tokens.c4 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf5 (done : Tokens.remaining 0 = true) : dead 8 branch5 := Tokens.finishIDs 5 Tokens.ids5 (by decide +kernel) (by decide +kernel) Tokens.c5 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf6 (done : Tokens.remaining 0 = true) : dead 8 branch6 := Tokens.finishIDs 6 Tokens.ids6 (by decide +kernel) (by decide +kernel) Tokens.c6 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf7 (done : Tokens.remaining 0 = true) : dead 8 branch7 := Tokens.finishIDs 7 Tokens.ids7 (by decide +kernel) (by decide +kernel) Tokens.c7 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf8 (done : Tokens.remaining 0 = true) : dead 8 branch8 := Tokens.finishIDs 8 Tokens.ids8 (by decide +kernel) (by decide +kernel) Tokens.c8 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf9 (done : Tokens.remaining 0 = true) : dead 8 branch9 := Tokens.finishIDs 9 Tokens.ids9 (by decide +kernel) (by decide +kernel) Tokens.c9 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf10 (done : Tokens.remaining 0 = true) : dead 8 branch10 := Tokens.finishIDs 10 Tokens.ids10 (by decide +kernel) (by decide +kernel) Tokens.c10 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf11 (done : Tokens.remaining 0 = true) : dead 8 branch11 := Tokens.finishIDs 11 Tokens.ids11 (by decide +kernel) (by decide +kernel) Tokens.c11 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf12 (done : Tokens.remaining 0 = true) : dead 8 branch12 := Tokens.finishIDs 12 Tokens.ids12 (by decide +kernel) (by decide +kernel) Tokens.c12 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf13 (done : Tokens.remaining 0 = true) : dead 8 branch13 := Tokens.finishIDs 13 Tokens.ids13 (by decide +kernel) (by decide +kernel) Tokens.c13 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf14 (done : Tokens.remaining 0 = true) : dead 8 branch14 := Tokens.finishIDs 14 Tokens.ids14 (by decide +kernel) (by decide +kernel) Tokens.c14 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf15 (done : Tokens.remaining 0 = true) : dead 8 branch15 := Tokens.finishIDs 15 Tokens.ids15 (by decide +kernel) (by decide +kernel) Tokens.c15 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf16 (done : Tokens.remaining 0 = true) : dead 8 branch16 := Tokens.finishIDs 16 Tokens.ids16 (by decide +kernel) (by decide +kernel) Tokens.c16 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf17 (done : Tokens.remaining 0 = true) : dead 8 branch17 := Tokens.finishIDs 17 Tokens.ids17 (by decide +kernel) (by decide +kernel) Tokens.c17 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf18 (done : Tokens.remaining 0 = true) : dead 8 branch18 := Tokens.finishIDs 18 Tokens.ids18 (by decide +kernel) (by decide +kernel) Tokens.c18 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf19 (done : Tokens.remaining 0 = true) : dead 8 branch19 := Tokens.finishIDs 19 Tokens.ids19 (by decide +kernel) (by decide +kernel) Tokens.c19 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf20 (done : Tokens.remaining 0 = true) : dead 8 branch20 := Tokens.finishIDs 20 Tokens.ids20 (by decide +kernel) (by decide +kernel) Tokens.c20 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf21 (done : Tokens.remaining 0 = true) : dead 8 branch21 := Tokens.finishIDs 21 Tokens.ids21 (by decide +kernel) (by decide +kernel) Tokens.c21 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf22 (done : Tokens.remaining 0 = true) : dead 8 branch22 := Tokens.finishIDs 22 Tokens.ids22 (by decide +kernel) (by decide +kernel) Tokens.c22 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf23 (done : Tokens.remaining 0 = true) : dead 8 branch23 := Tokens.finishIDs 23 Tokens.ids23 (by decide +kernel) (by decide +kernel) Tokens.c23 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf24 (done : Tokens.remaining 0 = true) : dead 8 branch24 := Tokens.finishIDs 24 Tokens.ids24 (by decide +kernel) (by decide +kernel) Tokens.c24 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf25 (done : Tokens.remaining 0 = true) : dead 8 branch25 := Tokens.finishIDs 25 Tokens.ids25 (by decide +kernel) (by decide +kernel) Tokens.c25 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf26 (done : Tokens.remaining 0 = true) : dead 8 branch26 := Tokens.finishIDs 26 Tokens.ids26 (by decide +kernel) (by decide +kernel) Tokens.c26 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf27 (done : Tokens.remaining 0 = true) : dead 8 branch27 := Tokens.finishIDs 27 Tokens.ids27 (by decide +kernel) (by decide +kernel) Tokens.c27 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf28 (done : Tokens.remaining 0 = true) : dead 8 branch28 := Tokens.finishIDs 28 Tokens.ids28 (by decide +kernel) (by decide +kernel) Tokens.c28 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf29 (done : Tokens.remaining 0 = true) : dead 8 branch29 := Tokens.finishIDs 29 Tokens.ids29 (by decide +kernel) (by decide +kernel) Tokens.c29 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf30 (done : Tokens.remaining 0 = true) : dead 8 branch30 := Tokens.finishIDs 30 Tokens.ids30 (by decide +kernel) (by decide +kernel) Tokens.c30 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf31 (done : Tokens.remaining 0 = true) : dead 8 branch31 := Tokens.finishIDs 31 Tokens.ids31 (by decide +kernel) (by decide +kernel) Tokens.c31 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf32 (done : Tokens.remaining 0 = true) : dead 8 branch32 := Tokens.finishIDs 32 Tokens.ids32 (by decide +kernel) (by decide +kernel) Tokens.c32 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf33 (done : Tokens.remaining 0 = true) : dead 8 branch33 := Tokens.finishIDs 33 Tokens.ids33 (by decide +kernel) (by decide +kernel) Tokens.c33 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf34 (done : Tokens.remaining 0 = true) : dead 8 branch34 := Tokens.finishIDs 34 Tokens.ids34 (by decide +kernel) (by decide +kernel) Tokens.c34 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf35 (done : Tokens.remaining 0 = true) : dead 8 branch35 := Tokens.finishIDs 35 Tokens.ids35 (by decide +kernel) (by decide +kernel) Tokens.c35 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf36 (done : Tokens.remaining 0 = true) : dead 8 branch36 := Tokens.finishIDs 36 Tokens.ids36 (by decide +kernel) (by decide +kernel) Tokens.c36 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf37 (done : Tokens.remaining 0 = true) : dead 8 branch37 := Tokens.finishIDs 37 Tokens.ids37 (by decide +kernel) (by decide +kernel) Tokens.c37 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf38 (done : Tokens.remaining 0 = true) : dead 8 branch38 := Tokens.finishIDs 38 Tokens.ids38 (by decide +kernel) (by decide +kernel) Tokens.c38 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf39 (done : Tokens.remaining 0 = true) : dead 8 branch39 := Tokens.finishIDs 39 Tokens.ids39 (by decide +kernel) (by decide +kernel) Tokens.c39 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf40 (done : Tokens.remaining 0 = true) : dead 8 branch40 := Tokens.finishIDs 40 Tokens.ids40 (by decide +kernel) (by decide +kernel) Tokens.c40 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf41 (done : Tokens.remaining 0 = true) : dead 8 branch41 := Tokens.finishIDs 41 Tokens.ids41 (by decide +kernel) (by decide +kernel) Tokens.c41 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf42 (done : Tokens.remaining 0 = true) : dead 8 branch42 := Tokens.finishIDs 42 Tokens.ids42 (by decide +kernel) (by decide +kernel) Tokens.c42 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf43 (done : Tokens.remaining 0 = true) : dead 8 branch43 := Tokens.finishIDs 43 Tokens.ids43 (by decide +kernel) (by decide +kernel) Tokens.c43 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf44 (done : Tokens.remaining 0 = true) : dead 8 branch44 := Tokens.finishIDs 44 Tokens.ids44 (by decide +kernel) (by decide +kernel) Tokens.c44 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf45 (done : Tokens.remaining 0 = true) : dead 8 branch45 := Tokens.finishIDs 45 Tokens.ids45 (by decide +kernel) (by decide +kernel) Tokens.c45 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf46 (done : Tokens.remaining 0 = true) : dead 8 branch46 := Tokens.finishIDs 46 Tokens.ids46 (by decide +kernel) (by decide +kernel) Tokens.c46 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf47 (done : Tokens.remaining 0 = true) : dead 8 branch47 := Tokens.finishIDs 47 Tokens.ids47 (by decide +kernel) (by decide +kernel) Tokens.c47 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf48 (done : Tokens.remaining 0 = true) : dead 8 branch48 := Tokens.finishIDs 48 Tokens.ids48 (by decide +kernel) (by decide +kernel) Tokens.c48 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf49 (done : Tokens.remaining 0 = true) : dead 8 branch49 := Tokens.finishIDs 49 Tokens.ids49 (by decide +kernel) (by decide +kernel) Tokens.c49 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf50 (done : Tokens.remaining 0 = true) : dead 8 branch50 := Tokens.finishIDs 50 Tokens.ids50 (by decide +kernel) (by decide +kernel) Tokens.c50 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf51 (done : Tokens.remaining 0 = true) : dead 8 branch51 := Tokens.finishIDs 51 Tokens.ids51 (by decide +kernel) (by decide +kernel) Tokens.c51 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf52 (done : Tokens.remaining 0 = true) : dead 8 branch52 := Tokens.finishIDs 52 Tokens.ids52 (by decide +kernel) (by decide +kernel) Tokens.c52 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf53 (done : Tokens.remaining 0 = true) : dead 8 branch53 := Tokens.finishIDs 53 Tokens.ids53 (by decide +kernel) (by decide +kernel) Tokens.c53 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf54 (done : Tokens.remaining 0 = true) : dead 8 branch54 := Tokens.finishIDs 54 Tokens.ids54 (by decide +kernel) (by decide +kernel) Tokens.c54 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf55 (done : Tokens.remaining 0 = true) : dead 8 branch55 := Tokens.finishIDs 55 Tokens.ids55 (by decide +kernel) (by decide +kernel) Tokens.c55 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf56 (done : Tokens.remaining 0 = true) : dead 8 branch56 := Tokens.finishIDs 56 Tokens.ids56 (by decide +kernel) (by decide +kernel) Tokens.c56 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf57 (done : Tokens.remaining 0 = true) : dead 8 branch57 := Tokens.finishIDs 57 Tokens.ids57 (by decide +kernel) (by decide +kernel) Tokens.c57 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf58 (done : Tokens.remaining 0 = true) : dead 8 branch58 := Tokens.finishIDs 58 Tokens.ids58 (by decide +kernel) (by decide +kernel) Tokens.c58 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf59 (done : Tokens.remaining 0 = true) : dead 8 branch59 := Tokens.finishIDs 59 Tokens.ids59 (by decide +kernel) (by decide +kernel) Tokens.c59 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf60 (done : Tokens.remaining 0 = true) : dead 8 branch60 := Tokens.finishIDs 60 Tokens.ids60 (by decide +kernel) (by decide +kernel) Tokens.c60 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem leaf61 (done : Tokens.remaining 0 = true) : dead 8 branch61 := Tokens.finishIDs 61 Tokens.ids61 (by decide +kernel) (by decide +kernel) Tokens.c61 (by decide +kernel) done
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no_small (done : Tokens.remaining 0 = true) (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t 9 inputs.toFinset) : False := by
  apply finish_impossible 9 inputs (by decide +kernel) _ t ht run
  apply dead_split_checked 8 inputs branchList (by decide +kernel) (by decide +kernel)
  · exact (all_dead_cons (leaf0 done) (all_dead_cons (leaf1 done) (all_dead_cons (leaf2 done) (all_dead_cons (leaf3 done) (all_dead_cons (leaf4 done) (all_dead_cons (leaf5 done) (all_dead_cons (leaf6 done) (all_dead_cons (leaf7 done) (all_dead_cons (leaf8 done) (all_dead_cons (leaf9 done) (all_dead_cons (leaf10 done) (all_dead_cons (leaf11 done) (all_dead_cons (leaf12 done) (all_dead_cons (leaf13 done) (all_dead_cons (leaf14 done) (all_dead_cons (leaf15 done) (all_dead_cons (leaf16 done) (all_dead_cons (leaf17 done) (all_dead_cons (leaf18 done) (all_dead_cons (leaf19 done) (all_dead_cons (leaf20 done) (all_dead_cons (leaf21 done) (all_dead_cons (leaf22 done) (all_dead_cons (leaf23 done) (all_dead_cons (leaf24 done) (all_dead_cons (leaf25 done) (all_dead_cons (leaf26 done) (all_dead_cons (leaf27 done) (all_dead_cons (leaf28 done) (all_dead_cons (leaf29 done) (all_dead_cons (leaf30 done) (all_dead_cons (leaf31 done) (all_dead_cons (leaf32 done) (all_dead_cons (leaf33 done) (all_dead_cons (leaf34 done) (all_dead_cons (leaf35 done) (all_dead_cons (leaf36 done) (all_dead_cons (leaf37 done) (all_dead_cons (leaf38 done) (all_dead_cons (leaf39 done) (all_dead_cons (leaf40 done) (all_dead_cons (leaf41 done) (all_dead_cons (leaf42 done) (all_dead_cons (leaf43 done) (all_dead_cons (leaf44 done) (all_dead_cons (leaf45 done) (all_dead_cons (leaf46 done) (all_dead_cons (leaf47 done) (all_dead_cons (leaf48 done) (all_dead_cons (leaf49 done) (all_dead_cons (leaf50 done) (all_dead_cons (leaf51 done) (all_dead_cons (leaf52 done) (all_dead_cons (leaf53 done) (all_dead_cons (leaf54 done) (all_dead_cons (leaf55 done) (all_dead_cons (leaf56 done) (all_dead_cons (leaf57 done) (all_dead_cons (leaf58 done) (all_dead_cons (leaf59 done) (all_dead_cons (leaf60 done) (all_dead_cons (leaf61 done) (all_dead_nil 8)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · decide +kernel
end PEqualNP.Outside.L_meta_30815_aux.Signed

namespace PEqualNP.Outside.L_meta_30815_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_30815_aux.Signed (legal isBinary binaryCost)

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rcStep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) : List Gate × List (Bool ⊕ ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (out, env ++ [Sum.inl true])
    | i :: _ =>
      match env.getD i (Sum.inl false) with
      | Sum.inl b => (out, env ++ [Sum.inl (!b)])
      | Sum.inr w' => (out ++ [{ op := GateOp.not, inputs := [w'] }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.and =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) then
      (out, env ++ [Sum.inl false])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl true])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.and, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.or =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) then
      (out, env ++ [Sum.inl true])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl false])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.or, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | _ => (out, env ++ [Sum.inl false])

def rcCircuit (nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (gs : List Gate) (o : ℕ) : List Gate × ℕ :=
  let res := gs.foldl (rcStep nOut) ([], env0)
  match res.2.getD o (Sum.inl false) with
  | Sum.inr w' => (res.1, w')
  | Sum.inl false => (res.1, nOut + res.1.length)
  | Sum.inl true => (res.1 ++ [{ op := GateOp.not, inputs := [] }], nOut + res.1.length)

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t; omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]; omega

lemma rcStep_env_len (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (rcStep nOut st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]
    cases g.inputs with
    | nil => simp
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) <;> simp
  · simp [rcStep, h]
  · simp [rcStep, h]

lemma rcStep_legal (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, legal g') (hg : legal g) :
    ∀ g' ∈ (rcStep nOut st g).1, legal g' := by
  rcases st with ⟨out, env⟩
  dsimp only at h1 ⊢
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    cases g.inputs with
    | nil => exact h1
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => exact h1
      | inr w' =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · exact ⟨by simp, by simp⟩

lemma rcFold_legal (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ))
    (h1 : ∀ g' ∈ st.1, legal g') (hM : ∀ g ∈ gs, legal g) :
    ∀ g' ∈ (gs.foldl (rcStep nOut) st).1, legal g' := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rcStep nOut st g) (rcStep_legal nOut st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma binaryCost_append_one (gs : List Gate) (g : Gate) :
    binaryCost (gs ++ [g]) = binaryCost gs + (if isBinary g then 1 else 0) := by
  unfold binaryCost
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isBinary g <;> simp

lemma rcStep_binCost_le (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    binaryCost (rcStep nOut st g).1 ≤ binaryCost st.1 + (if isBinary g then 1 else 0) := by
  rcases st with ⟨out, env⟩
  dsimp only
  cases h : g.op
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases g.inputs with
    | nil => dsimp only; exact le_refl _
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => dsimp only; exact le_refl _
      | inr w' => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp [rcStep, h, isBinary]
  · simp [rcStep, h, isBinary]

lemma rcFold_binCost_le (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ)) :
    binaryCost (gs.foldl (rcStep nOut) st).1 ≤ binaryCost st.1 + binaryCost gs := by
  induction gs generalizing st with
  | nil => simp [binaryCost]
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    omega

lemma rcFold_eval_inv (nOut : ℕ) (gs : List Gate) (ys : List Bool) (hyl : ys.length = nOut)
    (hM : ∀ g ∈ gs, legal g) (ws : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i (Sum.inl false) with
      | Sum.inl b => ws.getD i false = b
      | Sum.inr w' => w' < nOut + st.1.length ∧ ws.getD i false = (st.1.foldl step ys).getD w' false) :
    let ws' := gs.foldl step ws
    let st' := gs.foldl (rcStep nOut) st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i (Sum.inl false) with
      | Sum.inl b => ws'.getD i false = b
      | Sum.inr w' => w' < nOut + st'.1.length ∧ ws'.getD i false = (st'.1.foldl step ys).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (step ws g).length = env.length + 1 := by simp [step, hlen_ws]
    have hget_old : ∀ i < env.length, (step ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (step ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (step ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (step ws g).length = (rcStep nOut (out, env) g).2.length ∧
        ∀ i, match (rcStep nOut (out, env) g).2.getD i (Sum.inl false) with
          | Sum.inl b => (step ws g).getD i false = b
          | Sum.inr w' => w' < nOut + (rcStep nOut (out, env) g).1.length ∧
              (step ws g).getD i false = ((rcStep nOut (out, env) g).1.foldl step ys).getD w' false := by
      constructor
      · rw [rcStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl step ys) = step (out.foldl step ys) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + out.length ∧ (step ws g).getD i false = (out.foldl step ys).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]; exact hinv i
        have hkeep_old_app : ∀ (x : Bool ⊕ ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + (out ++ [gnew]).length ∧
                (step ws g).getD i false = ((out ++ [gnew]).foldl step ys).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i (Sum.inl false) with
          | inl b => rw [hm] at hk; exact hk
          | inr w' =>
            rw [hm] at hk; dsimp only at hk
            have hw' : w' < nOut + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
            have hlen_w : (step (out.foldl step ys) gnew).length = nOut + out.length + 1 := by simp [step, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl step ys).length),
                List.getD_eq_getElem _ _ (by omega : w' < (step (out.foldl step ys) gnew).length)]
            simp [step, List.getElem_append_left (by omega : w' < (out.foldl step ys).length)]
        have hkeep_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none),
            w' < nOut + out.length := by
          intro w' hw'
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
          have hij := hinv j
          cases hm : env.getD j (Sum.inl false) with
          | inl b => rw [hm] at hj; cases hj
          | inr w0 =>
            rw [hm] at hj hij; dsimp only at hij
            cases hj; exact hij.1
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl false) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl false), hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjf⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjf hj'; dsimp only at hj'
                  cases b with
                  | false => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                  | true => simp at hjf
                | inr w' => rw [hm] at hjf; simp at hjf
              · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
          · have hand_eq : (g.inputs.map fun j => ws.getD j false).all id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).all id := by
              have hnof : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl false := by
                intro j hj heqf
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqf]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl false) →
                  (l.map fun j => ws.getD j false).all id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).all id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnf
                  have ha := hnf a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnf j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | false => exact absurd hm ha
                    | true =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia, Bool.true_and, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnof
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hand_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl true) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop]; simpa [GateOp.eval] using hand_eq
                · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl true), hget_last, hop]
                simp only [GateOp.eval, List.any_eq_true, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjt⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjt hj'; dsimp only at hj'
                  cases b with
                  | true => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hj'⟩
                  | false => simp at hjt
                | inr w' => rw [hm] at hjt; simp at hjt
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          · have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).any id := by
              have hnot : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl true := by
                intro j hj heqt
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqt]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl true) →
                  (l.map fun j => ws.getD j false).any id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).any id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnt
                  have ha := hnt a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | true => exact absurd hm ha
                    | false =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnot
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl false) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl false), hget_last, hop]; simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          cases hgi : g.inputs with
          | nil =>
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop, hgi]; rfl
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          | cons j rest_i =>
            dsimp only
            cases hm : env.getD j (Sum.inl false) with
            | inl b =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl (!b)) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl (!b)), hget_last, hop, hgi]; simpa [GateOp.eval] using hj'
                · rw [hkeep_hi (Sum.inl (!b)) i (by omega)]; exact hget_hi i (by omega)
            | inr w' =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (Sum.inr (nOut + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hgi, hfold_app]
                  have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                  simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hj'.2
                · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step ws g) (rcStep nOut (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma rcFold_inr_agree (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = st.2.length) (hylen : wy.length = st.2.length)
    (heq_cost : binaryCost (gs.foldl (rcStep nOut) st).1 = binaryCost st.1 + binaryCost gs)
    (hagree : ∀ i w', st.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false) :
    ∀ i w', (gs.foldl (rcStep nOut) st).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false := by
  induction gs generalizing wx wy st with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons] at heq_cost ⊢
    have hg := hM g List.mem_cons_self
    have h1 := rcFold_binCost_le nOut rest (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hstep_cost : binaryCost (rcStep nOut st g).1 = binaryCost st.1 + (if isBinary g then 1 else 0) := by omega
    have hrest_cost : binaryCost (rest.foldl (rcStep nOut) (rcStep nOut st g)).1 =
        binaryCost (rcStep nOut st g).1 + binaryCost rest := by omega
    rcases st with ⟨out, env⟩
    dsimp only at hxlen hylen hagree hstep_cost
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step wx g) (step wy g)
      (rcStep nOut (out, env) g) (by rw [rcStep_env_len]; simp [step, hxlen])
      (by rw [rcStep_env_len]; simp [step, hylen]) hrest_cost ?_
    have hget_old_x : ∀ i < env.length, (step wx g).getD i false = wx.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < env.length, (step wy g).getD i false = wy.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : (step wx g).getD env.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : (step wy g).getD env.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hall_inr_of_len2 :
        (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 →
        ∀ j ∈ g.inputs, ∃ w0, env.getD j (Sum.inl false) = Sum.inr w0 := by
      intro hl2 j hj
      cases hm : env.getD j (Sum.inl false) with
      | inr w0 => exact ⟨w0, rfl⟩
      | inl b =>
        exfalso
        have hlt := list_filterMap_len_lt (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
          g.inputs j hj (by rw [hm])
        have hcap := hg.2
        omega
    have hstep_env_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
        (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x i hi => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
      simp [List.getElem_append_left hi]
    have hstep_env_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
        (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
      List.getD_eq_default _ _ (by simp; omega)
    have hstep_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    intro i w' hiw'
    by_cases hi : i < env.length
    · have h1 : (rcStep nOut (out, env) g).2.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
        cases h : g.op
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; cases g.inputs with
          | nil => exact hstep_env_old _ i hi
          | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
      rw [h1] at hiw'
      rw [hget_old_x i hi, hget_old_y i hi]
      exact hagree i w' hiw'
    · by_cases heq : i = env.length
      · subst heq
        rw [hget_last_x, hget_last_y]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop] at hiw'
          cases hgi : g.inputs with
          | nil =>
            rw [hgi] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
          | cons j rest_i =>
            rw [hgi] at hiw'; dsimp only at hiw'
            cases hm : env.getD j (Sum.inl false) with
            | inl b => rw [hm] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
            | inr w0 =>
              rw [hop]
              simp only [GateOp.eval, List.map_cons, List.headD_cons, hagree j w0 hm]
      · exfalso
        have hlen_st : (rcStep nOut (out, env) g).2.length = env.length + 1 := rcStep_env_len nOut (out, env) g
        rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'

lemma rcCircuit_props (nIn nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (hlen0 : env0.length = nIn)
    (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g) :
    let res := rcCircuit nOut env0 gs o
    (∀ g ∈ res.1, legal g) ∧
    binaryCost res.1 ≤ binaryCost gs ∧
    (∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      Circuit.eval ⟨res.1, res.2⟩ ys = Circuit.eval ⟨gs, o⟩ xs) := by
  dsimp only [rcCircuit]
  have hfold_leg := rcFold_legal nOut gs ([], env0) (by intro g h; cases h) hM
  have hfold_bc : binaryCost (gs.foldl (rcStep nOut) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le nOut gs ([], env0); simpa [binaryCost] using this
  have hcore_eval : ∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      ∀ i, match (gs.foldl (rcStep nOut) ([], env0)).2.getD i (Sum.inl false) with
        | Sum.inl b => (gs.foldl step xs).getD i false = b
        | Sum.inr w' => w' < nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length ∧
            (gs.foldl step xs).getD i false = ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD w' false := by
    intro xs ys hxl hyl hinit
    have hinit' : ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut + (([] : List Gate), env0).1.length ∧ xs.getD i false = ((([] : List Gate), env0).1.foldl step ys).getD w' false := by
      intro i
      by_cases hi : i < nIn
      · simpa using hinit i hi
      · dsimp only
        rw [List.getD_eq_default _ _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
    exact (rcFold_eval_inv nOut gs ys hyl hM xs ([], env0) (by simp [hlen0, hxl]) hinit').2
  cases hm : (gs.foldl (rcStep nOut) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    refine ⟨hfold_leg, hfold_bc, ?_⟩
    intro xs ys hxl hyl hinit
    have h := hcore_eval xs ys hxl hyl hinit o
    rw [hm] at h; exact h.2.symm
  | inl b =>
    cases b with
    | false =>
      refine ⟨hfold_leg, hfold_bc, ?_⟩
      intro xs ys hxl hyl hinit
      have h := hcore_eval xs ys hxl hyl hinit o
      rw [hm] at h
      change ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
        (gs.foldl step xs).getD o false
      rw [h, List.getD_eq_default _ _ (by rw [wfold_len, hyl])]
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with h | rfl
        · exact hfold_leg g h
        · exact ⟨by simp, by decide⟩
      · rw [binaryCost_append_one]; simp [isBinary]; exact hfold_bc
      · intro xs ys hxl hyl hinit
        have h := hcore_eval xs ys hxl hyl hinit o
        rw [hm] at h
        change (((gs.foldl (rcStep nOut) ([], env0)).1 ++ [({ op := GateOp.not, inputs := [] } : Gate)]).foldl step ys).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
          (gs.foldl step xs).getD o false
        rw [h, List.foldl_append]
        change (step ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys) ({ op := GateOp.not, inputs := [] } : Gate)).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false = true
        have hlen : ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).length =
            nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length := by rw [wfold_len, hyl]
        rw [← hlen, List.getD_eq_getElem _ _ (by simp [step])]
        simp [step, GateOp.eval]


lemma rcCircuit_binCost_lt (n k : ℕ) (hk : k < n) (val : Bool) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = n) (hx2l : x2.length = n)
    (hagree_xy : ∀ i < n, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = n) (hz2l : z2.length = n)
    (hz1k : z1.getD k false = val) (hz2k : z2.getD k false = val)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl val else Sum.inr i.val
    binaryCost (rcCircuit n env0 gs o).1 + 1 ≤ binaryCost gs := by
  intro env0
  have hle_fold : binaryCost (gs.foldl (rcStep n) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le n gs ([], env0); simpa [binaryCost] using this
  have hbc_rc : binaryCost (rcCircuit n env0 gs o).1 = binaryCost (gs.foldl (rcStep n) ([], env0)).1 := by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep n) ([], env0)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  rw [hbc_rc]
  by_contra hlt
  have hzero : binaryCost ([] : List Gate) = 0 := rfl
  have heq_cost : binaryCost (gs.foldl (rcStep n) ([], env0)).1 = binaryCost ([] : List Gate) + binaryCost gs := by
    rw [hzero, Nat.zero_add]; omega
  cases hm : (gs.foldl (rcStep n) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    have hinit : ∀ i w0, (([] : List Gate), env0).2.getD i (Sum.inl false) = Sum.inr w0 → x1.getD i false = x2.getD i false := by
      intro i w0 hiw
      by_cases hi : i < n
      · dsimp only at hiw
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])] at hiw
        change (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) = Sum.inr w0 at hiw
        rw [List.getElem_ofFn] at hiw
        by_cases hik : i = k
        · simp [hik] at hiw
        · exact hagree_xy i hi hik
      · dsimp only at hiw
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)] at hiw; cases hiw
    have hsame := rcFold_inr_agree n gs hM x1 x2 ([], env0) (by simp [env0, hx1l]) (by simp [env0, hx2l])
      heq_cost hinit o w' hm
    exact hdiff_xy hsame
  | inl b =>
    have hinit_z : ∀ (z : List Bool), z.length = n → z.getD k false = val →
        ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < n + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
      intro z hzl hzk i
      by_cases hi : i < n
      · dsimp only
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
        change match (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < n + 0 ∧ z.getD i false = z.getD w' false
        rw [List.getElem_ofFn]
        by_cases hik : i = k
        · subst hik; simp only [ite_true]; exact hzk
        · simp [hik, hi]
      · dsimp only
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)]
        exact List.getD_eq_default z false (by omega)
    have hz1 := (rcFold_eval_inv n gs z1 hz1l hM z1 ([], env0) (by simp [env0, hz1l]) (hinit_z z1 hz1l hz1k)).2 o
    have hz2 := (rcFold_eval_inv n gs z2 hz2l hM z2 ([], env0) (by simp [env0, hz2l]) (hinit_z z2 hz2l hz2k)).2 o
    rw [hm] at hz1 hz2
    dsimp only at hz1 hz2
    exact hdiff_zz (hz1.trans hz2.symm)

lemma rcStep_env_old_getD (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (i : ℕ) (hi : i < st.2.length) :
    (rcStep nOut st g).2.getD i (Sum.inl false) = st.2.getD i (Sum.inl false) := by
  rcases st with ⟨out, env⟩
  dsimp only at hi ⊢
  have h1 : ∀ x : Bool ⊕ ℕ, (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
    simp [List.getElem_append_left hi]
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · exact h1 _
    · cases g.inputs.filterMap _ with | nil => exact h1 _ | cons a t => cases t <;> exact h1 _
  · simp only [rcStep, h]; split_ifs
    · exact h1 _
    · cases g.inputs.filterMap _ with | nil => exact h1 _ | cons a t => cases t <;> exact h1 _
  · simp only [rcStep, h]; cases g.inputs with
    | nil => exact h1 _
    | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact h1 _
  · simp only [rcStep, h]; exact h1 _
  · simp only [rcStep, h]; exact h1 _

lemma rcStep_bin_keep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', st.2.getD j (Sum.inl false) = Sum.inr w') :
    binaryCost (rcStep nOut st g).1 = binaryCost st.1 + 1 ∧
    ∃ w', (rcStep nOut st g).2.getD st.2.length (Sum.inl false) = Sum.inr w' := by
  rcases st with ⟨out, env⟩
  dsimp only at h2 ⊢
  obtain ⟨hl2, hall⟩ := h2
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [hins] at hl2
  · simp [hins] at hl2
  · obtain ⟨wa, hwa⟩ := hall a (by simp [hins])
    obtain ⟨wb, hwb⟩ := hall b (by simp [hins])
    rcases hop with hop | hop
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, hwa, hwb, Bool.or_false, Bool.false_eq_true, ite_false,
        List.filterMap_cons, List.filterMap_nil]
      refine ⟨by rw [binaryCost_append_one]; simp [isBinary], nOut + out.length, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, hwa, hwb, Bool.or_false, Bool.false_eq_true, ite_false,
        List.filterMap_cons, List.filterMap_nil]
      refine ⟨by rw [binaryCost_append_one]; simp [isBinary], nOut + out.length, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
  · simp [hins] at hl2

lemma rcStep_bin_drop (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hcap : g.inputs.length ≤ 2)
    (hnot2 : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', st.2.getD j (Sum.inl false) = Sum.inr w')) :
    binaryCost (rcStep nOut st g).1 = binaryCost st.1 := by
  rcases st with ⟨out, env⟩
  dsimp only at hnot2 ⊢
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with hop | hop <;> simp [rcStep, hop, hins]
  · rcases hop with hop | hop
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, Bool.or_false,
        List.filterMap_cons, List.filterMap_nil]
      cases env.getD a (Sum.inl false) with
      | inl bb => cases bb <;> rfl
      | inr wa => rfl
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, Bool.or_false,
        List.filterMap_cons, List.filterMap_nil]
      cases env.getD a (Sum.inl false) with
      | inl bb => cases bb <;> rfl
      | inr wa => rfl
  · have hex : ∃ j ∈ ([a, b] : List ℕ), ∀ w', env.getD j (Sum.inl false) ≠ Sum.inr w' := by
      by_contra hno
      apply hnot2
      refine ⟨by simp [hins], ?_⟩
      intro j hj
      rw [hins] at hj
      by_contra hno2
      exact hno ⟨j, hj, fun w' hw' => hno2 ⟨w', hw'⟩⟩
    obtain ⟨j, hj, hnj⟩ := hex
    have hflt : (([a, b] : List ℕ).filterMap fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length < 2 := by
      apply list_filterMap_len_lt _ [a, b] j hj
      cases hm : env.getD j (Sum.inl false) with
      | inl _ => rfl
      | inr w' => exact absurd hm (hnj w')
    rcases hop with hop | hop
    · simp only [rcStep, hop, hins]
      split_ifs
      · rfl
      · cases hf : ([a, b] : List ℕ).filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
        | nil => rfl
        | cons u t =>
          cases t with
          | nil => rfl
          | cons v t2 => rw [hf] at hflt; simp at hflt
    · simp only [rcStep, hop, hins]
      split_ifs
      · rfl
      · cases hf : ([a, b] : List ℕ).filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
        | nil => rfl
        | cons u t =>
          cases t with
          | nil => rfl
          | cons v t2 => rw [hf] at hflt; simp at hflt
  · simp [hins] at hcap

lemma rcStep_bin_inr_no_kill (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w' : ℕ) (hinr : (rcStep nOut st g).2.getD st.2.length (Sum.inl false) = Sum.inr w') :
    ∀ j ∈ g.inputs, ∀ b, st.2.getD j (Sum.inl false) = Sum.inl b →
      (g.op = GateOp.and → b = true) ∧ (g.op = GateOp.or → b = false) := by
  rcases st with ⟨out, env⟩
  dsimp only at hinr ⊢
  intro j hj b hjb
  rcases hop with hop | hop
  · refine ⟨(fun _ => ?_), (fun h => by rw [hop] at h; cases h)⟩
    cases b with
    | true => rfl
    | false =>
      exfalso
      have hany : g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) = true :=
        List.any_eq_true.mpr ⟨j, hj, by rw [hjb]⟩
      simp only [rcStep, hop, hany, ite_true] at hinr
      rw [List.getD_eq_getElem _ _ (by simp)] at hinr
      simp at hinr
  · refine ⟨(fun h => by rw [hop] at h; cases h), (fun _ => ?_)⟩
    cases b with
    | false => rfl
    | true =>
      exfalso
      have hany : g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) = true :=
        List.any_eq_true.mpr ⟨j, hj, by rw [hjb]⟩
      simp only [rcStep, hop, hany, ite_true] at hinr
      rw [List.getD_eq_getElem _ _ (by simp)] at hinr
      simp at hinr

lemma rcFold_two_elim_contra (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (stF stT : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = stF.2.length) (hylen : wy.length = stF.2.length)
    (hlenFT : stT.2.length = stF.2.length)
    (hshape : ∀ i, (∃ b, stF.2.getD i (Sum.inl false) = Sum.inl b) ↔
                   (∃ b, stT.2.getD i (Sum.inl false) = Sum.inl b))
    (hagreeF : ∀ i w', stF.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false)
    (hagreeT : ∀ i w', stT.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false)
    (hsameInl : ∀ i b, stF.2.getD i (Sum.inl false) = Sum.inl b →
                       stT.2.getD i (Sum.inl false) = Sum.inl b →
                       wx.getD i false = b ∧ wy.getD i false = b)
    (hcostF : binaryCost (gs.foldl (rcStep nOut) stF).1 + 1 = binaryCost stF.1 + binaryCost gs)
    (hcostT : binaryCost (gs.foldl (rcStep nOut) stT).1 + 1 = binaryCost stT.1 + binaryCost gs) :
    (∀ i w', (gs.foldl (rcStep nOut) stF).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false) ∨
    (∀ i w', (gs.foldl (rcStep nOut) stT).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false) := by
  induction gs generalizing wx wy stF stT with
  | nil =>
    simp [binaryCost] at hcostF
  | cons g rest ih =>
    simp only [List.foldl_cons] at hcostF hcostT ⊢
    have hg := hM g List.mem_cons_self
    have hMrest : ∀ g' ∈ rest, legal g' := fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')
    have hbc_cons : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hshape_inr : ∀ i, (∃ w', stF.2.getD i (Sum.inl false) = Sum.inr w') ↔
                           (∃ w', stT.2.getD i (Sum.inl false) = Sum.inr w') := by
      intro i
      cases hF : stF.2.getD i (Sum.inl false) <;> cases hT : stT.2.getD i (Sum.inl false)
      · simp
      · exfalso; obtain ⟨b, hb⟩ := (hshape i).mp ⟨_, hF⟩; rw [hT] at hb; cases hb
      · exfalso; obtain ⟨b, hb⟩ := (hshape i).mpr ⟨_, hT⟩; rw [hF] at hb; cases hb
      · simp
    set stF' := rcStep nOut stF g with hstF'
    set stT' := rcStep nOut stT g with hstT'
    set wx' := step wx g with hwx'
    set wy' := step wy g with hwy'
    have hlenF' : stF'.2.length = stF.2.length + 1 := rcStep_env_len nOut stF g
    have hlenT' : stT'.2.length = stF.2.length + 1 := by rw [rcStep_env_len, hlenFT]
    have hxlen' : wx'.length = stF'.2.length := by rw [hwx', hlenF']; simp [step, hxlen]
    have hylen' : wy'.length = stF'.2.length := by rw [hwy', hlenF']; simp [step, hylen]
    have hget_old_x : ∀ i < stF.2.length, wx'.getD i false = wx.getD i false := fun i hi => by
      rw [hwx', List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < stF.2.length, wy'.getD i false = wy.getD i false := fun i hi => by
      rw [hwy', List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : wx'.getD stF.2.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [hwx', ← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : wy'.getD stF.2.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [hwy', ← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hrc_oldF : ∀ i < stF.2.length, stF'.2.getD i (Sum.inl false) = stF.2.getD i (Sum.inl false) :=
      rcStep_env_old_getD nOut stF g
    have hrc_oldT : ∀ i < stF.2.length, stT'.2.getD i (Sum.inl false) = stT.2.getD i (Sum.inl false) := fun i hi =>
      rcStep_env_old_getD nOut stT g i (by omega)
    have hle_restF := rcFold_binCost_le nOut rest stF'
    have hle_restT := rcFold_binCost_le nOut rest stT'
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
    rcases hop with hop | hop | hop
    · have hbin : isBinary g = true := by simp [isBinary, hop]
      by_cases h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stF.2.getD j (Sum.inl false) = Sum.inr w'
      · have h2T : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w' :=
          ⟨h2.1, fun j hj => (hshape_inr j).mp (h2.2 j hj)⟩
        obtain ⟨hcF, wF, hwF⟩ := rcStep_bin_keep nOut stF g (Or.inl hop) h2
        obtain ⟨hcT, wT, hwT⟩ := rcStep_bin_keep nOut stT g (Or.inl hop) h2T
        have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
          rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
          intro j hj; obtain ⟨w0, hw0⟩ := h2.2 j hj; exact hagreeF j w0 hw0
        apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
        · intro i
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF, ← hlenFT, hwT]; simp
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i b hF hT
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
            rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF] at hF; cases hF
            · rw [List.getD_eq_default _ _ (by omega)] at hF
              cases hF
              exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
        · simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        · simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
      · have hnot2T : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w') :=
          fun h2T => h2 ⟨h2T.1, fun j hj => (hshape_inr j).mpr (h2T.2 j hj)⟩
        have hcF := rcStep_bin_drop nOut stF g (Or.inl hop) hg.2 h2
        have hcT := rcStep_bin_drop nOut stT g (Or.inl hop) hg.2 hnot2T
        have hrestF : binaryCost (rest.foldl (rcStep nOut) stF').1 = binaryCost stF'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        have hrestT : binaryCost (rest.foldl (rcStep nOut) stT').1 = binaryCost stT'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
        cases hlastF : stF'.2.getD stF.2.length (Sum.inl false) with
        | inl bf =>
          left
          refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
          intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hlastF] at hiw'; cases hiw'
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        | inr wF =>
          cases hlastT : stT'.2.getD stF.2.length (Sum.inl false) with
          | inl bt =>
            right
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stT' (by omega) (by omega) hrestT ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; rw [hlastT] at hiw'; cases hiw'
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
          | inr wT =>
            left
            have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
              rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
              intro j hj
              cases hjF : stF.2.getD j (Sum.inl false) with
              | inr w0 => exact hagreeF j w0 hjF
              | inl bF =>
                obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
                have hbF : bF = true := (rcStep_bin_inr_no_kill nOut stF g (Or.inl hop) wF hlastF j hj bF hjF).1 hop
                have hbT : bT = true := (rcStep_bin_inr_no_kill nOut stT g (Or.inl hop) wT (by rw [hlenFT]; exact hlastT) j hj bT hjT).1 hop
                subst hbF; subst hbT
                have hxy := hsameInl j true hjF hjT
                exact hxy.1.trans hxy.2.symm
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; exact hlast_eq
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
    · have hbin : isBinary g = true := by simp [isBinary, hop]
      by_cases h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stF.2.getD j (Sum.inl false) = Sum.inr w'
      · have h2T : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w' :=
          ⟨h2.1, fun j hj => (hshape_inr j).mp (h2.2 j hj)⟩
        obtain ⟨hcF, wF, hwF⟩ := rcStep_bin_keep nOut stF g (Or.inr hop) h2
        obtain ⟨hcT, wT, hwT⟩ := rcStep_bin_keep nOut stT g (Or.inr hop) h2T
        have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
          rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
          intro j hj; obtain ⟨w0, hw0⟩ := h2.2 j hj; exact hagreeF j w0 hw0
        apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
        · intro i
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF, ← hlenFT, hwT]; simp
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i b hF hT
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
            rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF] at hF; cases hF
            · rw [List.getD_eq_default _ _ (by omega)] at hF
              cases hF
              exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
        · simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        · simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
      · have hnot2T : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w') :=
          fun h2T => h2 ⟨h2T.1, fun j hj => (hshape_inr j).mpr (h2T.2 j hj)⟩
        have hcF := rcStep_bin_drop nOut stF g (Or.inr hop) hg.2 h2
        have hcT := rcStep_bin_drop nOut stT g (Or.inr hop) hg.2 hnot2T
        have hrestF : binaryCost (rest.foldl (rcStep nOut) stF').1 = binaryCost stF'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        have hrestT : binaryCost (rest.foldl (rcStep nOut) stT').1 = binaryCost stT'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
        cases hlastF : stF'.2.getD stF.2.length (Sum.inl false) with
        | inl bf =>
          left
          refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
          intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hlastF] at hiw'; cases hiw'
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        | inr wF =>
          cases hlastT : stT'.2.getD stF.2.length (Sum.inl false) with
          | inl bt =>
            right
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stT' (by omega) (by omega) hrestT ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; rw [hlastT] at hiw'; cases hiw'
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
          | inr wT =>
            left
            have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
              rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
              intro j hj
              cases hjF : stF.2.getD j (Sum.inl false) with
              | inr w0 => exact hagreeF j w0 hjF
              | inl bF =>
                obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
                have hbF : bF = false := (rcStep_bin_inr_no_kill nOut stF g (Or.inr hop) wF hlastF j hj bF hjF).2 hop
                have hbT : bT = false := (rcStep_bin_inr_no_kill nOut stT g (Or.inr hop) wT (by rw [hlenFT]; exact hlastT) j hj bT hjT).2 hop
                subst hbF; subst hbT
                have hxy := hsameInl j false hjF hjT
                exact hxy.1.trans hxy.2.symm
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; exact hlast_eq
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
    · have hbin : isBinary g = false := by simp [isBinary, hop]
      have hcF : binaryCost stF'.1 = binaryCost stF.1 := by
        rw [hstF']
        simp only [rcStep, hop]
        cases g.inputs with
        | nil => rfl
        | cons j _ =>
          dsimp only
          cases stF.2.getD j (Sum.inl false) with
          | inl _ => rfl
          | inr _ => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
      have hcT : binaryCost stT'.1 = binaryCost stT.1 := by
        rw [hstT']
        simp only [rcStep, hop]
        cases g.inputs with
        | nil => rfl
        | cons j _ =>
          dsimp only
          cases stT.2.getD j (Sum.inl false) with
          | inl _ => rfl
          | inr _ => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
      have hlast_cases :
          ((∃ b, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl b) ↔
           (∃ b, stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl b)) ∧
          ((∃ w', stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr w') →
            wx'.getD stF.2.length false = wy'.getD stF.2.length false) ∧
          (∀ b, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl b →
                stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl b →
                wx'.getD stF.2.length false = b ∧ wy'.getD stF.2.length false = b) := by
        cases hgi : g.inputs with
        | nil =>
          have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl true := by
            rw [hstF']; simp only [rcStep, hop, hgi]
            rw [List.getD_eq_getElem _ _ (by simp)]; simp
          have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl true := by
            rw [hstT']; simp only [rcStep, hop, hgi]
            rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
          rw [hlF, hlT]
          refine ⟨(by simp), (fun ⟨_, h⟩ => by cases h), (fun b hb _ => ?_)⟩
          cases hb
          rw [hget_last_x, hget_last_y, hop, hgi]
          exact ⟨rfl, rfl⟩
        | cons j _ =>
          cases hjF : stF.2.getD j (Sum.inl false) with
          | inl bF =>
            obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
            have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl (!bF) := by
              rw [hstF']; simp only [rcStep, hop, hgi, hjF]
              rw [List.getD_eq_getElem _ _ (by simp)]; simp
            have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl (!bT) := by
              rw [hstT']; simp only [rcStep, hop, hgi, hjT]
              rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
            rw [hlF, hlT]
            refine ⟨(by simp), (fun ⟨_, h⟩ => by cases h), (fun b hbF hbT => ?_)⟩
            have he1 : (!bF) = b := Sum.inl.inj hbF
            have he2 : (!bT) = b := Sum.inl.inj hbT
            have hbt : bF = bT := by
              have he : (!bF) = (!bT) := he1.trans he2.symm
              cases bF <;> cases bT <;> first | rfl | cases he
            subst hbt
            have hxy := hsameInl j bF hjF hjT
            rw [hget_last_x, hget_last_y, hop, hgi]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, hxy.1, hxy.2, he1, and_self]
          | inr wF =>
            obtain ⟨wT, hjT⟩ := (hshape_inr j).mp ⟨wF, hjF⟩
            have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr (nOut + stF.1.length) := by
              rw [hstF']; simp only [rcStep, hop, hgi, hjF]
              rw [List.getD_eq_getElem _ _ (by simp)]; simp
            have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inr (nOut + stT.1.length) := by
              rw [hstT']; simp only [rcStep, hop, hgi, hjT]
              rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
            rw [hlF, hlT]
            refine ⟨(by simp), (fun _ => ?_), (fun _ h _ => by cases h)⟩
            rw [hget_last_x, hget_last_y, hop, hgi]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, hagreeF j wF hjF]
      apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
      · intro i
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.1
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · intro i w' hiw'
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.2.1 ⟨w', hiw'⟩
          · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
      · intro i w' hiw'
        by_cases hi : i < stF.2.length
        · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
        · by_cases heq : i = stF.2.length
          · subst heq
            have hF_inr : ∃ w0, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr w0 := by
              cases hF : stF'.2.getD stF.2.length (Sum.inl false) with
              | inr w0 => exact ⟨w0, rfl⟩
              | inl b0 =>
                exfalso; obtain ⟨b1, hb1⟩ := hlast_cases.1.mp ⟨b0, hF⟩
                rw [hiw'] at hb1; cases hb1
            exact hlast_cases.2.1 hF_inr
          · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
      · intro i b hF hT
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
          rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.2.2 b hF hT
          · rw [List.getD_eq_default _ _ (by omega)] at hF
            cases hF
            exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
      · simp only [hbc_cons, hbin, Bool.false_eq_true, ite_false, Nat.add_zero] at hcostF; omega
      · simp only [hbc_cons, hbin, Bool.false_eq_true, ite_false, Nat.add_zero] at hcostT; omega

lemma rcCircuit_binCost_two_elim (n k : ℕ) (hk : k < n) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = n) (hx2l : x2.length = n)
    (hagree_xy : ∀ i < n, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = n) (hz2l : z2.length = n)
    (hz1k : z1.getD k false = false) (hz2k : z2.getD k false = false)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2)
    (w1 w2 : List Bool) (hw1l : w1.length = n) (hw2l : w2.length = n)
    (hw1k : w1.getD k false = true) (hw2k : w2.getD k false = true)
    (hdiff_ww : Circuit.eval ⟨gs, o⟩ w1 ≠ Circuit.eval ⟨gs, o⟩ w2) :
    ∃ val : Bool,
      let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl val else Sum.inr i.val
      binaryCost (rcCircuit n env0 gs o).1 + 2 ≤ binaryCost gs := by
  let envF : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl false else Sum.inr i.val
  let envT : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl true else Sum.inr i.val
  have hltF : binaryCost (rcCircuit n envF gs o).1 + 1 ≤ binaryCost gs :=
    rcCircuit_binCost_lt n k hk false gs o hM x1 x2 hx1l hx2l hagree_xy hdiff_xy z1 z2 hz1l hz2l hz1k hz2k hdiff_zz
  have hltT : binaryCost (rcCircuit n envT gs o).1 + 1 ≤ binaryCost gs :=
    rcCircuit_binCost_lt n k hk true gs o hM x1 x2 hx1l hx2l hagree_xy hdiff_xy w1 w2 hw1l hw2l hw1k hw2k hdiff_ww
  by_cases h2F : binaryCost (rcCircuit n envF gs o).1 + 2 ≤ binaryCost gs
  · exact ⟨false, h2F⟩
  by_cases h2T : binaryCost (rcCircuit n envT gs o).1 + 2 ≤ binaryCost gs
  · exact ⟨true, h2T⟩
  exfalso
  have hbc_rc : ∀ env : List (Bool ⊕ ℕ),
      binaryCost (rcCircuit n env gs o).1 = binaryCost (gs.foldl (rcStep n) ([], env)).1 := fun env => by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep n) ([], env)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  have hcostF : binaryCost (gs.foldl (rcStep n) ([], envF)).1 + 1 = binaryCost ([] : List Gate) + binaryCost gs := by
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    rw [← hbc_rc envF, h0, Nat.zero_add]; omega
  have hcostT : binaryCost (gs.foldl (rcStep n) ([], envT)).1 + 1 = binaryCost ([] : List Gate) + binaryCost gs := by
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    rw [← hbc_rc envT, h0, Nat.zero_add]; omega
  have henv_at : ∀ (val : Bool) (i : ℕ),
      (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val).getD i (Sum.inl false) =
        if i < n then (if i = k then Sum.inl val else Sum.inr i) else Sum.inl false := fun val i => by
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]; simp [hi]
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]
  have hcontra := rcFold_two_elim_contra n gs hM x1 x2 ([], envF) ([], envT)
    (by simp [envF, hx1l]) (by simp [envF, hx2l]) (by simp [envF, envT])
    (by intro i; dsimp only; rw [henv_at false i, henv_at true i]; split_ifs <;> simp)
    (by intro i w' hiw'; dsimp only at hiw'; rw [henv_at false i] at hiw'
        by_cases hi : i < n
        · simp only [hi, ite_true] at hiw'
          by_cases hik : i = k
          · simp [hik] at hiw'
          · exact hagree_xy i hi hik
        · simp [hi] at hiw')
    (by intro i w' hiw'; dsimp only at hiw'; rw [henv_at true i] at hiw'
        by_cases hi : i < n
        · simp only [hi, ite_true] at hiw'
          by_cases hik : i = k
          · simp [hik] at hiw'
          · exact hagree_xy i hi hik
        · simp [hi] at hiw')
    (by intro i b hF hT; dsimp only at hF hT; rw [henv_at false i] at hF; rw [henv_at true i] at hT
        by_cases hi : i < n
        · simp only [hi, ite_true] at hF hT
          by_cases hik : i = k
          · simp only [hik, ite_true] at hF hT; cases hF; cases hT
          · simp [hik] at hF
        · simp only [hi, ite_false] at hF; cases hF
          exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩)
    hcostF hcostT
  have hinit_val : ∀ (val : Bool) (z : List Bool), z.length = n → z.getD k false = val →
      ∀ i, match (([] : List Gate), List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val).2.getD i (Sum.inl false) with
        | Sum.inl b0 => z.getD i false = b0
        | Sum.inr w' => w' < n + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
    intro val z hzl hzk i
    dsimp only; rw [henv_at val i]
    by_cases hi : i < n
    · simp only [hi, ite_true]
      by_cases hik : i = k
      · subst hik; simp only [ite_true]; exact hzk
      · simp [hik, hi]
    · simp only [hi, ite_false]
      exact List.getD_eq_default z false (by omega)
  rcases hcontra with hF_ag | hT_ag
  · cases hm : (gs.foldl (rcStep n) ([], envF)).2.getD o (Sum.inl false) with
    | inr w' => exact hdiff_xy (hF_ag o w' hm)
    | inl b =>
      have hz1 := (rcFold_eval_inv n gs z1 hz1l hM z1 ([], envF) (by simp [envF, hz1l]) (hinit_val false z1 hz1l hz1k)).2 o
      have hz2 := (rcFold_eval_inv n gs z2 hz2l hM z2 ([], envF) (by simp [envF, hz2l]) (hinit_val false z2 hz2l hz2k)).2 o
      rw [hm] at hz1 hz2; dsimp only at hz1 hz2
      exact hdiff_zz (hz1.trans hz2.symm)
  · cases hm : (gs.foldl (rcStep n) ([], envT)).2.getD o (Sum.inl false) with
    | inr w' => exact hdiff_xy (hT_ag o w' hm)
    | inl b =>
      have hw1 := (rcFold_eval_inv n gs w1 hw1l hM w1 ([], envT) (by simp [envT, hw1l]) (hinit_val true w1 hw1l hw1k)).2 o
      have hw2 := (rcFold_eval_inv n gs w2 hw2l hM w2 ([], envT) (by simp [envT, hw2l]) (hinit_val true w2 hw2l hw2k)).2 o
      rw [hm] at hw1 hw2; dsimp only at hw1 hw2
      exact hdiff_ww (hw1.trans hw2.symm)

def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

lemma fixEnv_eval (k : ℕ) (hk : k < 8) (val : Bool) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x : Fin 8 → Bool) (hxk : x ⟨k, hk⟩ = val) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = k then Sum.inl val else Sum.inr i.val
    let C' := rcCircuit 8 env0 gs o
    Circuit.eval ⟨C'.1, C'.2⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
  intro env0 C'
  have hprops := rcCircuit_props 8 8 env0 (by simp [env0]) gs o hM
  refine hprops.2.2 (List.ofFn x) (List.ofFn x) (by simp) (by simp) ?_
  intro i hi
  rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
  change match (List.ofFn fun j : Fin 8 => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) with
    | Sum.inl b => (List.ofFn x).getD i false = b
    | Sum.inr w' => w' < 8 ∧ (List.ofFn x).getD i false = (List.ofFn x).getD w' false
  rw [List.getElem_ofFn]
  by_cases hik : i = k
  · subst hik; simp only [ite_true]; rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]; exact hxk
  · simp [hik, hi]

def lift (b4 : Bool) (y : Fin 6 → Bool) : Fin 8 → Bool
  | ⟨0, _⟩ => y 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => b4
  | ⟨3, _⟩ => y 2
  | ⟨4, _⟩ => y 3
  | ⟨5, _⟩ => y 4
  | ⟨6, _⟩ => false
  | ⟨7, _⟩ => y 5

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_lift : ∀ (b4 : Bool) (y : Fin 6 → Bool), target (lift b4 y) = Signed.targetFun y := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem binary_bound (done : Signed.Tokens.remaining 0 = true) (gates : List Gate) (o : ℕ) (hleg' : ∀ g ∈ gates, legal g)
    (heval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target x) : 12 < binaryCost gates := by
  have h1_ex : ∃ b4 : Bool,
      let env1 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 2 then Sum.inl b4 else Sum.inr i.val
      binaryCost (rcCircuit 8 env1 gates o).1 + 2 ≤ binaryCost gates := by
    let fx1 : Fin 8 → Bool := fun i => decide (i.val = 6 ∨ i.val = 2)
    let fx2 : Fin 8 → Bool := fun i => decide (i.val = 6)
    let fz1 : Fin 8 → Bool := fun _ => false
    let fz2 : Fin 8 → Bool := fun i => decide (i.val = 3 ∨ i.val = 0)
    let fw1 : Fin 8 → Bool := fun i => decide (i.val = 2)
    let fw2 : Fin 8 → Bool := fun i => decide (i.val = 6 ∨ i.val = 2)
    exact rcCircuit_binCost_two_elim 8 2 (by decide) gates o hleg'
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by decide)
      (by rw [heval fx1, heval fx2]; decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by decide) (by decide)
      (by rw [heval fz1, heval fz2]; decide)
      (List.ofFn fw1) (List.ofFn fw2) (by simp) (by simp) (by decide) (by decide)
      (by rw [heval fw1, heval fw2]; decide)
  obtain ⟨b4, h1_lt⟩ := h1_ex
  let env1 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 2 then Sum.inl b4 else Sum.inr i.val
  let C1 := rcCircuit 8 env1 gates o
  have h1_lt' : binaryCost C1.1 + 2 ≤ binaryCost gates := h1_lt
  have h1_props := rcCircuit_props 8 8 env1 (by simp [env1]) gates o hleg'
  have h1_eval : ∀ x : Fin 8 → Bool, x 2 = b4 → Circuit.eval ⟨C1.1, C1.2⟩ (List.ofFn x) = target x :=
    fun x hx4 => (fixEnv_eval 2 (by decide) b4 gates o hleg' x hx4).trans (heval x)
  let env2 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 6 then Sum.inl false else Sum.inr i.val
  let C2 := rcCircuit 8 env2 C1.1 C1.2
  have h2_props := rcCircuit_props 8 8 env2 (by simp [env2]) C1.1 C1.2 h1_props.1
  have h2_eval : ∀ x : Fin 8 → Bool, x 2 = b4 → x 6 = false → Circuit.eval ⟨C2.1, C2.2⟩ (List.ofFn x) = target x :=
    fun x hx4 hx0 => (fixEnv_eval 6 (by decide) false C1.1 C1.2 h1_props.1 x hx0).trans (h1_eval x hx4)
  have h2_lt : binaryCost C2.1 + 1 ≤ binaryCost C1.1 := by
    let fx1 : Fin 8 → Bool := fun i => if i.val = 2 then b4 else decide (i.val = 6 ∨ i.val = 0)
    let fx2 : Fin 8 → Bool := fun i => if i.val = 2 then b4 else decide (i.val = 0)
    let fz1 : Fin 8 → Bool := fun i => if i.val = 2 then b4 else false
    let fz2 : Fin 8 → Bool := fun i => if i.val = 2 then b4 else decide (i.val = 3 ∨ i.val = 0)
    exact rcCircuit_binCost_lt 8 6 (by decide) false C1.1 C1.2 h1_props.1
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by cases b4 <;> decide)
      (by rw [h1_eval fx1 rfl, h1_eval fx2 rfl]; cases b4 <;> decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by cases b4 <;> decide) (by cases b4 <;> decide)
      (by rw [h1_eval fz1 rfl, h1_eval fz2 rfl]; cases b4 <;> decide)
  let envP : List (Bool ⊕ ℕ) := [Sum.inr 0, Sum.inr 1, Sum.inl b4, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inl false, Sum.inr 5]
  let CP := rcCircuit 6 envP C2.1 C2.2
  have hP_props := rcCircuit_props 8 6 envP (by simp [envP]) C2.1 C2.2 h2_props.1
  have hP_eval : ∀ y : Fin 6 → Bool, Circuit.eval ⟨CP.1, CP.2⟩ (List.ofFn y) = Signed.targetFun y := by
    intro y
    rw [hP_props.2.2 (List.ofFn (lift b4 y)) (List.ofFn y) (by simp) (by simp) ?_,
        h2_eval (lift b4 y) rfl rfl, target_lift b4 y]
    intro i hi
    interval_cases i
    · exact ⟨by decide, by simp [lift]⟩
    · exact ⟨by decide, by simp [lift]⟩
    · simp [envP, lift]
    · exact ⟨by decide, by simp [lift]⟩
    · exact ⟨by decide, by simp [lift]⟩
    · exact ⟨by decide, by simp [lift]⟩
    · simp [envP, lift]
    · exact ⟨by decide, by simp [lift]⟩
  have lb := Signed.bound_from_impossible 9 (Signed.no_small done) CP.1 CP.2 hP_props.1 hP_eval
  have hP_le : binaryCost CP.1 ≤ binaryCost C2.1 := hP_props.2.1
  omega

def witness : List Gate := [⟨.or, [3, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [0, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [16, 20]⟩]

theorem witness_mono : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_30815_aux

namespace PEqualNP.Outside.L_meta_30815_aux

theorem finalReduction (done : Signed.Tokens.remaining 0 = true) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_30815_aux.Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_30815_aux.Signed.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_30815_aux.Signed.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_30815_aux.binary_bound done gates o (fun g hg => fits g hg) computes
    have hl : PEqualNP.Outside.L_meta_30815_aux.witness.length = 14 := rfl
    exact ⟨PEqualNP.Outside.L_meta_30815_aux.witness, 21, PEqualNP.Outside.L_meta_30815_aux.witness_mono, by omega, PEqualNP.Outside.L_meta_30815_aux.witness_eval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

end PEqualNP.Outside.L_meta_30815_aux

namespace PEqualNP.Outside.L_meta_30815_aux.Signed.Tokens
theorem joinBatch {i n m : Nat} (a : batch i n = true) (b : batch (i+n) m = true) :
    batch i (n+m) = true := by
  unfold batch at *
  simp only [List.take_add,List.all_append,List.drop_drop,a,b,Bool.true_and]
def passPair (ns : List Nat) (p : Nat × Nat × List Nat) : Bool :=
  !Fast.dispatchN (8-ns.length) (Fast.run 6) p.1 p.2.1 p.2.2
def pairBatch (i pos n : Nat) :=
  ((((pairs (witness i)).drop pos).take n).all (passPair (witness i)))
def pairTail (i pos : Nat) :=
  (((pairs (witness i)).drop pos).all (passPair (witness i)))
theorem joinPair {i pos n : Nat} (a : pairBatch i pos n = true) (b : pairTail i (pos+n) = true) :
    pairTail i pos = true := by
  unfold pairBatch at a
  unfold pairTail at *
  rw [←List.take_append_drop n ((pairs (witness i)).drop pos), List.all_append, a,
    Bool.true_and, List.drop_drop]
  exact b
theorem fromPairs {i : Nat} (nd : (witness i).Nodup)
    (out : ((witness i == [Fast.highGoal]) || (witness i == [Fast.mask])) = false)
    (h : pairTail i 0 = true) : valid (witness i) = true := by
  change (decide (witness i).Nodup && !(((witness i == [Fast.highGoal]) || (witness i == [Fast.mask])) ||
    (pairs (witness i)).any (fun (a,b,r) => Fast.dispatchN (8-(witness i).length) (Fast.run 6) a b r))) = true
  simp only [decide_eq_true nd,Bool.true_and,Bool.not_eq_true',out,Bool.false_or]
  apply List.any_eq_false.mpr
  rintro ⟨a,b,r⟩ hp hpos
  have q := List.all_eq_true.mp h (a,b,r) hp
  have no : Fast.dispatchN (8-(witness i).length) (Fast.run 6) a b r = false := by
    simpa only [passPair,Bool.not_eq_true'] using q
  exact Bool.noConfusion (no.symm.trans hpos)
theorem oneFromPairs {i : Nat}
    (idx : (((List.range 4125).drop i).take 1) = [i])
    (h : valid (witness i) = true) : batch i 1 = true := by
  simp only [batch,idx,List.all_cons,List.all_nil,acceptID,h,Bool.true_and]
theorem stitch {i n : Nat} (a : batch i n = true) (b : remaining (i+n) = true) :
    remaining i = true := by
  unfold batch at a
  unfold remaining at *
  rw [←List.take_append_drop n ((List.range 4125).drop i),List.all_append,a,Bool.true_and,List.drop_drop]
  exact b
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock0 (tail : remaining 96 = true) : remaining 0 = true := by
  have b0 : batch 0 4 = true := by decide +kernel
  have b4 : batch 4 4 = true := by decide +kernel
  have b8 : batch 8 4 = true := by decide +kernel
  have b12 : batch 12 4 = true := by decide +kernel
  have b16 : batch 16 4 = true := by decide +kernel
  have b20 : batch 20 4 = true := by decide +kernel
  have b24 : batch 24 4 = true := by decide +kernel
  have b28 : batch 28 4 = true := by decide +kernel
  have b32 : batch 32 4 = true := by decide +kernel
  have b36 : batch 36 4 = true := by decide +kernel
  have b40 : batch 40 4 = true := by decide +kernel
  have b44 : batch 44 4 = true := by decide +kernel
  have b48 : batch 48 4 = true := by decide +kernel
  have b52 : batch 52 4 = true := by decide +kernel
  have b56 : batch 56 4 = true := by decide +kernel
  have b60 : batch 60 4 = true := by decide +kernel
  have b64 : batch 64 4 = true := by decide +kernel
  have b68 : batch 68 4 = true := by decide +kernel
  have b72 : batch 72 4 = true := by decide +kernel
  have b76 : batch 76 4 = true := by decide +kernel
  have b80 : batch 80 4 = true := by decide +kernel
  have b84 : batch 84 4 = true := by decide +kernel
  have b88 : batch 88 4 = true := by decide +kernel
  have b92 : batch 92 4 = true := by decide +kernel
  exact (@stitch 0 4 b0 (@stitch 4 4 b4 (@stitch 8 4 b8 (@stitch 12 4 b12 (@stitch 16 4 b16 (@stitch 20 4 b20 (@stitch 24 4 b24 (@stitch 28 4 b28 (@stitch 32 4 b32 (@stitch 36 4 b36 (@stitch 40 4 b40 (@stitch 44 4 b44 (@stitch 48 4 b48 (@stitch 52 4 b52 (@stitch 56 4 b56 (@stitch 60 4 b60 (@stitch 64 4 b64 (@stitch 68 4 b68 (@stitch 72 4 b72 (@stitch 76 4 b76 (@stitch 80 4 b80 (@stitch 84 4 b84 (@stitch 88 4 b88 (@stitch 92 4 b92 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock96 (tail : remaining 192 = true) : remaining 96 = true := by
  have b96 : batch 96 4 = true := by decide +kernel
  have b100 : batch 100 4 = true := by decide +kernel
  have b104 : batch 104 4 = true := by decide +kernel
  have b108 : batch 108 4 = true := by decide +kernel
  have b112 : batch 112 4 = true := by decide +kernel
  have b116 : batch 116 4 = true := by decide +kernel
  have b120 : batch 120 4 = true := by decide +kernel
  have b124 : batch 124 4 = true := by decide +kernel
  have b128 : batch 128 4 = true := by decide +kernel
  have b132 : batch 132 4 = true := by decide +kernel
  have b136 : batch 136 4 = true := by decide +kernel
  have b140 : batch 140 4 = true := by decide +kernel
  have b144 : batch 144 4 = true := by decide +kernel
  have b148 : batch 148 4 = true := by decide +kernel
  have b152 : batch 152 4 = true := by decide +kernel
  have b156 : batch 156 4 = true := by decide +kernel
  have b160 : batch 160 4 = true := by decide +kernel
  have b164 : batch 164 4 = true := by decide +kernel
  have b168 : batch 168 4 = true := by decide +kernel
  have b172 : batch 172 4 = true := by decide +kernel
  have b176 : batch 176 4 = true := by decide +kernel
  have b180 : batch 180 4 = true := by decide +kernel
  have b184 : batch 184 4 = true := by decide +kernel
  have b188 : batch 188 4 = true := by decide +kernel
  exact (@stitch 96 4 b96 (@stitch 100 4 b100 (@stitch 104 4 b104 (@stitch 108 4 b108 (@stitch 112 4 b112 (@stitch 116 4 b116 (@stitch 120 4 b120 (@stitch 124 4 b124 (@stitch 128 4 b128 (@stitch 132 4 b132 (@stitch 136 4 b136 (@stitch 140 4 b140 (@stitch 144 4 b144 (@stitch 148 4 b148 (@stitch 152 4 b152 (@stitch 156 4 b156 (@stitch 160 4 b160 (@stitch 164 4 b164 (@stitch 168 4 b168 (@stitch 172 4 b172 (@stitch 176 4 b176 (@stitch 180 4 b180 (@stitch 184 4 b184 (@stitch 188 4 b188 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock192 (tail : remaining 288 = true) : remaining 192 = true := by
  have b192 : batch 192 4 = true := by decide +kernel
  have b196 : batch 196 4 = true := by decide +kernel
  have b200 : batch 200 4 = true := by decide +kernel
  have b204 : batch 204 4 = true := by decide +kernel
  have b208 : batch 208 4 = true := by decide +kernel
  have b212 : batch 212 4 = true := by decide +kernel
  have b216 : batch 216 4 = true := by decide +kernel
  have b220 : batch 220 4 = true := by decide +kernel
  have b224 : batch 224 4 = true := by decide +kernel
  have b228 : batch 228 4 = true := by decide +kernel
  have b232 : batch 232 4 = true := by decide +kernel
  have b236 : batch 236 4 = true := by decide +kernel
  have b240 : batch 240 4 = true := by decide +kernel
  have b244 : batch 244 4 = true := by decide +kernel
  have b248 : batch 248 4 = true := by decide +kernel
  have v252 : batch 252 1 = true := by decide +kernel
  have v253 : batch 253 1 = true := by decide +kernel
  have v254 : batch 254 1 = true := by decide +kernel
  have v255 : batch 255 1 = true := by decide +kernel
  have b252 : batch 252 4 = true := (joinBatch v252 (joinBatch v253 (joinBatch v254 v255)))
  have b256 : batch 256 4 = true := by decide +kernel
  have b260 : batch 260 4 = true := by decide +kernel
  have b264 : batch 264 4 = true := by decide +kernel
  have b268 : batch 268 4 = true := by decide +kernel
  have b272 : batch 272 4 = true := by decide +kernel
  have b276 : batch 276 4 = true := by decide +kernel
  have b280 : batch 280 4 = true := by decide +kernel
  have b284 : batch 284 4 = true := by decide +kernel
  exact (@stitch 192 4 b192 (@stitch 196 4 b196 (@stitch 200 4 b200 (@stitch 204 4 b204 (@stitch 208 4 b208 (@stitch 212 4 b212 (@stitch 216 4 b216 (@stitch 220 4 b220 (@stitch 224 4 b224 (@stitch 228 4 b228 (@stitch 232 4 b232 (@stitch 236 4 b236 (@stitch 240 4 b240 (@stitch 244 4 b244 (@stitch 248 4 b248 (@stitch 252 4 b252 (@stitch 256 4 b256 (@stitch 260 4 b260 (@stitch 264 4 b264 (@stitch 268 4 b268 (@stitch 272 4 b272 (@stitch 276 4 b276 (@stitch 280 4 b280 (@stitch 284 4 b284 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock288 (tail : remaining 384 = true) : remaining 288 = true := by
  have b288 : batch 288 4 = true := by decide +kernel
  have b292 : batch 292 4 = true := by decide +kernel
  have b296 : batch 296 4 = true := by decide +kernel
  have b300 : batch 300 4 = true := by decide +kernel
  have b304 : batch 304 4 = true := by decide +kernel
  have b308 : batch 308 4 = true := by decide +kernel
  have b312 : batch 312 4 = true := by decide +kernel
  have b316 : batch 316 4 = true := by decide +kernel
  have b320 : batch 320 4 = true := by decide +kernel
  have b324 : batch 324 4 = true := by decide +kernel
  have b328 : batch 328 4 = true := by decide +kernel
  have b332 : batch 332 4 = true := by decide +kernel
  have b336 : batch 336 4 = true := by decide +kernel
  have b340 : batch 340 4 = true := by decide +kernel
  have b344 : batch 344 4 = true := by decide +kernel
  have b348 : batch 348 4 = true := by decide +kernel
  have b352 : batch 352 4 = true := by decide +kernel
  have b356 : batch 356 4 = true := by decide +kernel
  have b360 : batch 360 4 = true := by decide +kernel
  have b364 : batch 364 4 = true := by decide +kernel
  have b368 : batch 368 4 = true := by decide +kernel
  have b372 : batch 372 4 = true := by decide +kernel
  have b376 : batch 376 4 = true := by decide +kernel
  have b380 : batch 380 4 = true := by decide +kernel
  exact (@stitch 288 4 b288 (@stitch 292 4 b292 (@stitch 296 4 b296 (@stitch 300 4 b300 (@stitch 304 4 b304 (@stitch 308 4 b308 (@stitch 312 4 b312 (@stitch 316 4 b316 (@stitch 320 4 b320 (@stitch 324 4 b324 (@stitch 328 4 b328 (@stitch 332 4 b332 (@stitch 336 4 b336 (@stitch 340 4 b340 (@stitch 344 4 b344 (@stitch 348 4 b348 (@stitch 352 4 b352 (@stitch 356 4 b356 (@stitch 360 4 b360 (@stitch 364 4 b364 (@stitch 368 4 b368 (@stitch 372 4 b372 (@stitch 376 4 b376 (@stitch 380 4 b380 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock384 (tail : remaining 480 = true) : remaining 384 = true := by
  have b384 : batch 384 4 = true := by decide +kernel
  have b388 : batch 388 4 = true := by decide +kernel
  have b392 : batch 392 4 = true := by decide +kernel
  have b396 : batch 396 4 = true := by decide +kernel
  have b400 : batch 400 4 = true := by decide +kernel
  have b404 : batch 404 4 = true := by decide +kernel
  have b408 : batch 408 4 = true := by decide +kernel
  have b412 : batch 412 4 = true := by decide +kernel
  have b416 : batch 416 4 = true := by decide +kernel
  have b420 : batch 420 4 = true := by decide +kernel
  have b424 : batch 424 4 = true := by decide +kernel
  have b428 : batch 428 4 = true := by decide +kernel
  have b432 : batch 432 4 = true := by decide +kernel
  have b436 : batch 436 4 = true := by decide +kernel
  have b440 : batch 440 4 = true := by decide +kernel
  have b444 : batch 444 4 = true := by decide +kernel
  have v448 : batch 448 1 = true := by decide +kernel
  have v449 : batch 449 1 = true := by decide +kernel
  have v450 : batch 450 1 = true := by decide +kernel
  have v451 : batch 451 1 = true := by decide +kernel
  have b448 : batch 448 4 = true := (joinBatch v448 (joinBatch v449 (joinBatch v450 v451)))
  have b452 : batch 452 4 = true := by decide +kernel
  have b456 : batch 456 4 = true := by decide +kernel
  have b460 : batch 460 4 = true := by decide +kernel
  have b464 : batch 464 4 = true := by decide +kernel
  have b468 : batch 468 4 = true := by decide +kernel
  have b472 : batch 472 4 = true := by decide +kernel
  have b476 : batch 476 4 = true := by decide +kernel
  exact (@stitch 384 4 b384 (@stitch 388 4 b388 (@stitch 392 4 b392 (@stitch 396 4 b396 (@stitch 400 4 b400 (@stitch 404 4 b404 (@stitch 408 4 b408 (@stitch 412 4 b412 (@stitch 416 4 b416 (@stitch 420 4 b420 (@stitch 424 4 b424 (@stitch 428 4 b428 (@stitch 432 4 b432 (@stitch 436 4 b436 (@stitch 440 4 b440 (@stitch 444 4 b444 (@stitch 448 4 b448 (@stitch 452 4 b452 (@stitch 456 4 b456 (@stitch 460 4 b460 (@stitch 464 4 b464 (@stitch 468 4 b468 (@stitch 472 4 b472 (@stitch 476 4 b476 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock480 (tail : remaining 576 = true) : remaining 480 = true := by
  have b480 : batch 480 4 = true := by decide +kernel
  have b484 : batch 484 4 = true := by decide +kernel
  have b488 : batch 488 4 = true := by decide +kernel
  have b492 : batch 492 4 = true := by decide +kernel
  have b496 : batch 496 4 = true := by decide +kernel
  have b500 : batch 500 4 = true := by decide +kernel
  have b504 : batch 504 4 = true := by decide +kernel
  have b508 : batch 508 4 = true := by decide +kernel
  have b512 : batch 512 4 = true := by decide +kernel
  have b516 : batch 516 4 = true := by decide +kernel
  have b520 : batch 520 4 = true := by decide +kernel
  have b524 : batch 524 4 = true := by decide +kernel
  have b528 : batch 528 4 = true := by decide +kernel
  have b532 : batch 532 4 = true := by decide +kernel
  have b536 : batch 536 4 = true := by decide +kernel
  have b540 : batch 540 4 = true := by decide +kernel
  have b544 : batch 544 4 = true := by decide +kernel
  have b548 : batch 548 4 = true := by decide +kernel
  have b552 : batch 552 4 = true := by decide +kernel
  have b556 : batch 556 4 = true := by decide +kernel
  have b560 : batch 560 4 = true := by decide +kernel
  have b564 : batch 564 4 = true := by decide +kernel
  have b568 : batch 568 4 = true := by decide +kernel
  have b572 : batch 572 4 = true := by decide +kernel
  exact (@stitch 480 4 b480 (@stitch 484 4 b484 (@stitch 488 4 b488 (@stitch 492 4 b492 (@stitch 496 4 b496 (@stitch 500 4 b500 (@stitch 504 4 b504 (@stitch 508 4 b508 (@stitch 512 4 b512 (@stitch 516 4 b516 (@stitch 520 4 b520 (@stitch 524 4 b524 (@stitch 528 4 b528 (@stitch 532 4 b532 (@stitch 536 4 b536 (@stitch 540 4 b540 (@stitch 544 4 b544 (@stitch 548 4 b548 (@stitch 552 4 b552 (@stitch 556 4 b556 (@stitch 560 4 b560 (@stitch 564 4 b564 (@stitch 568 4 b568 (@stitch 572 4 b572 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock576 (tail : remaining 672 = true) : remaining 576 = true := by
  have b576 : batch 576 4 = true := by decide +kernel
  have b580 : batch 580 4 = true := by decide +kernel
  have b584 : batch 584 4 = true := by decide +kernel
  have b588 : batch 588 4 = true := by decide +kernel
  have b592 : batch 592 4 = true := by decide +kernel
  have b596 : batch 596 4 = true := by decide +kernel
  have b600 : batch 600 4 = true := by decide +kernel
  have b604 : batch 604 4 = true := by decide +kernel
  have b608 : batch 608 4 = true := by decide +kernel
  have b612 : batch 612 4 = true := by decide +kernel
  have b616 : batch 616 4 = true := by decide +kernel
  have b620 : batch 620 4 = true := by decide +kernel
  have b624 : batch 624 4 = true := by decide +kernel
  have b628 : batch 628 4 = true := by decide +kernel
  have b632 : batch 632 4 = true := by decide +kernel
  have b636 : batch 636 4 = true := by decide +kernel
  have b640 : batch 640 4 = true := by decide +kernel
  have b644 : batch 644 4 = true := by decide +kernel
  have b648 : batch 648 4 = true := by decide +kernel
  have b652 : batch 652 4 = true := by decide +kernel
  have b656 : batch 656 4 = true := by decide +kernel
  have b660 : batch 660 4 = true := by decide +kernel
  have b664 : batch 664 4 = true := by decide +kernel
  have b668 : batch 668 4 = true := by decide +kernel
  exact (@stitch 576 4 b576 (@stitch 580 4 b580 (@stitch 584 4 b584 (@stitch 588 4 b588 (@stitch 592 4 b592 (@stitch 596 4 b596 (@stitch 600 4 b600 (@stitch 604 4 b604 (@stitch 608 4 b608 (@stitch 612 4 b612 (@stitch 616 4 b616 (@stitch 620 4 b620 (@stitch 624 4 b624 (@stitch 628 4 b628 (@stitch 632 4 b632 (@stitch 636 4 b636 (@stitch 640 4 b640 (@stitch 644 4 b644 (@stitch 648 4 b648 (@stitch 652 4 b652 (@stitch 656 4 b656 (@stitch 660 4 b660 (@stitch 664 4 b664 (@stitch 668 4 b668 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock672 (tail : remaining 768 = true) : remaining 672 = true := by
  have b672 : batch 672 4 = true := by decide +kernel
  have b676 : batch 676 4 = true := by decide +kernel
  have b680 : batch 680 4 = true := by decide +kernel
  have b684 : batch 684 4 = true := by decide +kernel
  have b688 : batch 688 4 = true := by decide +kernel
  have b692 : batch 692 4 = true := by decide +kernel
  have b696 : batch 696 4 = true := by decide +kernel
  have b700 : batch 700 4 = true := by decide +kernel
  have b704 : batch 704 4 = true := by decide +kernel
  have b708 : batch 708 4 = true := by decide +kernel
  have b712 : batch 712 4 = true := by decide +kernel
  have b716 : batch 716 4 = true := by decide +kernel
  have b720 : batch 720 4 = true := by decide +kernel
  have b724 : batch 724 4 = true := by decide +kernel
  have b728 : batch 728 4 = true := by decide +kernel
  have b732 : batch 732 4 = true := by decide +kernel
  have b736 : batch 736 4 = true := by decide +kernel
  have b740 : batch 740 4 = true := by decide +kernel
  have b744 : batch 744 4 = true := by decide +kernel
  have b748 : batch 748 4 = true := by decide +kernel
  have b752 : batch 752 4 = true := by decide +kernel
  have b756 : batch 756 4 = true := by decide +kernel
  have b760 : batch 760 4 = true := by decide +kernel
  have b764 : batch 764 4 = true := by decide +kernel
  exact (@stitch 672 4 b672 (@stitch 676 4 b676 (@stitch 680 4 b680 (@stitch 684 4 b684 (@stitch 688 4 b688 (@stitch 692 4 b692 (@stitch 696 4 b696 (@stitch 700 4 b700 (@stitch 704 4 b704 (@stitch 708 4 b708 (@stitch 712 4 b712 (@stitch 716 4 b716 (@stitch 720 4 b720 (@stitch 724 4 b724 (@stitch 728 4 b728 (@stitch 732 4 b732 (@stitch 736 4 b736 (@stitch 740 4 b740 (@stitch 744 4 b744 (@stitch 748 4 b748 (@stitch 752 4 b752 (@stitch 756 4 b756 (@stitch 760 4 b760 (@stitch 764 4 b764 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock768 (tail : remaining 864 = true) : remaining 768 = true := by
  have b768 : batch 768 4 = true := by decide +kernel
  have b772 : batch 772 4 = true := by decide +kernel
  have b776 : batch 776 4 = true := by decide +kernel
  have b780 : batch 780 4 = true := by decide +kernel
  have b784 : batch 784 4 = true := by decide +kernel
  have b788 : batch 788 4 = true := by decide +kernel
  have b792 : batch 792 4 = true := by decide +kernel
  have v796 : batch 796 1 = true := by decide +kernel
  have v797 : batch 797 1 = true := by decide +kernel
  have v798 : batch 798 1 = true := by decide +kernel
  have v799 : batch 799 1 = true := by decide +kernel
  have b796 : batch 796 4 = true := (joinBatch v796 (joinBatch v797 (joinBatch v798 v799)))
  have b800 : batch 800 4 = true := by decide +kernel
  have b804 : batch 804 4 = true := by decide +kernel
  have b808 : batch 808 4 = true := by decide +kernel
  have b812 : batch 812 4 = true := by decide +kernel
  have b816 : batch 816 4 = true := by decide +kernel
  have v820 : batch 820 1 = true := by decide +kernel
  have v821 : batch 821 1 = true := by decide +kernel
  have v822 : batch 822 1 = true := by decide +kernel
  have v823 : batch 823 1 = true := by decide +kernel
  have b820 : batch 820 4 = true := (joinBatch v820 (joinBatch v821 (joinBatch v822 v823)))
  have v824 : batch 824 1 = true := by decide +kernel
  have v825 : batch 825 1 = true := by decide +kernel
  have v826 : batch 826 1 = true := by decide +kernel
  have v827 : batch 827 1 = true := by decide +kernel
  have b824 : batch 824 4 = true := (joinBatch v824 (joinBatch v825 (joinBatch v826 v827)))
  have b828 : batch 828 4 = true := by decide +kernel
  have b832 : batch 832 4 = true := by decide +kernel
  have v836 : batch 836 1 = true := by decide +kernel
  have v837 : batch 837 1 = true := by decide +kernel
  have v838 : batch 838 1 = true := by decide +kernel
  have v839 : batch 839 1 = true := by decide +kernel
  have b836 : batch 836 4 = true := (joinBatch v836 (joinBatch v837 (joinBatch v838 v839)))
  have v840 : batch 840 1 = true := by decide +kernel
  have v841 : batch 841 1 = true := by decide +kernel
  have v842 : batch 842 1 = true := by decide +kernel
  have v843 : batch 843 1 = true := by decide +kernel
  have b840 : batch 840 4 = true := (joinBatch v840 (joinBatch v841 (joinBatch v842 v843)))
  have b844 : batch 844 4 = true := by decide +kernel
  have b848 : batch 848 4 = true := by decide +kernel
  have b852 : batch 852 4 = true := by decide +kernel
  have b856 : batch 856 4 = true := by decide +kernel
  have b860 : batch 860 4 = true := by decide +kernel
  exact (@stitch 768 4 b768 (@stitch 772 4 b772 (@stitch 776 4 b776 (@stitch 780 4 b780 (@stitch 784 4 b784 (@stitch 788 4 b788 (@stitch 792 4 b792 (@stitch 796 4 b796 (@stitch 800 4 b800 (@stitch 804 4 b804 (@stitch 808 4 b808 (@stitch 812 4 b812 (@stitch 816 4 b816 (@stitch 820 4 b820 (@stitch 824 4 b824 (@stitch 828 4 b828 (@stitch 832 4 b832 (@stitch 836 4 b836 (@stitch 840 4 b840 (@stitch 844 4 b844 (@stitch 848 4 b848 (@stitch 852 4 b852 (@stitch 856 4 b856 (@stitch 860 4 b860 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock864 (tail : remaining 960 = true) : remaining 864 = true := by
  have b864 : batch 864 4 = true := by decide +kernel
  have v868 : batch 868 1 = true := by decide +kernel
  have v869 : batch 869 1 = true := by decide +kernel
  have v870 : batch 870 1 = true := by decide +kernel
  have v871 : batch 871 1 = true := by decide +kernel
  have b868 : batch 868 4 = true := (joinBatch v868 (joinBatch v869 (joinBatch v870 v871)))
  have b872 : batch 872 4 = true := by decide +kernel
  have b876 : batch 876 4 = true := by decide +kernel
  have b880 : batch 880 4 = true := by decide +kernel
  have b884 : batch 884 4 = true := by decide +kernel
  have b888 : batch 888 4 = true := by decide +kernel
  have b892 : batch 892 4 = true := by decide +kernel
  have b896 : batch 896 4 = true := by decide +kernel
  have v900 : batch 900 1 = true := by decide +kernel
  have v901 : batch 901 1 = true := by decide +kernel
  have v902 : batch 902 1 = true := by decide +kernel
  have v903 : batch 903 1 = true := by decide +kernel
  have b900 : batch 900 4 = true := (joinBatch v900 (joinBatch v901 (joinBatch v902 v903)))
  have b904 : batch 904 4 = true := by decide +kernel
  have b908 : batch 908 4 = true := by decide +kernel
  have b912 : batch 912 4 = true := by decide +kernel
  have b916 : batch 916 4 = true := by decide +kernel
  have b920 : batch 920 4 = true := by decide +kernel
  have b924 : batch 924 4 = true := by decide +kernel
  have b928 : batch 928 4 = true := by decide +kernel
  have b932 : batch 932 4 = true := by decide +kernel
  have b936 : batch 936 4 = true := by decide +kernel
  have b940 : batch 940 4 = true := by decide +kernel
  have b944 : batch 944 4 = true := by decide +kernel
  have b948 : batch 948 4 = true := by decide +kernel
  have b952 : batch 952 4 = true := by decide +kernel
  have b956 : batch 956 4 = true := by decide +kernel
  exact (@stitch 864 4 b864 (@stitch 868 4 b868 (@stitch 872 4 b872 (@stitch 876 4 b876 (@stitch 880 4 b880 (@stitch 884 4 b884 (@stitch 888 4 b888 (@stitch 892 4 b892 (@stitch 896 4 b896 (@stitch 900 4 b900 (@stitch 904 4 b904 (@stitch 908 4 b908 (@stitch 912 4 b912 (@stitch 916 4 b916 (@stitch 920 4 b920 (@stitch 924 4 b924 (@stitch 928 4 b928 (@stitch 932 4 b932 (@stitch 936 4 b936 (@stitch 940 4 b940 (@stitch 944 4 b944 (@stitch 948 4 b948 (@stitch 952 4 b952 (@stitch 956 4 b956 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock960 (tail : remaining 1056 = true) : remaining 960 = true := by
  have b960 : batch 960 4 = true := by decide +kernel
  have b964 : batch 964 4 = true := by decide +kernel
  have b968 : batch 968 4 = true := by decide +kernel
  have b972 : batch 972 4 = true := by decide +kernel
  have b976 : batch 976 4 = true := by decide +kernel
  have b980 : batch 980 4 = true := by decide +kernel
  have b984 : batch 984 4 = true := by decide +kernel
  have b988 : batch 988 4 = true := by decide +kernel
  have b992 : batch 992 4 = true := by decide +kernel
  have b996 : batch 996 4 = true := by decide +kernel
  have b1000 : batch 1000 4 = true := by decide +kernel
  have b1004 : batch 1004 4 = true := by decide +kernel
  have b1008 : batch 1008 4 = true := by decide +kernel
  have b1012 : batch 1012 4 = true := by decide +kernel
  have b1016 : batch 1016 4 = true := by decide +kernel
  have b1020 : batch 1020 4 = true := by decide +kernel
  have b1024 : batch 1024 4 = true := by decide +kernel
  have b1028 : batch 1028 4 = true := by decide +kernel
  have b1032 : batch 1032 4 = true := by decide +kernel
  have b1036 : batch 1036 4 = true := by decide +kernel
  have b1040 : batch 1040 4 = true := by decide +kernel
  have b1044 : batch 1044 4 = true := by decide +kernel
  have b1048 : batch 1048 4 = true := by decide +kernel
  have b1052 : batch 1052 4 = true := by decide +kernel
  exact (@stitch 960 4 b960 (@stitch 964 4 b964 (@stitch 968 4 b968 (@stitch 972 4 b972 (@stitch 976 4 b976 (@stitch 980 4 b980 (@stitch 984 4 b984 (@stitch 988 4 b988 (@stitch 992 4 b992 (@stitch 996 4 b996 (@stitch 1000 4 b1000 (@stitch 1004 4 b1004 (@stitch 1008 4 b1008 (@stitch 1012 4 b1012 (@stitch 1016 4 b1016 (@stitch 1020 4 b1020 (@stitch 1024 4 b1024 (@stitch 1028 4 b1028 (@stitch 1032 4 b1032 (@stitch 1036 4 b1036 (@stitch 1040 4 b1040 (@stitch 1044 4 b1044 (@stitch 1048 4 b1048 (@stitch 1052 4 b1052 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1056 (tail : remaining 1152 = true) : remaining 1056 = true := by
  have b1056 : batch 1056 4 = true := by decide +kernel
  have b1060 : batch 1060 4 = true := by decide +kernel
  have b1064 : batch 1064 4 = true := by decide +kernel
  have b1068 : batch 1068 4 = true := by decide +kernel
  have b1072 : batch 1072 4 = true := by decide +kernel
  have b1076 : batch 1076 4 = true := by decide +kernel
  have b1080 : batch 1080 4 = true := by decide +kernel
  have b1084 : batch 1084 4 = true := by decide +kernel
  have b1088 : batch 1088 4 = true := by decide +kernel
  have b1092 : batch 1092 4 = true := by decide +kernel
  have b1096 : batch 1096 4 = true := by decide +kernel
  have b1100 : batch 1100 4 = true := by decide +kernel
  have b1104 : batch 1104 4 = true := by decide +kernel
  have b1108 : batch 1108 4 = true := by decide +kernel
  have b1112 : batch 1112 4 = true := by decide +kernel
  have b1116 : batch 1116 4 = true := by decide +kernel
  have b1120 : batch 1120 4 = true := by decide +kernel
  have b1124 : batch 1124 4 = true := by decide +kernel
  have b1128 : batch 1128 4 = true := by decide +kernel
  have b1132 : batch 1132 4 = true := by decide +kernel
  have b1136 : batch 1136 4 = true := by decide +kernel
  have b1140 : batch 1140 4 = true := by decide +kernel
  have b1144 : batch 1144 4 = true := by decide +kernel
  have b1148 : batch 1148 4 = true := by decide +kernel
  exact (@stitch 1056 4 b1056 (@stitch 1060 4 b1060 (@stitch 1064 4 b1064 (@stitch 1068 4 b1068 (@stitch 1072 4 b1072 (@stitch 1076 4 b1076 (@stitch 1080 4 b1080 (@stitch 1084 4 b1084 (@stitch 1088 4 b1088 (@stitch 1092 4 b1092 (@stitch 1096 4 b1096 (@stitch 1100 4 b1100 (@stitch 1104 4 b1104 (@stitch 1108 4 b1108 (@stitch 1112 4 b1112 (@stitch 1116 4 b1116 (@stitch 1120 4 b1120 (@stitch 1124 4 b1124 (@stitch 1128 4 b1128 (@stitch 1132 4 b1132 (@stitch 1136 4 b1136 (@stitch 1140 4 b1140 (@stitch 1144 4 b1144 (@stitch 1148 4 b1148 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1152 (tail : remaining 1248 = true) : remaining 1152 = true := by
  have b1152 : batch 1152 4 = true := by decide +kernel
  have b1156 : batch 1156 4 = true := by decide +kernel
  have b1160 : batch 1160 4 = true := by decide +kernel
  have b1164 : batch 1164 4 = true := by decide +kernel
  have b1168 : batch 1168 4 = true := by decide +kernel
  have b1172 : batch 1172 4 = true := by decide +kernel
  have b1176 : batch 1176 4 = true := by decide +kernel
  have b1180 : batch 1180 4 = true := by decide +kernel
  have b1184 : batch 1184 4 = true := by decide +kernel
  have b1188 : batch 1188 4 = true := by decide +kernel
  have b1192 : batch 1192 4 = true := by decide +kernel
  have b1196 : batch 1196 4 = true := by decide +kernel
  have b1200 : batch 1200 4 = true := by decide +kernel
  have b1204 : batch 1204 4 = true := by decide +kernel
  have b1208 : batch 1208 4 = true := by decide +kernel
  have b1212 : batch 1212 4 = true := by decide +kernel
  have b1216 : batch 1216 4 = true := by decide +kernel
  have b1220 : batch 1220 4 = true := by decide +kernel
  have b1224 : batch 1224 4 = true := by decide +kernel
  have b1228 : batch 1228 4 = true := by decide +kernel
  have b1232 : batch 1232 4 = true := by decide +kernel
  have b1236 : batch 1236 4 = true := by decide +kernel
  have b1240 : batch 1240 4 = true := by decide +kernel
  have b1244 : batch 1244 4 = true := by decide +kernel
  exact (@stitch 1152 4 b1152 (@stitch 1156 4 b1156 (@stitch 1160 4 b1160 (@stitch 1164 4 b1164 (@stitch 1168 4 b1168 (@stitch 1172 4 b1172 (@stitch 1176 4 b1176 (@stitch 1180 4 b1180 (@stitch 1184 4 b1184 (@stitch 1188 4 b1188 (@stitch 1192 4 b1192 (@stitch 1196 4 b1196 (@stitch 1200 4 b1200 (@stitch 1204 4 b1204 (@stitch 1208 4 b1208 (@stitch 1212 4 b1212 (@stitch 1216 4 b1216 (@stitch 1220 4 b1220 (@stitch 1224 4 b1224 (@stitch 1228 4 b1228 (@stitch 1232 4 b1232 (@stitch 1236 4 b1236 (@stitch 1240 4 b1240 (@stitch 1244 4 b1244 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1248 (tail : remaining 1344 = true) : remaining 1248 = true := by
  have b1248 : batch 1248 4 = true := by decide +kernel
  have b1252 : batch 1252 4 = true := by decide +kernel
  have b1256 : batch 1256 4 = true := by decide +kernel
  have b1260 : batch 1260 4 = true := by decide +kernel
  have b1264 : batch 1264 4 = true := by decide +kernel
  have b1268 : batch 1268 4 = true := by decide +kernel
  have b1272 : batch 1272 4 = true := by decide +kernel
  have b1276 : batch 1276 4 = true := by decide +kernel
  have b1280 : batch 1280 4 = true := by decide +kernel
  have b1284 : batch 1284 4 = true := by decide +kernel
  have b1288 : batch 1288 4 = true := by decide +kernel
  have b1292 : batch 1292 4 = true := by decide +kernel
  have b1296 : batch 1296 4 = true := by decide +kernel
  have b1300 : batch 1300 4 = true := by decide +kernel
  have b1304 : batch 1304 4 = true := by decide +kernel
  have b1308 : batch 1308 4 = true := by decide +kernel
  have b1312 : batch 1312 4 = true := by decide +kernel
  have b1316 : batch 1316 4 = true := by decide +kernel
  have b1320 : batch 1320 4 = true := by decide +kernel
  have b1324 : batch 1324 4 = true := by decide +kernel
  have b1328 : batch 1328 4 = true := by decide +kernel
  have b1332 : batch 1332 4 = true := by decide +kernel
  have b1336 : batch 1336 4 = true := by decide +kernel
  have b1340 : batch 1340 4 = true := by decide +kernel
  exact (@stitch 1248 4 b1248 (@stitch 1252 4 b1252 (@stitch 1256 4 b1256 (@stitch 1260 4 b1260 (@stitch 1264 4 b1264 (@stitch 1268 4 b1268 (@stitch 1272 4 b1272 (@stitch 1276 4 b1276 (@stitch 1280 4 b1280 (@stitch 1284 4 b1284 (@stitch 1288 4 b1288 (@stitch 1292 4 b1292 (@stitch 1296 4 b1296 (@stitch 1300 4 b1300 (@stitch 1304 4 b1304 (@stitch 1308 4 b1308 (@stitch 1312 4 b1312 (@stitch 1316 4 b1316 (@stitch 1320 4 b1320 (@stitch 1324 4 b1324 (@stitch 1328 4 b1328 (@stitch 1332 4 b1332 (@stitch 1336 4 b1336 (@stitch 1340 4 b1340 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1344 (tail : remaining 1440 = true) : remaining 1344 = true := by
  have b1344 : batch 1344 4 = true := by decide +kernel
  have b1348 : batch 1348 4 = true := by decide +kernel
  have b1352 : batch 1352 4 = true := by decide +kernel
  have b1356 : batch 1356 4 = true := by decide +kernel
  have b1360 : batch 1360 4 = true := by decide +kernel
  have b1364 : batch 1364 4 = true := by decide +kernel
  have b1368 : batch 1368 4 = true := by decide +kernel
  have b1372 : batch 1372 4 = true := by decide +kernel
  have b1376 : batch 1376 4 = true := by decide +kernel
  have b1380 : batch 1380 4 = true := by decide +kernel
  have b1384 : batch 1384 4 = true := by decide +kernel
  have b1388 : batch 1388 4 = true := by decide +kernel
  have b1392 : batch 1392 4 = true := by decide +kernel
  have b1396 : batch 1396 4 = true := by decide +kernel
  have b1400 : batch 1400 4 = true := by decide +kernel
  have b1404 : batch 1404 4 = true := by decide +kernel
  have b1408 : batch 1408 4 = true := by decide +kernel
  have b1412 : batch 1412 4 = true := by decide +kernel
  have b1416 : batch 1416 4 = true := by decide +kernel
  have b1420 : batch 1420 4 = true := by decide +kernel
  have b1424 : batch 1424 4 = true := by decide +kernel
  have b1428 : batch 1428 4 = true := by decide +kernel
  have b1432 : batch 1432 4 = true := by decide +kernel
  have b1436 : batch 1436 4 = true := by decide +kernel
  exact (@stitch 1344 4 b1344 (@stitch 1348 4 b1348 (@stitch 1352 4 b1352 (@stitch 1356 4 b1356 (@stitch 1360 4 b1360 (@stitch 1364 4 b1364 (@stitch 1368 4 b1368 (@stitch 1372 4 b1372 (@stitch 1376 4 b1376 (@stitch 1380 4 b1380 (@stitch 1384 4 b1384 (@stitch 1388 4 b1388 (@stitch 1392 4 b1392 (@stitch 1396 4 b1396 (@stitch 1400 4 b1400 (@stitch 1404 4 b1404 (@stitch 1408 4 b1408 (@stitch 1412 4 b1412 (@stitch 1416 4 b1416 (@stitch 1420 4 b1420 (@stitch 1424 4 b1424 (@stitch 1428 4 b1428 (@stitch 1432 4 b1432 (@stitch 1436 4 b1436 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1440 (tail : remaining 1536 = true) : remaining 1440 = true := by
  have b1440 : batch 1440 4 = true := by decide +kernel
  have b1444 : batch 1444 4 = true := by decide +kernel
  have b1448 : batch 1448 4 = true := by decide +kernel
  have v1452 : batch 1452 1 = true := by decide +kernel
  have v1453 : batch 1453 1 = true := by decide +kernel
  have v1454 : batch 1454 1 = true := by decide +kernel
  have v1455 : batch 1455 1 = true := by decide +kernel
  have b1452 : batch 1452 4 = true := (joinBatch v1452 (joinBatch v1453 (joinBatch v1454 v1455)))
  have b1456 : batch 1456 4 = true := by decide +kernel
  have b1460 : batch 1460 4 = true := by decide +kernel
  have b1464 : batch 1464 4 = true := by decide +kernel
  have b1468 : batch 1468 4 = true := by decide +kernel
  have b1472 : batch 1472 4 = true := by decide +kernel
  have b1476 : batch 1476 4 = true := by decide +kernel
  have b1480 : batch 1480 4 = true := by decide +kernel
  have b1484 : batch 1484 4 = true := by decide +kernel
  have b1488 : batch 1488 4 = true := by decide +kernel
  have b1492 : batch 1492 4 = true := by decide +kernel
  have b1496 : batch 1496 4 = true := by decide +kernel
  have b1500 : batch 1500 4 = true := by decide +kernel
  have b1504 : batch 1504 4 = true := by decide +kernel
  have b1508 : batch 1508 4 = true := by decide +kernel
  have b1512 : batch 1512 4 = true := by decide +kernel
  have b1516 : batch 1516 4 = true := by decide +kernel
  have v1520 : batch 1520 1 = true := by decide +kernel
  have v1521 : batch 1521 1 = true := by decide +kernel
  have v1522 : batch 1522 1 = true := by decide +kernel
  have v1523 : batch 1523 1 = true := by decide +kernel
  have b1520 : batch 1520 4 = true := (joinBatch v1520 (joinBatch v1521 (joinBatch v1522 v1523)))
  have b1524 : batch 1524 4 = true := by decide +kernel
  have b1528 : batch 1528 4 = true := by decide +kernel
  have b1532 : batch 1532 4 = true := by decide +kernel
  exact (@stitch 1440 4 b1440 (@stitch 1444 4 b1444 (@stitch 1448 4 b1448 (@stitch 1452 4 b1452 (@stitch 1456 4 b1456 (@stitch 1460 4 b1460 (@stitch 1464 4 b1464 (@stitch 1468 4 b1468 (@stitch 1472 4 b1472 (@stitch 1476 4 b1476 (@stitch 1480 4 b1480 (@stitch 1484 4 b1484 (@stitch 1488 4 b1488 (@stitch 1492 4 b1492 (@stitch 1496 4 b1496 (@stitch 1500 4 b1500 (@stitch 1504 4 b1504 (@stitch 1508 4 b1508 (@stitch 1512 4 b1512 (@stitch 1516 4 b1516 (@stitch 1520 4 b1520 (@stitch 1524 4 b1524 (@stitch 1528 4 b1528 (@stitch 1532 4 b1532 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1536 (tail : remaining 1632 = true) : remaining 1536 = true := by
  have b1536 : batch 1536 4 = true := by decide +kernel
  have b1540 : batch 1540 4 = true := by decide +kernel
  have b1544 : batch 1544 4 = true := by decide +kernel
  have b1548 : batch 1548 4 = true := by decide +kernel
  have b1552 : batch 1552 4 = true := by decide +kernel
  have b1556 : batch 1556 4 = true := by decide +kernel
  have b1560 : batch 1560 4 = true := by decide +kernel
  have b1564 : batch 1564 4 = true := by decide +kernel
  have b1568 : batch 1568 4 = true := by decide +kernel
  have b1572 : batch 1572 4 = true := by decide +kernel
  have b1576 : batch 1576 4 = true := by decide +kernel
  have b1580 : batch 1580 4 = true := by decide +kernel
  have b1584 : batch 1584 4 = true := by decide +kernel
  have b1588 : batch 1588 4 = true := by decide +kernel
  have b1592 : batch 1592 4 = true := by decide +kernel
  have b1596 : batch 1596 4 = true := by decide +kernel
  have b1600 : batch 1600 4 = true := by decide +kernel
  have b1604 : batch 1604 4 = true := by decide +kernel
  have b1608 : batch 1608 4 = true := by decide +kernel
  have b1612 : batch 1612 4 = true := by decide +kernel
  have b1616 : batch 1616 4 = true := by decide +kernel
  have b1620 : batch 1620 4 = true := by decide +kernel
  have b1624 : batch 1624 4 = true := by decide +kernel
  have b1628 : batch 1628 4 = true := by decide +kernel
  exact (@stitch 1536 4 b1536 (@stitch 1540 4 b1540 (@stitch 1544 4 b1544 (@stitch 1548 4 b1548 (@stitch 1552 4 b1552 (@stitch 1556 4 b1556 (@stitch 1560 4 b1560 (@stitch 1564 4 b1564 (@stitch 1568 4 b1568 (@stitch 1572 4 b1572 (@stitch 1576 4 b1576 (@stitch 1580 4 b1580 (@stitch 1584 4 b1584 (@stitch 1588 4 b1588 (@stitch 1592 4 b1592 (@stitch 1596 4 b1596 (@stitch 1600 4 b1600 (@stitch 1604 4 b1604 (@stitch 1608 4 b1608 (@stitch 1612 4 b1612 (@stitch 1616 4 b1616 (@stitch 1620 4 b1620 (@stitch 1624 4 b1624 (@stitch 1628 4 b1628 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1632 (tail : remaining 1728 = true) : remaining 1632 = true := by
  have b1632 : batch 1632 4 = true := by decide +kernel
  have b1636 : batch 1636 4 = true := by decide +kernel
  have b1640 : batch 1640 4 = true := by decide +kernel
  have b1644 : batch 1644 4 = true := by decide +kernel
  have b1648 : batch 1648 4 = true := by decide +kernel
  have b1652 : batch 1652 4 = true := by decide +kernel
  have b1656 : batch 1656 4 = true := by decide +kernel
  have b1660 : batch 1660 4 = true := by decide +kernel
  have b1664 : batch 1664 4 = true := by decide +kernel
  have b1668 : batch 1668 4 = true := by decide +kernel
  have b1672 : batch 1672 4 = true := by decide +kernel
  have b1676 : batch 1676 4 = true := by decide +kernel
  have b1680 : batch 1680 4 = true := by decide +kernel
  have b1684 : batch 1684 4 = true := by decide +kernel
  have b1688 : batch 1688 4 = true := by decide +kernel
  have b1692 : batch 1692 4 = true := by decide +kernel
  have b1696 : batch 1696 4 = true := by decide +kernel
  have b1700 : batch 1700 4 = true := by decide +kernel
  have b1704 : batch 1704 4 = true := by decide +kernel
  have b1708 : batch 1708 4 = true := by decide +kernel
  have b1712 : batch 1712 4 = true := by decide +kernel
  have b1716 : batch 1716 4 = true := by decide +kernel
  have b1720 : batch 1720 4 = true := by decide +kernel
  have b1724 : batch 1724 4 = true := by decide +kernel
  exact (@stitch 1632 4 b1632 (@stitch 1636 4 b1636 (@stitch 1640 4 b1640 (@stitch 1644 4 b1644 (@stitch 1648 4 b1648 (@stitch 1652 4 b1652 (@stitch 1656 4 b1656 (@stitch 1660 4 b1660 (@stitch 1664 4 b1664 (@stitch 1668 4 b1668 (@stitch 1672 4 b1672 (@stitch 1676 4 b1676 (@stitch 1680 4 b1680 (@stitch 1684 4 b1684 (@stitch 1688 4 b1688 (@stitch 1692 4 b1692 (@stitch 1696 4 b1696 (@stitch 1700 4 b1700 (@stitch 1704 4 b1704 (@stitch 1708 4 b1708 (@stitch 1712 4 b1712 (@stitch 1716 4 b1716 (@stitch 1720 4 b1720 (@stitch 1724 4 b1724 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1728 (tail : remaining 1824 = true) : remaining 1728 = true := by
  have b1728 : batch 1728 4 = true := by decide +kernel
  have b1732 : batch 1732 4 = true := by decide +kernel
  have b1736 : batch 1736 4 = true := by decide +kernel
  have b1740 : batch 1740 4 = true := by decide +kernel
  have b1744 : batch 1744 4 = true := by decide +kernel
  have b1748 : batch 1748 4 = true := by decide +kernel
  have b1752 : batch 1752 4 = true := by decide +kernel
  have b1756 : batch 1756 4 = true := by decide +kernel
  have b1760 : batch 1760 4 = true := by decide +kernel
  have b1764 : batch 1764 4 = true := by decide +kernel
  have b1768 : batch 1768 4 = true := by decide +kernel
  have b1772 : batch 1772 4 = true := by decide +kernel
  have b1776 : batch 1776 4 = true := by decide +kernel
  have b1780 : batch 1780 4 = true := by decide +kernel
  have b1784 : batch 1784 4 = true := by decide +kernel
  have b1788 : batch 1788 4 = true := by decide +kernel
  have b1792 : batch 1792 4 = true := by decide +kernel
  have b1796 : batch 1796 4 = true := by decide +kernel
  have b1800 : batch 1800 4 = true := by decide +kernel
  have b1804 : batch 1804 4 = true := by decide +kernel
  have b1808 : batch 1808 4 = true := by decide +kernel
  have b1812 : batch 1812 4 = true := by decide +kernel
  have b1816 : batch 1816 4 = true := by decide +kernel
  have b1820 : batch 1820 4 = true := by decide +kernel
  exact (@stitch 1728 4 b1728 (@stitch 1732 4 b1732 (@stitch 1736 4 b1736 (@stitch 1740 4 b1740 (@stitch 1744 4 b1744 (@stitch 1748 4 b1748 (@stitch 1752 4 b1752 (@stitch 1756 4 b1756 (@stitch 1760 4 b1760 (@stitch 1764 4 b1764 (@stitch 1768 4 b1768 (@stitch 1772 4 b1772 (@stitch 1776 4 b1776 (@stitch 1780 4 b1780 (@stitch 1784 4 b1784 (@stitch 1788 4 b1788 (@stitch 1792 4 b1792 (@stitch 1796 4 b1796 (@stitch 1800 4 b1800 (@stitch 1804 4 b1804 (@stitch 1808 4 b1808 (@stitch 1812 4 b1812 (@stitch 1816 4 b1816 (@stitch 1820 4 b1820 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1824 (tail : remaining 1920 = true) : remaining 1824 = true := by
  have b1824 : batch 1824 4 = true := by decide +kernel
  have b1828 : batch 1828 4 = true := by decide +kernel
  have b1832 : batch 1832 4 = true := by decide +kernel
  have b1836 : batch 1836 4 = true := by decide +kernel
  have b1840 : batch 1840 4 = true := by decide +kernel
  have b1844 : batch 1844 4 = true := by decide +kernel
  have b1848 : batch 1848 4 = true := by decide +kernel
  have b1852 : batch 1852 4 = true := by decide +kernel
  have b1856 : batch 1856 4 = true := by decide +kernel
  have b1860 : batch 1860 4 = true := by decide +kernel
  have b1864 : batch 1864 4 = true := by decide +kernel
  have b1868 : batch 1868 4 = true := by decide +kernel
  have b1872 : batch 1872 4 = true := by decide +kernel
  have b1876 : batch 1876 4 = true := by decide +kernel
  have b1880 : batch 1880 4 = true := by decide +kernel
  have b1884 : batch 1884 4 = true := by decide +kernel
  have b1888 : batch 1888 4 = true := by decide +kernel
  have b1892 : batch 1892 4 = true := by decide +kernel
  have b1896 : batch 1896 4 = true := by decide +kernel
  have b1900 : batch 1900 4 = true := by decide +kernel
  have b1904 : batch 1904 4 = true := by decide +kernel
  have b1908 : batch 1908 4 = true := by decide +kernel
  have b1912 : batch 1912 4 = true := by decide +kernel
  have b1916 : batch 1916 4 = true := by decide +kernel
  exact (@stitch 1824 4 b1824 (@stitch 1828 4 b1828 (@stitch 1832 4 b1832 (@stitch 1836 4 b1836 (@stitch 1840 4 b1840 (@stitch 1844 4 b1844 (@stitch 1848 4 b1848 (@stitch 1852 4 b1852 (@stitch 1856 4 b1856 (@stitch 1860 4 b1860 (@stitch 1864 4 b1864 (@stitch 1868 4 b1868 (@stitch 1872 4 b1872 (@stitch 1876 4 b1876 (@stitch 1880 4 b1880 (@stitch 1884 4 b1884 (@stitch 1888 4 b1888 (@stitch 1892 4 b1892 (@stitch 1896 4 b1896 (@stitch 1900 4 b1900 (@stitch 1904 4 b1904 (@stitch 1908 4 b1908 (@stitch 1912 4 b1912 (@stitch 1916 4 b1916 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock1920 (tail : remaining 2016 = true) : remaining 1920 = true := by
  have b1920 : batch 1920 4 = true := by decide +kernel
  have b1924 : batch 1924 4 = true := by decide +kernel
  have b1928 : batch 1928 4 = true := by decide +kernel
  have b1932 : batch 1932 4 = true := by decide +kernel
  have b1936 : batch 1936 4 = true := by decide +kernel
  have b1940 : batch 1940 4 = true := by decide +kernel
  have b1944 : batch 1944 4 = true := by decide +kernel
  have b1948 : batch 1948 4 = true := by decide +kernel
  have b1952 : batch 1952 4 = true := by decide +kernel
  have b1956 : batch 1956 4 = true := by decide +kernel
  have b1960 : batch 1960 4 = true := by decide +kernel
  have b1964 : batch 1964 4 = true := by decide +kernel
  have b1968 : batch 1968 4 = true := by decide +kernel
  have b1972 : batch 1972 4 = true := by decide +kernel
  have b1976 : batch 1976 4 = true := by decide +kernel
  have b1980 : batch 1980 4 = true := by decide +kernel
  have b1984 : batch 1984 4 = true := by decide +kernel
  have b1988 : batch 1988 4 = true := by decide +kernel
  have b1992 : batch 1992 4 = true := by decide +kernel
  have b1996 : batch 1996 4 = true := by decide +kernel
  have b2000 : batch 2000 4 = true := by decide +kernel
  have b2004 : batch 2004 4 = true := by decide +kernel
  have b2008 : batch 2008 4 = true := by decide +kernel
  have b2012 : batch 2012 4 = true := by decide +kernel
  exact (@stitch 1920 4 b1920 (@stitch 1924 4 b1924 (@stitch 1928 4 b1928 (@stitch 1932 4 b1932 (@stitch 1936 4 b1936 (@stitch 1940 4 b1940 (@stitch 1944 4 b1944 (@stitch 1948 4 b1948 (@stitch 1952 4 b1952 (@stitch 1956 4 b1956 (@stitch 1960 4 b1960 (@stitch 1964 4 b1964 (@stitch 1968 4 b1968 (@stitch 1972 4 b1972 (@stitch 1976 4 b1976 (@stitch 1980 4 b1980 (@stitch 1984 4 b1984 (@stitch 1988 4 b1988 (@stitch 1992 4 b1992 (@stitch 1996 4 b1996 (@stitch 2000 4 b2000 (@stitch 2004 4 b2004 (@stitch 2008 4 b2008 (@stitch 2012 4 b2012 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2016 (tail : remaining 2112 = true) : remaining 2016 = true := by
  have b2016 : batch 2016 4 = true := by decide +kernel
  have b2020 : batch 2020 4 = true := by decide +kernel
  have b2024 : batch 2024 4 = true := by decide +kernel
  have b2028 : batch 2028 4 = true := by decide +kernel
  have b2032 : batch 2032 4 = true := by decide +kernel
  have b2036 : batch 2036 4 = true := by decide +kernel
  have b2040 : batch 2040 4 = true := by decide +kernel
  have b2044 : batch 2044 4 = true := by decide +kernel
  have b2048 : batch 2048 4 = true := by decide +kernel
  have b2052 : batch 2052 4 = true := by decide +kernel
  have b2056 : batch 2056 4 = true := by decide +kernel
  have b2060 : batch 2060 4 = true := by decide +kernel
  have b2064 : batch 2064 4 = true := by decide +kernel
  have b2068 : batch 2068 4 = true := by decide +kernel
  have b2072 : batch 2072 4 = true := by decide +kernel
  have b2076 : batch 2076 4 = true := by decide +kernel
  have b2080 : batch 2080 4 = true := by decide +kernel
  have b2084 : batch 2084 4 = true := by decide +kernel
  have b2088 : batch 2088 4 = true := by decide +kernel
  have b2092 : batch 2092 4 = true := by decide +kernel
  have b2096 : batch 2096 4 = true := by decide +kernel
  have b2100 : batch 2100 4 = true := by decide +kernel
  have b2104 : batch 2104 4 = true := by decide +kernel
  have b2108 : batch 2108 4 = true := by decide +kernel
  exact (@stitch 2016 4 b2016 (@stitch 2020 4 b2020 (@stitch 2024 4 b2024 (@stitch 2028 4 b2028 (@stitch 2032 4 b2032 (@stitch 2036 4 b2036 (@stitch 2040 4 b2040 (@stitch 2044 4 b2044 (@stitch 2048 4 b2048 (@stitch 2052 4 b2052 (@stitch 2056 4 b2056 (@stitch 2060 4 b2060 (@stitch 2064 4 b2064 (@stitch 2068 4 b2068 (@stitch 2072 4 b2072 (@stitch 2076 4 b2076 (@stitch 2080 4 b2080 (@stitch 2084 4 b2084 (@stitch 2088 4 b2088 (@stitch 2092 4 b2092 (@stitch 2096 4 b2096 (@stitch 2100 4 b2100 (@stitch 2104 4 b2104 (@stitch 2108 4 b2108 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2112 (tail : remaining 2208 = true) : remaining 2112 = true := by
  have b2112 : batch 2112 4 = true := by decide +kernel
  have b2116 : batch 2116 4 = true := by decide +kernel
  have b2120 : batch 2120 4 = true := by decide +kernel
  have b2124 : batch 2124 4 = true := by decide +kernel
  have b2128 : batch 2128 4 = true := by decide +kernel
  have b2132 : batch 2132 4 = true := by decide +kernel
  have b2136 : batch 2136 4 = true := by decide +kernel
  have b2140 : batch 2140 4 = true := by decide +kernel
  have v2144 : batch 2144 1 = true := by decide +kernel
  have v2145 : batch 2145 1 = true := by decide +kernel
  have v2146 : batch 2146 1 = true := by decide +kernel
  have v2147 : batch 2147 1 = true := by decide +kernel
  have b2144 : batch 2144 4 = true := (joinBatch v2144 (joinBatch v2145 (joinBatch v2146 v2147)))
  have b2148 : batch 2148 4 = true := by decide +kernel
  have b2152 : batch 2152 4 = true := by decide +kernel
  have v2156 : batch 2156 1 = true := by decide +kernel
  have v2157 : batch 2157 1 = true := by decide +kernel
  have v2158 : batch 2158 1 = true := by decide +kernel
  have v2159 : batch 2159 1 = true := by decide +kernel
  have b2156 : batch 2156 4 = true := (joinBatch v2156 (joinBatch v2157 (joinBatch v2158 v2159)))
  have v2160 : batch 2160 1 = true := by decide +kernel
  have v2161 : batch 2161 1 = true := by decide +kernel
  have v2162 : batch 2162 1 = true := by decide +kernel
  have v2163 : batch 2163 1 = true := by decide +kernel
  have b2160 : batch 2160 4 = true := (joinBatch v2160 (joinBatch v2161 (joinBatch v2162 v2163)))
  have b2164 : batch 2164 4 = true := by decide +kernel
  have b2168 : batch 2168 4 = true := by decide +kernel
  have v2172 : batch 2172 1 = true := by decide +kernel
  have v2173 : batch 2173 1 = true := by decide +kernel
  have v2174 : batch 2174 1 = true := by decide +kernel
  have v2175 : batch 2175 1 = true := by decide +kernel
  have b2172 : batch 2172 4 = true := (joinBatch v2172 (joinBatch v2173 (joinBatch v2174 v2175)))
  have b2176 : batch 2176 4 = true := by decide +kernel
  have b2180 : batch 2180 4 = true := by decide +kernel
  have b2184 : batch 2184 4 = true := by decide +kernel
  have b2188 : batch 2188 4 = true := by decide +kernel
  have b2192 : batch 2192 4 = true := by decide +kernel
  have b2196 : batch 2196 4 = true := by decide +kernel
  have b2200 : batch 2200 4 = true := by decide +kernel
  have b2204 : batch 2204 4 = true := by decide +kernel
  exact (@stitch 2112 4 b2112 (@stitch 2116 4 b2116 (@stitch 2120 4 b2120 (@stitch 2124 4 b2124 (@stitch 2128 4 b2128 (@stitch 2132 4 b2132 (@stitch 2136 4 b2136 (@stitch 2140 4 b2140 (@stitch 2144 4 b2144 (@stitch 2148 4 b2148 (@stitch 2152 4 b2152 (@stitch 2156 4 b2156 (@stitch 2160 4 b2160 (@stitch 2164 4 b2164 (@stitch 2168 4 b2168 (@stitch 2172 4 b2172 (@stitch 2176 4 b2176 (@stitch 2180 4 b2180 (@stitch 2184 4 b2184 (@stitch 2188 4 b2188 (@stitch 2192 4 b2192 (@stitch 2196 4 b2196 (@stitch 2200 4 b2200 (@stitch 2204 4 b2204 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2208 (tail : remaining 2304 = true) : remaining 2208 = true := by
  have v2208 : batch 2208 1 = true := by decide +kernel
  have v2209 : batch 2209 1 = true := by decide +kernel
  have v2210 : batch 2210 1 = true := by decide +kernel
  have v2211 : batch 2211 1 = true := by decide +kernel
  have b2208 : batch 2208 4 = true := (joinBatch v2208 (joinBatch v2209 (joinBatch v2210 v2211)))
  have b2212 : batch 2212 4 = true := by decide +kernel
  have b2216 : batch 2216 4 = true := by decide +kernel
  have b2220 : batch 2220 4 = true := by decide +kernel
  have b2224 : batch 2224 4 = true := by decide +kernel
  have b2228 : batch 2228 4 = true := by decide +kernel
  have b2232 : batch 2232 4 = true := by decide +kernel
  have b2236 : batch 2236 4 = true := by decide +kernel
  have b2240 : batch 2240 4 = true := by decide +kernel
  have b2244 : batch 2244 4 = true := by decide +kernel
  have b2248 : batch 2248 4 = true := by decide +kernel
  have b2252 : batch 2252 4 = true := by decide +kernel
  have b2256 : batch 2256 4 = true := by decide +kernel
  have b2260 : batch 2260 4 = true := by decide +kernel
  have b2264 : batch 2264 4 = true := by decide +kernel
  have b2268 : batch 2268 4 = true := by decide +kernel
  have b2272 : batch 2272 4 = true := by decide +kernel
  have b2276 : batch 2276 4 = true := by decide +kernel
  have b2280 : batch 2280 4 = true := by decide +kernel
  have b2284 : batch 2284 4 = true := by decide +kernel
  have b2288 : batch 2288 4 = true := by decide +kernel
  have b2292 : batch 2292 4 = true := by decide +kernel
  have b2296 : batch 2296 4 = true := by decide +kernel
  have b2300 : batch 2300 4 = true := by decide +kernel
  exact (@stitch 2208 4 b2208 (@stitch 2212 4 b2212 (@stitch 2216 4 b2216 (@stitch 2220 4 b2220 (@stitch 2224 4 b2224 (@stitch 2228 4 b2228 (@stitch 2232 4 b2232 (@stitch 2236 4 b2236 (@stitch 2240 4 b2240 (@stitch 2244 4 b2244 (@stitch 2248 4 b2248 (@stitch 2252 4 b2252 (@stitch 2256 4 b2256 (@stitch 2260 4 b2260 (@stitch 2264 4 b2264 (@stitch 2268 4 b2268 (@stitch 2272 4 b2272 (@stitch 2276 4 b2276 (@stitch 2280 4 b2280 (@stitch 2284 4 b2284 (@stitch 2288 4 b2288 (@stitch 2292 4 b2292 (@stitch 2296 4 b2296 (@stitch 2300 4 b2300 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2304 (tail : remaining 2400 = true) : remaining 2304 = true := by
  have b2304 : batch 2304 4 = true := by decide +kernel
  have b2308 : batch 2308 4 = true := by decide +kernel
  have b2312 : batch 2312 4 = true := by decide +kernel
  have b2316 : batch 2316 4 = true := by decide +kernel
  have b2320 : batch 2320 4 = true := by decide +kernel
  have b2324 : batch 2324 4 = true := by decide +kernel
  have b2328 : batch 2328 4 = true := by decide +kernel
  have b2332 : batch 2332 4 = true := by decide +kernel
  have b2336 : batch 2336 4 = true := by decide +kernel
  have b2340 : batch 2340 4 = true := by decide +kernel
  have b2344 : batch 2344 4 = true := by decide +kernel
  have b2348 : batch 2348 4 = true := by decide +kernel
  have b2352 : batch 2352 4 = true := by decide +kernel
  have b2356 : batch 2356 4 = true := by decide +kernel
  have b2360 : batch 2360 4 = true := by decide +kernel
  have b2364 : batch 2364 4 = true := by decide +kernel
  have b2368 : batch 2368 4 = true := by decide +kernel
  have b2372 : batch 2372 4 = true := by decide +kernel
  have b2376 : batch 2376 4 = true := by decide +kernel
  have b2380 : batch 2380 4 = true := by decide +kernel
  have b2384 : batch 2384 4 = true := by decide +kernel
  have b2388 : batch 2388 4 = true := by decide +kernel
  have b2392 : batch 2392 4 = true := by decide +kernel
  have b2396 : batch 2396 4 = true := by decide +kernel
  exact (@stitch 2304 4 b2304 (@stitch 2308 4 b2308 (@stitch 2312 4 b2312 (@stitch 2316 4 b2316 (@stitch 2320 4 b2320 (@stitch 2324 4 b2324 (@stitch 2328 4 b2328 (@stitch 2332 4 b2332 (@stitch 2336 4 b2336 (@stitch 2340 4 b2340 (@stitch 2344 4 b2344 (@stitch 2348 4 b2348 (@stitch 2352 4 b2352 (@stitch 2356 4 b2356 (@stitch 2360 4 b2360 (@stitch 2364 4 b2364 (@stitch 2368 4 b2368 (@stitch 2372 4 b2372 (@stitch 2376 4 b2376 (@stitch 2380 4 b2380 (@stitch 2384 4 b2384 (@stitch 2388 4 b2388 (@stitch 2392 4 b2392 (@stitch 2396 4 b2396 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2400 (tail : remaining 2496 = true) : remaining 2400 = true := by
  have b2400 : batch 2400 4 = true := by decide +kernel
  have b2404 : batch 2404 4 = true := by decide +kernel
  have b2408 : batch 2408 4 = true := by decide +kernel
  have b2412 : batch 2412 4 = true := by decide +kernel
  have b2416 : batch 2416 4 = true := by decide +kernel
  have b2420 : batch 2420 4 = true := by decide +kernel
  have b2424 : batch 2424 4 = true := by decide +kernel
  have b2428 : batch 2428 4 = true := by decide +kernel
  have v2432 : batch 2432 1 = true := by decide +kernel
  have v2433 : batch 2433 1 = true := by decide +kernel
  have v2434 : batch 2434 1 = true := by decide +kernel
  have v2435 : batch 2435 1 = true := by decide +kernel
  have b2432 : batch 2432 4 = true := (joinBatch v2432 (joinBatch v2433 (joinBatch v2434 v2435)))
  have b2436 : batch 2436 4 = true := by decide +kernel
  have b2440 : batch 2440 4 = true := by decide +kernel
  have b2444 : batch 2444 4 = true := by decide +kernel
  have b2448 : batch 2448 4 = true := by decide +kernel
  have v2452 : batch 2452 1 = true := by decide +kernel
  have v2453 : batch 2453 1 = true := by decide +kernel
  have v2454 : batch 2454 1 = true := by decide +kernel
  have v2455 : batch 2455 1 = true := by decide +kernel
  have b2452 : batch 2452 4 = true := (joinBatch v2452 (joinBatch v2453 (joinBatch v2454 v2455)))
  have b2456 : batch 2456 4 = true := by decide +kernel
  have b2460 : batch 2460 4 = true := by decide +kernel
  have b2464 : batch 2464 4 = true := by decide +kernel
  have v2468 : batch 2468 1 = true := by decide +kernel
  have v2469 : batch 2469 1 = true := by decide +kernel
  have v2470 : batch 2470 1 = true := by decide +kernel
  have v2471 : batch 2471 1 = true := by decide +kernel
  have b2468 : batch 2468 4 = true := (joinBatch v2468 (joinBatch v2469 (joinBatch v2470 v2471)))
  have b2472 : batch 2472 4 = true := by decide +kernel
  have b2476 : batch 2476 4 = true := by decide +kernel
  have b2480 : batch 2480 4 = true := by decide +kernel
  have b2484 : batch 2484 4 = true := by decide +kernel
  have b2488 : batch 2488 4 = true := by decide +kernel
  have b2492 : batch 2492 4 = true := by decide +kernel
  exact (@stitch 2400 4 b2400 (@stitch 2404 4 b2404 (@stitch 2408 4 b2408 (@stitch 2412 4 b2412 (@stitch 2416 4 b2416 (@stitch 2420 4 b2420 (@stitch 2424 4 b2424 (@stitch 2428 4 b2428 (@stitch 2432 4 b2432 (@stitch 2436 4 b2436 (@stitch 2440 4 b2440 (@stitch 2444 4 b2444 (@stitch 2448 4 b2448 (@stitch 2452 4 b2452 (@stitch 2456 4 b2456 (@stitch 2460 4 b2460 (@stitch 2464 4 b2464 (@stitch 2468 4 b2468 (@stitch 2472 4 b2472 (@stitch 2476 4 b2476 (@stitch 2480 4 b2480 (@stitch 2484 4 b2484 (@stitch 2488 4 b2488 (@stitch 2492 4 b2492 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2496 (tail : remaining 2592 = true) : remaining 2496 = true := by
  have b2496 : batch 2496 4 = true := by decide +kernel
  have b2500 : batch 2500 4 = true := by decide +kernel
  have b2504 : batch 2504 4 = true := by decide +kernel
  have b2508 : batch 2508 4 = true := by decide +kernel
  have b2512 : batch 2512 4 = true := by decide +kernel
  have b2516 : batch 2516 4 = true := by decide +kernel
  have b2520 : batch 2520 4 = true := by decide +kernel
  have b2524 : batch 2524 4 = true := by decide +kernel
  have b2528 : batch 2528 4 = true := by decide +kernel
  have b2532 : batch 2532 4 = true := by decide +kernel
  have b2536 : batch 2536 4 = true := by decide +kernel
  have b2540 : batch 2540 4 = true := by decide +kernel
  have b2544 : batch 2544 4 = true := by decide +kernel
  have b2548 : batch 2548 4 = true := by decide +kernel
  have b2552 : batch 2552 4 = true := by decide +kernel
  have b2556 : batch 2556 4 = true := by decide +kernel
  have b2560 : batch 2560 4 = true := by decide +kernel
  have b2564 : batch 2564 4 = true := by decide +kernel
  have b2568 : batch 2568 4 = true := by decide +kernel
  have b2572 : batch 2572 4 = true := by decide +kernel
  have b2576 : batch 2576 4 = true := by decide +kernel
  have b2580 : batch 2580 4 = true := by decide +kernel
  have b2584 : batch 2584 4 = true := by decide +kernel
  have b2588 : batch 2588 4 = true := by decide +kernel
  exact (@stitch 2496 4 b2496 (@stitch 2500 4 b2500 (@stitch 2504 4 b2504 (@stitch 2508 4 b2508 (@stitch 2512 4 b2512 (@stitch 2516 4 b2516 (@stitch 2520 4 b2520 (@stitch 2524 4 b2524 (@stitch 2528 4 b2528 (@stitch 2532 4 b2532 (@stitch 2536 4 b2536 (@stitch 2540 4 b2540 (@stitch 2544 4 b2544 (@stitch 2548 4 b2548 (@stitch 2552 4 b2552 (@stitch 2556 4 b2556 (@stitch 2560 4 b2560 (@stitch 2564 4 b2564 (@stitch 2568 4 b2568 (@stitch 2572 4 b2572 (@stitch 2576 4 b2576 (@stitch 2580 4 b2580 (@stitch 2584 4 b2584 (@stitch 2588 4 b2588 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2592 (tail : remaining 2688 = true) : remaining 2592 = true := by
  have b2592 : batch 2592 4 = true := by decide +kernel
  have b2596 : batch 2596 4 = true := by decide +kernel
  have b2600 : batch 2600 4 = true := by decide +kernel
  have b2604 : batch 2604 4 = true := by decide +kernel
  have b2608 : batch 2608 4 = true := by decide +kernel
  have b2612 : batch 2612 4 = true := by decide +kernel
  have b2616 : batch 2616 4 = true := by decide +kernel
  have b2620 : batch 2620 4 = true := by decide +kernel
  have b2624 : batch 2624 4 = true := by decide +kernel
  have b2628 : batch 2628 4 = true := by decide +kernel
  have b2632 : batch 2632 4 = true := by decide +kernel
  have b2636 : batch 2636 4 = true := by decide +kernel
  have b2640 : batch 2640 4 = true := by decide +kernel
  have b2644 : batch 2644 4 = true := by decide +kernel
  have b2648 : batch 2648 4 = true := by decide +kernel
  have b2652 : batch 2652 4 = true := by decide +kernel
  have b2656 : batch 2656 4 = true := by decide +kernel
  have b2660 : batch 2660 4 = true := by decide +kernel
  have b2664 : batch 2664 4 = true := by decide +kernel
  have b2668 : batch 2668 4 = true := by decide +kernel
  have b2672 : batch 2672 4 = true := by decide +kernel
  have b2676 : batch 2676 4 = true := by decide +kernel
  have b2680 : batch 2680 4 = true := by decide +kernel
  have b2684 : batch 2684 4 = true := by decide +kernel
  exact (@stitch 2592 4 b2592 (@stitch 2596 4 b2596 (@stitch 2600 4 b2600 (@stitch 2604 4 b2604 (@stitch 2608 4 b2608 (@stitch 2612 4 b2612 (@stitch 2616 4 b2616 (@stitch 2620 4 b2620 (@stitch 2624 4 b2624 (@stitch 2628 4 b2628 (@stitch 2632 4 b2632 (@stitch 2636 4 b2636 (@stitch 2640 4 b2640 (@stitch 2644 4 b2644 (@stitch 2648 4 b2648 (@stitch 2652 4 b2652 (@stitch 2656 4 b2656 (@stitch 2660 4 b2660 (@stitch 2664 4 b2664 (@stitch 2668 4 b2668 (@stitch 2672 4 b2672 (@stitch 2676 4 b2676 (@stitch 2680 4 b2680 (@stitch 2684 4 b2684 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2688 (tail : remaining 2784 = true) : remaining 2688 = true := by
  have b2688 : batch 2688 4 = true := by decide +kernel
  have b2692 : batch 2692 4 = true := by decide +kernel
  have b2696 : batch 2696 4 = true := by decide +kernel
  have b2700 : batch 2700 4 = true := by decide +kernel
  have b2704 : batch 2704 4 = true := by decide +kernel
  have b2708 : batch 2708 4 = true := by decide +kernel
  have b2712 : batch 2712 4 = true := by decide +kernel
  have b2716 : batch 2716 4 = true := by decide +kernel
  have b2720 : batch 2720 4 = true := by decide +kernel
  have b2724 : batch 2724 4 = true := by decide +kernel
  have b2728 : batch 2728 4 = true := by decide +kernel
  have b2732 : batch 2732 4 = true := by decide +kernel
  have b2736 : batch 2736 4 = true := by decide +kernel
  have b2740 : batch 2740 4 = true := by decide +kernel
  have b2744 : batch 2744 4 = true := by decide +kernel
  have b2748 : batch 2748 4 = true := by decide +kernel
  have b2752 : batch 2752 4 = true := by decide +kernel
  have v2756 : batch 2756 1 = true := by decide +kernel
  have v2757 : batch 2757 1 = true := by decide +kernel
  have v2758 : batch 2758 1 = true := by decide +kernel
  have v2759 : batch 2759 1 = true := by decide +kernel
  have b2756 : batch 2756 4 = true := (joinBatch v2756 (joinBatch v2757 (joinBatch v2758 v2759)))
  have v2760 : batch 2760 1 = true := by decide +kernel
  have v2761 : batch 2761 1 = true := by decide +kernel
  have v2762 : batch 2762 1 = true := by decide +kernel
  have v2763 : batch 2763 1 = true := by decide +kernel
  have b2760 : batch 2760 4 = true := (joinBatch v2760 (joinBatch v2761 (joinBatch v2762 v2763)))
  have v2764 : batch 2764 1 = true := by decide +kernel
  have v2765 : batch 2765 1 = true := by decide +kernel
  have v2766 : batch 2766 1 = true := by decide +kernel
  have v2767 : batch 2767 1 = true := by decide +kernel
  have b2764 : batch 2764 4 = true := (joinBatch v2764 (joinBatch v2765 (joinBatch v2766 v2767)))
  have b2768 : batch 2768 4 = true := by decide +kernel
  have b2772 : batch 2772 4 = true := by decide +kernel
  have v2776 : batch 2776 1 = true := by decide +kernel
  have v2777 : batch 2777 1 = true := by decide +kernel
  have v2778 : batch 2778 1 = true := by decide +kernel
  have v2779 : batch 2779 1 = true := by decide +kernel
  have b2776 : batch 2776 4 = true := (joinBatch v2776 (joinBatch v2777 (joinBatch v2778 v2779)))
  have v2780 : batch 2780 1 = true := by decide +kernel
  have v2781 : batch 2781 1 = true := by decide +kernel
  have v2782 : batch 2782 1 = true := by decide +kernel
  have v2783 : batch 2783 1 = true := by decide +kernel
  have b2780 : batch 2780 4 = true := (joinBatch v2780 (joinBatch v2781 (joinBatch v2782 v2783)))
  exact (@stitch 2688 4 b2688 (@stitch 2692 4 b2692 (@stitch 2696 4 b2696 (@stitch 2700 4 b2700 (@stitch 2704 4 b2704 (@stitch 2708 4 b2708 (@stitch 2712 4 b2712 (@stitch 2716 4 b2716 (@stitch 2720 4 b2720 (@stitch 2724 4 b2724 (@stitch 2728 4 b2728 (@stitch 2732 4 b2732 (@stitch 2736 4 b2736 (@stitch 2740 4 b2740 (@stitch 2744 4 b2744 (@stitch 2748 4 b2748 (@stitch 2752 4 b2752 (@stitch 2756 4 b2756 (@stitch 2760 4 b2760 (@stitch 2764 4 b2764 (@stitch 2768 4 b2768 (@stitch 2772 4 b2772 (@stitch 2776 4 b2776 (@stitch 2780 4 b2780 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2784 (tail : remaining 2880 = true) : remaining 2784 = true := by
  have v2784 : batch 2784 1 = true := by decide +kernel
  have v2785 : batch 2785 1 = true := by decide +kernel
  have v2786 : batch 2786 1 = true := by decide +kernel
  have v2787 : batch 2787 1 = true := by decide +kernel
  have b2784 : batch 2784 4 = true := (joinBatch v2784 (joinBatch v2785 (joinBatch v2786 v2787)))
  have v2788 : batch 2788 1 = true := by decide +kernel
  have v2789 : batch 2789 1 = true := by decide +kernel
  have v2790 : batch 2790 1 = true := by decide +kernel
  have v2791 : batch 2791 1 = true := by decide +kernel
  have b2788 : batch 2788 4 = true := (joinBatch v2788 (joinBatch v2789 (joinBatch v2790 v2791)))
  have v2792 : batch 2792 1 = true := by decide +kernel
  have v2793 : batch 2793 1 = true := by decide +kernel
  have v2794 : batch 2794 1 = true := by decide +kernel
  have v2795 : batch 2795 1 = true := by decide +kernel
  have b2792 : batch 2792 4 = true := (joinBatch v2792 (joinBatch v2793 (joinBatch v2794 v2795)))
  have v2796 : batch 2796 1 = true := by decide +kernel
  have v2797 : batch 2797 1 = true := by decide +kernel
  have v2798 : batch 2798 1 = true := by decide +kernel
  have v2799 : batch 2799 1 = true := by decide +kernel
  have b2796 : batch 2796 4 = true := (joinBatch v2796 (joinBatch v2797 (joinBatch v2798 v2799)))
  have b2800 : batch 2800 4 = true := by decide +kernel
  have b2804 : batch 2804 4 = true := by decide +kernel
  have b2808 : batch 2808 4 = true := by decide +kernel
  have b2812 : batch 2812 4 = true := by decide +kernel
  have b2816 : batch 2816 4 = true := by decide +kernel
  have b2820 : batch 2820 4 = true := by decide +kernel
  have b2824 : batch 2824 4 = true := by decide +kernel
  have b2828 : batch 2828 4 = true := by decide +kernel
  have b2832 : batch 2832 4 = true := by decide +kernel
  have b2836 : batch 2836 4 = true := by decide +kernel
  have b2840 : batch 2840 4 = true := by decide +kernel
  have b2844 : batch 2844 4 = true := by decide +kernel
  have b2848 : batch 2848 4 = true := by decide +kernel
  have b2852 : batch 2852 4 = true := by decide +kernel
  have b2856 : batch 2856 4 = true := by decide +kernel
  have b2860 : batch 2860 4 = true := by decide +kernel
  have b2864 : batch 2864 4 = true := by decide +kernel
  have b2868 : batch 2868 4 = true := by decide +kernel
  have b2872 : batch 2872 4 = true := by decide +kernel
  have b2876 : batch 2876 4 = true := by decide +kernel
  exact (@stitch 2784 4 b2784 (@stitch 2788 4 b2788 (@stitch 2792 4 b2792 (@stitch 2796 4 b2796 (@stitch 2800 4 b2800 (@stitch 2804 4 b2804 (@stitch 2808 4 b2808 (@stitch 2812 4 b2812 (@stitch 2816 4 b2816 (@stitch 2820 4 b2820 (@stitch 2824 4 b2824 (@stitch 2828 4 b2828 (@stitch 2832 4 b2832 (@stitch 2836 4 b2836 (@stitch 2840 4 b2840 (@stitch 2844 4 b2844 (@stitch 2848 4 b2848 (@stitch 2852 4 b2852 (@stitch 2856 4 b2856 (@stitch 2860 4 b2860 (@stitch 2864 4 b2864 (@stitch 2868 4 b2868 (@stitch 2872 4 b2872 (@stitch 2876 4 b2876 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2880 (tail : remaining 2976 = true) : remaining 2880 = true := by
  have b2880 : batch 2880 4 = true := by decide +kernel
  have b2884 : batch 2884 4 = true := by decide +kernel
  have b2888 : batch 2888 4 = true := by decide +kernel
  have b2892 : batch 2892 4 = true := by decide +kernel
  have b2896 : batch 2896 4 = true := by decide +kernel
  have b2900 : batch 2900 4 = true := by decide +kernel
  have b2904 : batch 2904 4 = true := by decide +kernel
  have b2908 : batch 2908 4 = true := by decide +kernel
  have b2912 : batch 2912 4 = true := by decide +kernel
  have b2916 : batch 2916 4 = true := by decide +kernel
  have b2920 : batch 2920 4 = true := by decide +kernel
  have b2924 : batch 2924 4 = true := by decide +kernel
  have b2928 : batch 2928 4 = true := by decide +kernel
  have b2932 : batch 2932 4 = true := by decide +kernel
  have b2936 : batch 2936 4 = true := by decide +kernel
  have b2940 : batch 2940 4 = true := by decide +kernel
  have b2944 : batch 2944 4 = true := by decide +kernel
  have b2948 : batch 2948 4 = true := by decide +kernel
  have b2952 : batch 2952 4 = true := by decide +kernel
  have b2956 : batch 2956 4 = true := by decide +kernel
  have b2960 : batch 2960 4 = true := by decide +kernel
  have b2964 : batch 2964 4 = true := by decide +kernel
  have b2968 : batch 2968 4 = true := by decide +kernel
  have b2972 : batch 2972 4 = true := by decide +kernel
  exact (@stitch 2880 4 b2880 (@stitch 2884 4 b2884 (@stitch 2888 4 b2888 (@stitch 2892 4 b2892 (@stitch 2896 4 b2896 (@stitch 2900 4 b2900 (@stitch 2904 4 b2904 (@stitch 2908 4 b2908 (@stitch 2912 4 b2912 (@stitch 2916 4 b2916 (@stitch 2920 4 b2920 (@stitch 2924 4 b2924 (@stitch 2928 4 b2928 (@stitch 2932 4 b2932 (@stitch 2936 4 b2936 (@stitch 2940 4 b2940 (@stitch 2944 4 b2944 (@stitch 2948 4 b2948 (@stitch 2952 4 b2952 (@stitch 2956 4 b2956 (@stitch 2960 4 b2960 (@stitch 2964 4 b2964 (@stitch 2968 4 b2968 (@stitch 2972 4 b2972 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock2976 (tail : remaining 3072 = true) : remaining 2976 = true := by
  have b2976 : batch 2976 4 = true := by decide +kernel
  have b2980 : batch 2980 4 = true := by decide +kernel
  have b2984 : batch 2984 4 = true := by decide +kernel
  have b2988 : batch 2988 4 = true := by decide +kernel
  have b2992 : batch 2992 4 = true := by decide +kernel
  have b2996 : batch 2996 4 = true := by decide +kernel
  have b3000 : batch 3000 4 = true := by decide +kernel
  have b3004 : batch 3004 4 = true := by decide +kernel
  have b3008 : batch 3008 4 = true := by decide +kernel
  have b3012 : batch 3012 4 = true := by decide +kernel
  have b3016 : batch 3016 4 = true := by decide +kernel
  have b3020 : batch 3020 4 = true := by decide +kernel
  have b3024 : batch 3024 4 = true := by decide +kernel
  have b3028 : batch 3028 4 = true := by decide +kernel
  have b3032 : batch 3032 4 = true := by decide +kernel
  have b3036 : batch 3036 4 = true := by decide +kernel
  have b3040 : batch 3040 4 = true := by decide +kernel
  have b3044 : batch 3044 4 = true := by decide +kernel
  have b3048 : batch 3048 4 = true := by decide +kernel
  have b3052 : batch 3052 4 = true := by decide +kernel
  have b3056 : batch 3056 4 = true := by decide +kernel
  have b3060 : batch 3060 4 = true := by decide +kernel
  have b3064 : batch 3064 4 = true := by decide +kernel
  have b3068 : batch 3068 4 = true := by decide +kernel
  exact (@stitch 2976 4 b2976 (@stitch 2980 4 b2980 (@stitch 2984 4 b2984 (@stitch 2988 4 b2988 (@stitch 2992 4 b2992 (@stitch 2996 4 b2996 (@stitch 3000 4 b3000 (@stitch 3004 4 b3004 (@stitch 3008 4 b3008 (@stitch 3012 4 b3012 (@stitch 3016 4 b3016 (@stitch 3020 4 b3020 (@stitch 3024 4 b3024 (@stitch 3028 4 b3028 (@stitch 3032 4 b3032 (@stitch 3036 4 b3036 (@stitch 3040 4 b3040 (@stitch 3044 4 b3044 (@stitch 3048 4 b3048 (@stitch 3052 4 b3052 (@stitch 3056 4 b3056 (@stitch 3060 4 b3060 (@stitch 3064 4 b3064 (@stitch 3068 4 b3068 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3072 (tail : remaining 3168 = true) : remaining 3072 = true := by
  have b3072 : batch 3072 4 = true := by decide +kernel
  have b3076 : batch 3076 4 = true := by decide +kernel
  have b3080 : batch 3080 4 = true := by decide +kernel
  have b3084 : batch 3084 4 = true := by decide +kernel
  have b3088 : batch 3088 4 = true := by decide +kernel
  have b3092 : batch 3092 4 = true := by decide +kernel
  have b3096 : batch 3096 4 = true := by decide +kernel
  have b3100 : batch 3100 4 = true := by decide +kernel
  have b3104 : batch 3104 4 = true := by decide +kernel
  have b3108 : batch 3108 4 = true := by decide +kernel
  have b3112 : batch 3112 4 = true := by decide +kernel
  have b3116 : batch 3116 4 = true := by decide +kernel
  have b3120 : batch 3120 4 = true := by decide +kernel
  have b3124 : batch 3124 4 = true := by decide +kernel
  have b3128 : batch 3128 4 = true := by decide +kernel
  have b3132 : batch 3132 4 = true := by decide +kernel
  have b3136 : batch 3136 4 = true := by decide +kernel
  have b3140 : batch 3140 4 = true := by decide +kernel
  have b3144 : batch 3144 4 = true := by decide +kernel
  have b3148 : batch 3148 4 = true := by decide +kernel
  have b3152 : batch 3152 4 = true := by decide +kernel
  have b3156 : batch 3156 4 = true := by decide +kernel
  have b3160 : batch 3160 4 = true := by decide +kernel
  have b3164 : batch 3164 4 = true := by decide +kernel
  exact (@stitch 3072 4 b3072 (@stitch 3076 4 b3076 (@stitch 3080 4 b3080 (@stitch 3084 4 b3084 (@stitch 3088 4 b3088 (@stitch 3092 4 b3092 (@stitch 3096 4 b3096 (@stitch 3100 4 b3100 (@stitch 3104 4 b3104 (@stitch 3108 4 b3108 (@stitch 3112 4 b3112 (@stitch 3116 4 b3116 (@stitch 3120 4 b3120 (@stitch 3124 4 b3124 (@stitch 3128 4 b3128 (@stitch 3132 4 b3132 (@stitch 3136 4 b3136 (@stitch 3140 4 b3140 (@stitch 3144 4 b3144 (@stitch 3148 4 b3148 (@stitch 3152 4 b3152 (@stitch 3156 4 b3156 (@stitch 3160 4 b3160 (@stitch 3164 4 b3164 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3168 (tail : remaining 3264 = true) : remaining 3168 = true := by
  have b3168 : batch 3168 4 = true := by decide +kernel
  have b3172 : batch 3172 4 = true := by decide +kernel
  have b3176 : batch 3176 4 = true := by decide +kernel
  have b3180 : batch 3180 4 = true := by decide +kernel
  have b3184 : batch 3184 4 = true := by decide +kernel
  have b3188 : batch 3188 4 = true := by decide +kernel
  have b3192 : batch 3192 4 = true := by decide +kernel
  have b3196 : batch 3196 4 = true := by decide +kernel
  have b3200 : batch 3200 4 = true := by decide +kernel
  have b3204 : batch 3204 4 = true := by decide +kernel
  have b3208 : batch 3208 4 = true := by decide +kernel
  have v3212 : batch 3212 1 = true := by decide +kernel
  have v3213 : batch 3213 1 = true := by decide +kernel
  have v3214 : batch 3214 1 = true := by decide +kernel
  have v3215 : batch 3215 1 = true := by decide +kernel
  have b3212 : batch 3212 4 = true := (joinBatch v3212 (joinBatch v3213 (joinBatch v3214 v3215)))
  have b3216 : batch 3216 4 = true := by decide +kernel
  have b3220 : batch 3220 4 = true := by decide +kernel
  have b3224 : batch 3224 4 = true := by decide +kernel
  have b3228 : batch 3228 4 = true := by decide +kernel
  have b3232 : batch 3232 4 = true := by decide +kernel
  have b3236 : batch 3236 4 = true := by decide +kernel
  have b3240 : batch 3240 4 = true := by decide +kernel
  have b3244 : batch 3244 4 = true := by decide +kernel
  have b3248 : batch 3248 4 = true := by decide +kernel
  have v3252 : batch 3252 1 = true := by decide +kernel
  have v3253 : batch 3253 1 = true := by decide +kernel
  have v3254 : batch 3254 1 = true := by decide +kernel
  have v3255 : batch 3255 1 = true := by decide +kernel
  have b3252 : batch 3252 4 = true := (joinBatch v3252 (joinBatch v3253 (joinBatch v3254 v3255)))
  have b3256 : batch 3256 4 = true := by decide +kernel
  have b3260 : batch 3260 4 = true := by decide +kernel
  exact (@stitch 3168 4 b3168 (@stitch 3172 4 b3172 (@stitch 3176 4 b3176 (@stitch 3180 4 b3180 (@stitch 3184 4 b3184 (@stitch 3188 4 b3188 (@stitch 3192 4 b3192 (@stitch 3196 4 b3196 (@stitch 3200 4 b3200 (@stitch 3204 4 b3204 (@stitch 3208 4 b3208 (@stitch 3212 4 b3212 (@stitch 3216 4 b3216 (@stitch 3220 4 b3220 (@stitch 3224 4 b3224 (@stitch 3228 4 b3228 (@stitch 3232 4 b3232 (@stitch 3236 4 b3236 (@stitch 3240 4 b3240 (@stitch 3244 4 b3244 (@stitch 3248 4 b3248 (@stitch 3252 4 b3252 (@stitch 3256 4 b3256 (@stitch 3260 4 b3260 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3264 (tail : remaining 3360 = true) : remaining 3264 = true := by
  have b3264 : batch 3264 4 = true := by decide +kernel
  have b3268 : batch 3268 4 = true := by decide +kernel
  have b3272 : batch 3272 4 = true := by decide +kernel
  have b3276 : batch 3276 4 = true := by decide +kernel
  have b3280 : batch 3280 4 = true := by decide +kernel
  have v3284 : batch 3284 1 = true := by decide +kernel
  have v3285 : batch 3285 1 = true := by decide +kernel
  have v3286 : batch 3286 1 = true := by decide +kernel
  have v3287 : batch 3287 1 = true := by decide +kernel
  have b3284 : batch 3284 4 = true := (joinBatch v3284 (joinBatch v3285 (joinBatch v3286 v3287)))
  have v3288 : batch 3288 1 = true := by decide +kernel
  have v3289 : batch 3289 1 = true := by decide +kernel
  have v3290 : batch 3290 1 = true := by decide +kernel
  have v3291 : batch 3291 1 = true := by decide +kernel
  have b3288 : batch 3288 4 = true := (joinBatch v3288 (joinBatch v3289 (joinBatch v3290 v3291)))
  have b3292 : batch 3292 4 = true := by decide +kernel
  have b3296 : batch 3296 4 = true := by decide +kernel
  have b3300 : batch 3300 4 = true := by decide +kernel
  have v3304 : batch 3304 1 = true := by decide +kernel
  have v3305 : batch 3305 1 = true := by decide +kernel
  have v3306 : batch 3306 1 = true := by decide +kernel
  have v3307 : batch 3307 1 = true := by decide +kernel
  have b3304 : batch 3304 4 = true := (joinBatch v3304 (joinBatch v3305 (joinBatch v3306 v3307)))
  have b3308 : batch 3308 4 = true := by decide +kernel
  have b3312 : batch 3312 4 = true := by decide +kernel
  have b3316 : batch 3316 4 = true := by decide +kernel
  have b3320 : batch 3320 4 = true := by decide +kernel
  have b3324 : batch 3324 4 = true := by decide +kernel
  have b3328 : batch 3328 4 = true := by decide +kernel
  have b3332 : batch 3332 4 = true := by decide +kernel
  have b3336 : batch 3336 4 = true := by decide +kernel
  have b3340 : batch 3340 4 = true := by decide +kernel
  have b3344 : batch 3344 4 = true := by decide +kernel
  have b3348 : batch 3348 4 = true := by decide +kernel
  have b3352 : batch 3352 4 = true := by decide +kernel
  have b3356 : batch 3356 4 = true := by decide +kernel
  exact (@stitch 3264 4 b3264 (@stitch 3268 4 b3268 (@stitch 3272 4 b3272 (@stitch 3276 4 b3276 (@stitch 3280 4 b3280 (@stitch 3284 4 b3284 (@stitch 3288 4 b3288 (@stitch 3292 4 b3292 (@stitch 3296 4 b3296 (@stitch 3300 4 b3300 (@stitch 3304 4 b3304 (@stitch 3308 4 b3308 (@stitch 3312 4 b3312 (@stitch 3316 4 b3316 (@stitch 3320 4 b3320 (@stitch 3324 4 b3324 (@stitch 3328 4 b3328 (@stitch 3332 4 b3332 (@stitch 3336 4 b3336 (@stitch 3340 4 b3340 (@stitch 3344 4 b3344 (@stitch 3348 4 b3348 (@stitch 3352 4 b3352 (@stitch 3356 4 b3356 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3360 (tail : remaining 3456 = true) : remaining 3360 = true := by
  have b3360 : batch 3360 4 = true := by decide +kernel
  have b3364 : batch 3364 4 = true := by decide +kernel
  have b3368 : batch 3368 4 = true := by decide +kernel
  have b3372 : batch 3372 4 = true := by decide +kernel
  have b3376 : batch 3376 4 = true := by decide +kernel
  have b3380 : batch 3380 4 = true := by decide +kernel
  have b3384 : batch 3384 4 = true := by decide +kernel
  have b3388 : batch 3388 4 = true := by decide +kernel
  have b3392 : batch 3392 4 = true := by decide +kernel
  have b3396 : batch 3396 4 = true := by decide +kernel
  have b3400 : batch 3400 4 = true := by decide +kernel
  have b3404 : batch 3404 4 = true := by decide +kernel
  have b3408 : batch 3408 4 = true := by decide +kernel
  have b3412 : batch 3412 4 = true := by decide +kernel
  have b3416 : batch 3416 4 = true := by decide +kernel
  have b3420 : batch 3420 4 = true := by decide +kernel
  have b3424 : batch 3424 4 = true := by decide +kernel
  have b3428 : batch 3428 4 = true := by decide +kernel
  have b3432 : batch 3432 4 = true := by decide +kernel
  have b3436 : batch 3436 4 = true := by decide +kernel
  have b3440 : batch 3440 4 = true := by decide +kernel
  have b3444 : batch 3444 4 = true := by decide +kernel
  have b3448 : batch 3448 4 = true := by decide +kernel
  have b3452 : batch 3452 4 = true := by decide +kernel
  exact (@stitch 3360 4 b3360 (@stitch 3364 4 b3364 (@stitch 3368 4 b3368 (@stitch 3372 4 b3372 (@stitch 3376 4 b3376 (@stitch 3380 4 b3380 (@stitch 3384 4 b3384 (@stitch 3388 4 b3388 (@stitch 3392 4 b3392 (@stitch 3396 4 b3396 (@stitch 3400 4 b3400 (@stitch 3404 4 b3404 (@stitch 3408 4 b3408 (@stitch 3412 4 b3412 (@stitch 3416 4 b3416 (@stitch 3420 4 b3420 (@stitch 3424 4 b3424 (@stitch 3428 4 b3428 (@stitch 3432 4 b3432 (@stitch 3436 4 b3436 (@stitch 3440 4 b3440 (@stitch 3444 4 b3444 (@stitch 3448 4 b3448 (@stitch 3452 4 b3452 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3456 (tail : remaining 3552 = true) : remaining 3456 = true := by
  have b3456 : batch 3456 4 = true := by decide +kernel
  have b3460 : batch 3460 4 = true := by decide +kernel
  have b3464 : batch 3464 4 = true := by decide +kernel
  have b3468 : batch 3468 4 = true := by decide +kernel
  have b3472 : batch 3472 4 = true := by decide +kernel
  have b3476 : batch 3476 4 = true := by decide +kernel
  have b3480 : batch 3480 4 = true := by decide +kernel
  have b3484 : batch 3484 4 = true := by decide +kernel
  have b3488 : batch 3488 4 = true := by decide +kernel
  have b3492 : batch 3492 4 = true := by decide +kernel
  have b3496 : batch 3496 4 = true := by decide +kernel
  have b3500 : batch 3500 4 = true := by decide +kernel
  have b3504 : batch 3504 4 = true := by decide +kernel
  have b3508 : batch 3508 4 = true := by decide +kernel
  have b3512 : batch 3512 4 = true := by decide +kernel
  have b3516 : batch 3516 4 = true := by decide +kernel
  have b3520 : batch 3520 4 = true := by decide +kernel
  have b3524 : batch 3524 4 = true := by decide +kernel
  have b3528 : batch 3528 4 = true := by decide +kernel
  have b3532 : batch 3532 4 = true := by decide +kernel
  have b3536 : batch 3536 4 = true := by decide +kernel
  have b3540 : batch 3540 4 = true := by decide +kernel
  have b3544 : batch 3544 4 = true := by decide +kernel
  have b3548 : batch 3548 4 = true := by decide +kernel
  exact (@stitch 3456 4 b3456 (@stitch 3460 4 b3460 (@stitch 3464 4 b3464 (@stitch 3468 4 b3468 (@stitch 3472 4 b3472 (@stitch 3476 4 b3476 (@stitch 3480 4 b3480 (@stitch 3484 4 b3484 (@stitch 3488 4 b3488 (@stitch 3492 4 b3492 (@stitch 3496 4 b3496 (@stitch 3500 4 b3500 (@stitch 3504 4 b3504 (@stitch 3508 4 b3508 (@stitch 3512 4 b3512 (@stitch 3516 4 b3516 (@stitch 3520 4 b3520 (@stitch 3524 4 b3524 (@stitch 3528 4 b3528 (@stitch 3532 4 b3532 (@stitch 3536 4 b3536 (@stitch 3540 4 b3540 (@stitch 3544 4 b3544 (@stitch 3548 4 b3548 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3552 (tail : remaining 3648 = true) : remaining 3552 = true := by
  have b3552 : batch 3552 4 = true := by decide +kernel
  have b3556 : batch 3556 4 = true := by decide +kernel
  have b3560 : batch 3560 4 = true := by decide +kernel
  have b3564 : batch 3564 4 = true := by decide +kernel
  have b3568 : batch 3568 4 = true := by decide +kernel
  have b3572 : batch 3572 4 = true := by decide +kernel
  have b3576 : batch 3576 4 = true := by decide +kernel
  have b3580 : batch 3580 4 = true := by decide +kernel
  have b3584 : batch 3584 4 = true := by decide +kernel
  have b3588 : batch 3588 4 = true := by decide +kernel
  have b3592 : batch 3592 4 = true := by decide +kernel
  have b3596 : batch 3596 4 = true := by decide +kernel
  have b3600 : batch 3600 4 = true := by decide +kernel
  have b3604 : batch 3604 4 = true := by decide +kernel
  have b3608 : batch 3608 4 = true := by decide +kernel
  have b3612 : batch 3612 4 = true := by decide +kernel
  have b3616 : batch 3616 4 = true := by decide +kernel
  have b3620 : batch 3620 4 = true := by decide +kernel
  have b3624 : batch 3624 4 = true := by decide +kernel
  have b3628 : batch 3628 4 = true := by decide +kernel
  have b3632 : batch 3632 4 = true := by decide +kernel
  have b3636 : batch 3636 4 = true := by decide +kernel
  have b3640 : batch 3640 4 = true := by decide +kernel
  have b3644 : batch 3644 4 = true := by decide +kernel
  exact (@stitch 3552 4 b3552 (@stitch 3556 4 b3556 (@stitch 3560 4 b3560 (@stitch 3564 4 b3564 (@stitch 3568 4 b3568 (@stitch 3572 4 b3572 (@stitch 3576 4 b3576 (@stitch 3580 4 b3580 (@stitch 3584 4 b3584 (@stitch 3588 4 b3588 (@stitch 3592 4 b3592 (@stitch 3596 4 b3596 (@stitch 3600 4 b3600 (@stitch 3604 4 b3604 (@stitch 3608 4 b3608 (@stitch 3612 4 b3612 (@stitch 3616 4 b3616 (@stitch 3620 4 b3620 (@stitch 3624 4 b3624 (@stitch 3628 4 b3628 (@stitch 3632 4 b3632 (@stitch 3636 4 b3636 (@stitch 3640 4 b3640 (@stitch 3644 4 b3644 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3648 (tail : remaining 3744 = true) : remaining 3648 = true := by
  have b3648 : batch 3648 4 = true := by decide +kernel
  have b3652 : batch 3652 4 = true := by decide +kernel
  have b3656 : batch 3656 4 = true := by decide +kernel
  have b3660 : batch 3660 4 = true := by decide +kernel
  have b3664 : batch 3664 4 = true := by decide +kernel
  have b3668 : batch 3668 4 = true := by decide +kernel
  have b3672 : batch 3672 4 = true := by decide +kernel
  have b3676 : batch 3676 4 = true := by decide +kernel
  have b3680 : batch 3680 4 = true := by decide +kernel
  have b3684 : batch 3684 4 = true := by decide +kernel
  have b3688 : batch 3688 4 = true := by decide +kernel
  have b3692 : batch 3692 4 = true := by decide +kernel
  have b3696 : batch 3696 4 = true := by decide +kernel
  have b3700 : batch 3700 4 = true := by decide +kernel
  have b3704 : batch 3704 4 = true := by decide +kernel
  have b3708 : batch 3708 4 = true := by decide +kernel
  have b3712 : batch 3712 4 = true := by decide +kernel
  have b3716 : batch 3716 4 = true := by decide +kernel
  have b3720 : batch 3720 4 = true := by decide +kernel
  have b3724 : batch 3724 4 = true := by decide +kernel
  have op3728_0 : pairBatch 3728 0 2 = true := by decide +kernel
  have op3728_2 : pairBatch 3728 2 2 = true := by decide +kernel
  have op3728_4 : pairBatch 3728 4 2 = true := by decide +kernel
  have op3728_6 : pairBatch 3728 6 2 = true := by decide +kernel
  have op3728_8 : pairBatch 3728 8 2 = true := by decide +kernel
  have op3728_10 : pairBatch 3728 10 2 = true := by decide +kernel
  have op3728_12 : pairBatch 3728 12 2 = true := by decide +kernel
  have op3728_14 : pairBatch 3728 14 1 = true := by decide +kernel
  have v3728 : batch 3728 1 = true := @oneFromPairs 3728 (by decide +kernel) (@fromPairs 3728 (by decide +kernel) (by decide +kernel) (@joinPair 3728 0 2 op3728_0 (@joinPair 3728 2 2 op3728_2 (@joinPair 3728 4 2 op3728_4 (@joinPair 3728 6 2 op3728_6 (@joinPair 3728 8 2 op3728_8 (@joinPair 3728 10 2 op3728_10 (@joinPair 3728 12 2 op3728_12 (@joinPair 3728 14 1 op3728_14 (by decide +kernel))))))))))
  have op3729_0 : pairBatch 3729 0 2 = true := by decide +kernel
  have op3729_2 : pairBatch 3729 2 2 = true := by decide +kernel
  have op3729_4 : pairBatch 3729 4 2 = true := by decide +kernel
  have op3729_6 : pairBatch 3729 6 2 = true := by decide +kernel
  have op3729_8 : pairBatch 3729 8 2 = true := by decide +kernel
  have op3729_10 : pairBatch 3729 10 2 = true := by decide +kernel
  have op3729_12 : pairBatch 3729 12 2 = true := by decide +kernel
  have op3729_14 : pairBatch 3729 14 2 = true := by decide +kernel
  have op3729_16 : pairBatch 3729 16 2 = true := by decide +kernel
  have op3729_18 : pairBatch 3729 18 2 = true := by decide +kernel
  have op3729_20 : pairBatch 3729 20 1 = true := by decide +kernel
  have v3729 : batch 3729 1 = true := @oneFromPairs 3729 (by decide +kernel) (@fromPairs 3729 (by decide +kernel) (by decide +kernel) (@joinPair 3729 0 2 op3729_0 (@joinPair 3729 2 2 op3729_2 (@joinPair 3729 4 2 op3729_4 (@joinPair 3729 6 2 op3729_6 (@joinPair 3729 8 2 op3729_8 (@joinPair 3729 10 2 op3729_10 (@joinPair 3729 12 2 op3729_12 (@joinPair 3729 14 2 op3729_14 (@joinPair 3729 16 2 op3729_16 (@joinPair 3729 18 2 op3729_18 (@joinPair 3729 20 1 op3729_20 (by decide +kernel)))))))))))))
  have op3730_0 : pairBatch 3730 0 2 = true := by decide +kernel
  have op3730_2 : pairBatch 3730 2 2 = true := by decide +kernel
  have op3730_4 : pairBatch 3730 4 2 = true := by decide +kernel
  have op3730_6 : pairBatch 3730 6 2 = true := by decide +kernel
  have op3730_8 : pairBatch 3730 8 2 = true := by decide +kernel
  have op3730_10 : pairBatch 3730 10 2 = true := by decide +kernel
  have op3730_12 : pairBatch 3730 12 2 = true := by decide +kernel
  have op3730_14 : pairBatch 3730 14 2 = true := by decide +kernel
  have op3730_16 : pairBatch 3730 16 2 = true := by decide +kernel
  have op3730_18 : pairBatch 3730 18 2 = true := by decide +kernel
  have op3730_20 : pairBatch 3730 20 1 = true := by decide +kernel
  have v3730 : batch 3730 1 = true := @oneFromPairs 3730 (by decide +kernel) (@fromPairs 3730 (by decide +kernel) (by decide +kernel) (@joinPair 3730 0 2 op3730_0 (@joinPair 3730 2 2 op3730_2 (@joinPair 3730 4 2 op3730_4 (@joinPair 3730 6 2 op3730_6 (@joinPair 3730 8 2 op3730_8 (@joinPair 3730 10 2 op3730_10 (@joinPair 3730 12 2 op3730_12 (@joinPair 3730 14 2 op3730_14 (@joinPair 3730 16 2 op3730_16 (@joinPair 3730 18 2 op3730_18 (@joinPair 3730 20 1 op3730_20 (by decide +kernel)))))))))))))
  have op3731_0 : pairBatch 3731 0 2 = true := by decide +kernel
  have op3731_2 : pairBatch 3731 2 2 = true := by decide +kernel
  have op3731_4 : pairBatch 3731 4 2 = true := by decide +kernel
  have op3731_6 : pairBatch 3731 6 2 = true := by decide +kernel
  have op3731_8 : pairBatch 3731 8 2 = true := by decide +kernel
  have op3731_10 : pairBatch 3731 10 2 = true := by decide +kernel
  have op3731_12 : pairBatch 3731 12 2 = true := by decide +kernel
  have op3731_14 : pairBatch 3731 14 2 = true := by decide +kernel
  have op3731_16 : pairBatch 3731 16 2 = true := by decide +kernel
  have op3731_18 : pairBatch 3731 18 2 = true := by decide +kernel
  have op3731_20 : pairBatch 3731 20 2 = true := by decide +kernel
  have op3731_22 : pairBatch 3731 22 2 = true := by decide +kernel
  have op3731_24 : pairBatch 3731 24 2 = true := by decide +kernel
  have op3731_26 : pairBatch 3731 26 2 = true := by decide +kernel
  have v3731 : batch 3731 1 = true := @oneFromPairs 3731 (by decide +kernel) (@fromPairs 3731 (by decide +kernel) (by decide +kernel) (@joinPair 3731 0 2 op3731_0 (@joinPair 3731 2 2 op3731_2 (@joinPair 3731 4 2 op3731_4 (@joinPair 3731 6 2 op3731_6 (@joinPair 3731 8 2 op3731_8 (@joinPair 3731 10 2 op3731_10 (@joinPair 3731 12 2 op3731_12 (@joinPair 3731 14 2 op3731_14 (@joinPair 3731 16 2 op3731_16 (@joinPair 3731 18 2 op3731_18 (@joinPair 3731 20 2 op3731_20 (@joinPair 3731 22 2 op3731_22 (@joinPair 3731 24 2 op3731_24 (@joinPair 3731 26 2 op3731_26 (by decide +kernel))))))))))))))))
  have b3728 : batch 3728 4 = true := (joinBatch v3728 (joinBatch v3729 (joinBatch v3730 v3731)))
  have b3732 : batch 3732 4 = true := by decide +kernel
  have b3736 : batch 3736 4 = true := by decide +kernel
  have b3740 : batch 3740 4 = true := by decide +kernel
  exact (@stitch 3648 4 b3648 (@stitch 3652 4 b3652 (@stitch 3656 4 b3656 (@stitch 3660 4 b3660 (@stitch 3664 4 b3664 (@stitch 3668 4 b3668 (@stitch 3672 4 b3672 (@stitch 3676 4 b3676 (@stitch 3680 4 b3680 (@stitch 3684 4 b3684 (@stitch 3688 4 b3688 (@stitch 3692 4 b3692 (@stitch 3696 4 b3696 (@stitch 3700 4 b3700 (@stitch 3704 4 b3704 (@stitch 3708 4 b3708 (@stitch 3712 4 b3712 (@stitch 3716 4 b3716 (@stitch 3720 4 b3720 (@stitch 3724 4 b3724 (@stitch 3728 4 b3728 (@stitch 3732 4 b3732 (@stitch 3736 4 b3736 (@stitch 3740 4 b3740 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3744 (tail : remaining 3840 = true) : remaining 3744 = true := by
  have b3744 : batch 3744 4 = true := by decide +kernel
  have b3748 : batch 3748 4 = true := by decide +kernel
  have b3752 : batch 3752 4 = true := by decide +kernel
  have b3756 : batch 3756 4 = true := by decide +kernel
  have b3760 : batch 3760 4 = true := by decide +kernel
  have b3764 : batch 3764 4 = true := by decide +kernel
  have b3768 : batch 3768 4 = true := by decide +kernel
  have b3772 : batch 3772 4 = true := by decide +kernel
  have b3776 : batch 3776 4 = true := by decide +kernel
  have b3780 : batch 3780 4 = true := by decide +kernel
  have b3784 : batch 3784 4 = true := by decide +kernel
  have b3788 : batch 3788 4 = true := by decide +kernel
  have b3792 : batch 3792 4 = true := by decide +kernel
  have b3796 : batch 3796 4 = true := by decide +kernel
  have b3800 : batch 3800 4 = true := by decide +kernel
  have b3804 : batch 3804 4 = true := by decide +kernel
  have b3808 : batch 3808 4 = true := by decide +kernel
  have b3812 : batch 3812 4 = true := by decide +kernel
  have b3816 : batch 3816 4 = true := by decide +kernel
  have b3820 : batch 3820 4 = true := by decide +kernel
  have b3824 : batch 3824 4 = true := by decide +kernel
  have b3828 : batch 3828 4 = true := by decide +kernel
  have b3832 : batch 3832 4 = true := by decide +kernel
  have b3836 : batch 3836 4 = true := by decide +kernel
  exact (@stitch 3744 4 b3744 (@stitch 3748 4 b3748 (@stitch 3752 4 b3752 (@stitch 3756 4 b3756 (@stitch 3760 4 b3760 (@stitch 3764 4 b3764 (@stitch 3768 4 b3768 (@stitch 3772 4 b3772 (@stitch 3776 4 b3776 (@stitch 3780 4 b3780 (@stitch 3784 4 b3784 (@stitch 3788 4 b3788 (@stitch 3792 4 b3792 (@stitch 3796 4 b3796 (@stitch 3800 4 b3800 (@stitch 3804 4 b3804 (@stitch 3808 4 b3808 (@stitch 3812 4 b3812 (@stitch 3816 4 b3816 (@stitch 3820 4 b3820 (@stitch 3824 4 b3824 (@stitch 3828 4 b3828 (@stitch 3832 4 b3832 (@stitch 3836 4 b3836 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3840 (tail : remaining 3936 = true) : remaining 3840 = true := by
  have b3840 : batch 3840 4 = true := by decide +kernel
  have b3844 : batch 3844 4 = true := by decide +kernel
  have b3848 : batch 3848 4 = true := by decide +kernel
  have b3852 : batch 3852 4 = true := by decide +kernel
  have b3856 : batch 3856 4 = true := by decide +kernel
  have b3860 : batch 3860 4 = true := by decide +kernel
  have b3864 : batch 3864 4 = true := by decide +kernel
  have b3868 : batch 3868 4 = true := by decide +kernel
  have b3872 : batch 3872 4 = true := by decide +kernel
  have b3876 : batch 3876 4 = true := by decide +kernel
  have b3880 : batch 3880 4 = true := by decide +kernel
  have b3884 : batch 3884 4 = true := by decide +kernel
  have b3888 : batch 3888 4 = true := by decide +kernel
  have b3892 : batch 3892 4 = true := by decide +kernel
  have b3896 : batch 3896 4 = true := by decide +kernel
  have b3900 : batch 3900 4 = true := by decide +kernel
  have b3904 : batch 3904 4 = true := by decide +kernel
  have b3908 : batch 3908 4 = true := by decide +kernel
  have b3912 : batch 3912 4 = true := by decide +kernel
  have b3916 : batch 3916 4 = true := by decide +kernel
  have b3920 : batch 3920 4 = true := by decide +kernel
  have b3924 : batch 3924 4 = true := by decide +kernel
  have b3928 : batch 3928 4 = true := by decide +kernel
  have b3932 : batch 3932 4 = true := by decide +kernel
  exact (@stitch 3840 4 b3840 (@stitch 3844 4 b3844 (@stitch 3848 4 b3848 (@stitch 3852 4 b3852 (@stitch 3856 4 b3856 (@stitch 3860 4 b3860 (@stitch 3864 4 b3864 (@stitch 3868 4 b3868 (@stitch 3872 4 b3872 (@stitch 3876 4 b3876 (@stitch 3880 4 b3880 (@stitch 3884 4 b3884 (@stitch 3888 4 b3888 (@stitch 3892 4 b3892 (@stitch 3896 4 b3896 (@stitch 3900 4 b3900 (@stitch 3904 4 b3904 (@stitch 3908 4 b3908 (@stitch 3912 4 b3912 (@stitch 3916 4 b3916 (@stitch 3920 4 b3920 (@stitch 3924 4 b3924 (@stitch 3928 4 b3928 (@stitch 3932 4 b3932 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock3936 (tail : remaining 4032 = true) : remaining 3936 = true := by
  have b3936 : batch 3936 4 = true := by decide +kernel
  have b3940 : batch 3940 4 = true := by decide +kernel
  have b3944 : batch 3944 4 = true := by decide +kernel
  have b3948 : batch 3948 4 = true := by decide +kernel
  have b3952 : batch 3952 4 = true := by decide +kernel
  have b3956 : batch 3956 4 = true := by decide +kernel
  have b3960 : batch 3960 4 = true := by decide +kernel
  have b3964 : batch 3964 4 = true := by decide +kernel
  have b3968 : batch 3968 4 = true := by decide +kernel
  have b3972 : batch 3972 4 = true := by decide +kernel
  have b3976 : batch 3976 4 = true := by decide +kernel
  have b3980 : batch 3980 4 = true := by decide +kernel
  have b3984 : batch 3984 4 = true := by decide +kernel
  have b3988 : batch 3988 4 = true := by decide +kernel
  have b3992 : batch 3992 4 = true := by decide +kernel
  have b3996 : batch 3996 4 = true := by decide +kernel
  have b4000 : batch 4000 4 = true := by decide +kernel
  have b4004 : batch 4004 4 = true := by decide +kernel
  have b4008 : batch 4008 4 = true := by decide +kernel
  have b4012 : batch 4012 4 = true := by decide +kernel
  have b4016 : batch 4016 4 = true := by decide +kernel
  have b4020 : batch 4020 4 = true := by decide +kernel
  have b4024 : batch 4024 4 = true := by decide +kernel
  have b4028 : batch 4028 4 = true := by decide +kernel
  exact (@stitch 3936 4 b3936 (@stitch 3940 4 b3940 (@stitch 3944 4 b3944 (@stitch 3948 4 b3948 (@stitch 3952 4 b3952 (@stitch 3956 4 b3956 (@stitch 3960 4 b3960 (@stitch 3964 4 b3964 (@stitch 3968 4 b3968 (@stitch 3972 4 b3972 (@stitch 3976 4 b3976 (@stitch 3980 4 b3980 (@stitch 3984 4 b3984 (@stitch 3988 4 b3988 (@stitch 3992 4 b3992 (@stitch 3996 4 b3996 (@stitch 4000 4 b4000 (@stitch 4004 4 b4004 (@stitch 4008 4 b4008 (@stitch 4012 4 b4012 (@stitch 4016 4 b4016 (@stitch 4020 4 b4020 (@stitch 4024 4 b4024 (@stitch 4028 4 b4028 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem verifiedBlock4032 (tail : remaining 4125 = true) : remaining 4032 = true := by
  have b4032 : batch 4032 4 = true := by decide +kernel
  have b4036 : batch 4036 4 = true := by decide +kernel
  have b4040 : batch 4040 4 = true := by decide +kernel
  have b4044 : batch 4044 4 = true := by decide +kernel
  have b4048 : batch 4048 4 = true := by decide +kernel
  have b4052 : batch 4052 4 = true := by decide +kernel
  have b4056 : batch 4056 4 = true := by decide +kernel
  have b4060 : batch 4060 4 = true := by decide +kernel
  have b4064 : batch 4064 4 = true := by decide +kernel
  have b4068 : batch 4068 4 = true := by decide +kernel
  have b4072 : batch 4072 4 = true := by decide +kernel
  have b4076 : batch 4076 4 = true := by decide +kernel
  have b4080 : batch 4080 4 = true := by decide +kernel
  have b4084 : batch 4084 4 = true := by decide +kernel
  have b4088 : batch 4088 4 = true := by decide +kernel
  have b4092 : batch 4092 4 = true := by decide +kernel
  have b4096 : batch 4096 4 = true := by decide +kernel
  have b4100 : batch 4100 4 = true := by decide +kernel
  have b4104 : batch 4104 4 = true := by decide +kernel
  have b4108 : batch 4108 4 = true := by decide +kernel
  have b4112 : batch 4112 4 = true := by decide +kernel
  have b4116 : batch 4116 4 = true := by decide +kernel
  have b4120 : batch 4120 4 = true := by decide +kernel
  have b4124 : batch 4124 1 = true := by decide +kernel
  exact (@stitch 4032 4 b4032 (@stitch 4036 4 b4036 (@stitch 4040 4 b4040 (@stitch 4044 4 b4044 (@stitch 4048 4 b4048 (@stitch 4052 4 b4052 (@stitch 4056 4 b4056 (@stitch 4060 4 b4060 (@stitch 4064 4 b4064 (@stitch 4068 4 b4068 (@stitch 4072 4 b4072 (@stitch 4076 4 b4076 (@stitch 4080 4 b4080 (@stitch 4084 4 b4084 (@stitch 4088 4 b4088 (@stitch 4092 4 b4092 (@stitch 4096 4 b4096 (@stitch 4100 4 b4100 (@stitch 4104 4 b4104 (@stitch 4108 4 b4108 (@stitch 4112 4 b4112 (@stitch 4116 4 b4116 (@stitch 4120 4 b4120 (@stitch 4124 1 b4124 tail))))))))))))))))))))))))
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem spanFrom0 : remaining 0 = true := (verifiedBlock0 (verifiedBlock96 (verifiedBlock192 (verifiedBlock288 (verifiedBlock384 (verifiedBlock480 (verifiedBlock576 (verifiedBlock672 (verifiedBlock768 (verifiedBlock864 (verifiedBlock960 (verifiedBlock1056 (verifiedBlock1152 (verifiedBlock1248 (verifiedBlock1344 (verifiedBlock1440 (verifiedBlock1536 (verifiedBlock1632 (verifiedBlock1728 (verifiedBlock1824 (verifiedBlock1920 (verifiedBlock2016 (verifiedBlock2112 (verifiedBlock2208 (verifiedBlock2304 (verifiedBlock2400 (verifiedBlock2496 (verifiedBlock2592 (verifiedBlock2688 (verifiedBlock2784 (verifiedBlock2880 (verifiedBlock2976 (verifiedBlock3072 (verifiedBlock3168 (verifiedBlock3264 (verifiedBlock3360 (verifiedBlock3456 (verifiedBlock3552 (verifiedBlock3648 (verifiedBlock3744 (verifiedBlock3840 (verifiedBlock3936 (verifiedBlock4032 (by decide +kernel : remaining 4125 = true))))))))))))))))))))))))))))))))))))))))))))
end PEqualNP.Outside.L_meta_30815_aux.Signed.Tokens

theorem PEqualNP.Outside.L_meta_30815 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := PEqualNP.Outside.L_meta_30815_aux.finalReduction PEqualNP.Outside.L_meta_30815_aux.Signed.Tokens.spanFrom0
