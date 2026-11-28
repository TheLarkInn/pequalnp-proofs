import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1168

abbrev W (r : Nat) := Fin r → Fin 16
abbrev K (r : Nat) := Finset (Fin r)
abbrev F := ZMod 11

def sign (a x : Fin 16) : F :=
  if ((![0,43690,52428,26214,61680,23130,15420,38550,
    65280,21930,13260,39270,4080,42330,49980,27030] : Fin 16 → Nat) a).testBit x.val then -1 else 1

def localPass (b : Bool) (z x : Fin 16) : Bool :=
  let w := z.val ^^^ x.val
  (w &&& 3) != 0 && (w &&& 13) != (if b then 1 else 0)

def eig (b : Bool) (a : Fin 16) : F :=
  if b then (![10,9,7,7,9,2,0,0,9,2,0,0,9,2,0,0] : Fin 16 → F) a
  else (![0,6,8,8,10,10,1,1,10,10,1,1,10,10,1,1] : Fin 16 → F) a

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
lemma orth1 (a x : Fin 16) :
    ∑ z : Fin 16, sign a z * sign z x = if a = x then 16 else 0 := by
  decide +revert

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
lemma trans1 (b : Bool) (a x : Fin 16) :
    ∑ z : Fin 16, sign a z * (if localPass b z x then 1 else 0) = eig b a * sign a x := by
  decide +revert

def charW {r : Nat} (a x : W r) : F := ∏ j, sign (a j) (x j)
def tr {r : Nat} (d : W r → F) (a : W r) : F := ∑ x, charW a x * d x

noncomputable def passW {r : Nat} (e : K r) (z x : W r) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all fun j => localPass (decide (j ∈ e)) (z j) (x j)

noncomputable def rowW {r : Nat} (e : K r) (d : W r → F) (z : W r) : F :=
  ∑ x, (if passW e z x then 1 else 0) * d x

def eigW {r : Nat} (e : K r) (a : W r) : F := ∏ j, eig (decide (j ∈ e)) (a j)

lemma tensorSum {r : Nat} (f : Fin r → Fin 16 → F) :
    (∑ x : W r, ∏ i, f i (x i)) = ∏ i, ∑ z, f i z := by
  exact (Fintype.prod_sum f).symm

lemma orthW {r : Nat} (a x : W r) :
    ∑ z : W r, charW a z * charW z x = if a = x then 16 ^ r else 0 := by
  classical
  simp only [charW, ← Finset.prod_mul_distrib]
  rw [tensorSum (fun i z => sign (a i) z * sign z (x i))]
  simp only [orth1]
  split_ifs with h
  · subst x; simp
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ x i := not_forall.mp (fun hax => h (funext hax))
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma tr_comp {r : Nat} (k : W r → W r → F) (d : W r → F) (a : W r) :
    tr (fun z => ∑ x, k z x * d x) a = ∑ x, (∑ z, charW a z * k z x) * d x := by
  simp only [tr, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

lemma tr_twice {r : Nat} (d : W r → F) (a : W r) :
    tr (tr d) a = (16 : F)^r * d a := by
  classical
  change tr (fun z => ∑ x, charW z x * d x) a = _
  rw [tr_comp]
  simp [orthW, ite_mul]

lemma tr_inj {r : Nat} : Function.Injective (@tr r) := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro d d' h
  funext a
  have hh := congrArg (fun v => tr v a) h
  simp only [tr_twice] at hh
  exact mul_left_cancel₀ (pow_ne_zero _ (by decide : (16 : F) ≠ 0)) hh

noncomputable def trEquiv (r : Nat) : (W r → F) ≃ (W r → F) :=
  Equiv.ofBijective tr ((Finite.injective_iff_bijective).mp tr_inj)

lemma passW_prod {r : Nat} (e : K r) (z x : W r) :
    (if passW e z x then (1 : F) else 0) =
      ∏ j, if localPass (decide (j ∈ e)) (z j) (x j) then 1 else 0 := by
  classical
  by_cases h : ∀ j, localPass (decide (j ∈ e)) (z j) (x j) = true
  · simp [passW, List.all_eq_true, h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hp : passW e z x = false := by simpa [passW, List.all_eq_true] using h
    rw [hp, if_neg (by decide : ¬ false = true)]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma transW {r : Nat} (e : K r) (a x : W r) :
    ∑ z : W r, charW a z * (if passW e z x then 1 else 0) = eigW e a * charW a x := by
  simp only [passW_prod, charW, eigW, ← Finset.prod_mul_distrib]
  rw [tensorSum (fun i z => sign (a i) z * (if localPass (decide (i ∈ e)) z (x i) then 1 else 0))]
  simp only [trans1]

lemma tr_row {r : Nat} (e : K r) (d : W r → F) (a : W r) :
    tr (rowW e d) a = eigW e a * tr d a := by
  unfold rowW
  rw [tr_comp]
  simp only [transW, tr, Finset.mul_sum, mul_assoc]

lemma rowW_eq_zero {r : Nat} (e : K r) (d : W r → F) :
    (∀ z, rowW e d z = 0) ↔ ∀ a, eigW e a * tr d a = 0 := by
  constructor
  · intro h a
    rw [← tr_row]
    simp [tr, h]
  · intro h
    have hh : tr (rowW e d) = tr 0 := by
      funext a
      rw [tr_row, h]
      simp [tr]
    exact fun z => congrFun (tr_inj hh) z

def lost {r : Nat} (M : Finset (K r)) : Finset (W r) :=
  Finset.univ.filter fun a => ∀ e ∈ M, eigW e a = 0

abbrev readings {r : Nat} (d : W r → Fin 11) (q : K r × W r) : Prop :=
  (((Finset.univ : Finset (W r)).filter fun x => passW q.1 q.2 x).sum fun x => (d x).val) % 11 = 0

noncomputable def ker {r : Nat} (M : Finset (K r)) : Nat :=
  ((Finset.univ : Finset (W r → Fin 11)).filter fun d => ∀ q ∈ M.product Finset.univ, readings d q).card

def asF (x : Fin 11) : F := x

lemma asF_cast (x : Fin 11) : (x.val : F) = asF x := by decide +revert

lemma readings_iff {r : Nat} (d : W r → Fin 11) (e : K r) (z : W r) :
    readings d (e,z) ↔ rowW e (fun x => asF (d x)) z = 0 := by
  unfold readings rowW
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
  simp [Finset.sum_filter, asF_cast, ite_mul]

lemma spectral_iff {r : Nat} (M : Finset (K r)) (d : W r → Fin 11) :
    (∀ q ∈ M.product Finset.univ, readings d q) ↔
      ∀ a, a ∉ lost M → tr (fun x => asF (d x)) a = 0 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  simp only [Prod.forall, readings_iff]
  constructor
  · intro h a ha
    obtain ⟨e, he, hn⟩ : ∃ e ∈ M, eigW e a ≠ 0 := by simpa [lost] using ha
    exact (mul_eq_zero.mp ((rowW_eq_zero e d).mp (fun z => h e z (Finset.mem_product.mpr ⟨he, Finset.mem_univ _⟩)) a)).resolve_left hn
  · intro h e z he
    apply (rowW_eq_zero e d).mpr _ z
    intro a
    by_cases hz : eigW e a = 0
    · simp [hz]
    · have ha : a ∉ lost M := by simpa [lost] using (show ∃ e ∈ M, eigW e a ≠ 0 from ⟨e,(Finset.mem_product.mp he).1,hz⟩)
      exact mul_eq_zero.mpr (Or.inr (h a ha))

noncomputable def kerEquiv {r : Nat} (M : Finset (K r)) :
    {d : W r → Fin 11 // ∀ q ∈ M.product Finset.univ, readings d q} ≃ (lost M → F) := by
  classical
  let E := trEquiv r
  let extend (v : lost M → F) (a : W r) : F := if h : a ∈ lost M then v ⟨a,h⟩ else 0
  refine ⟨fun d a => tr d.val a.val, fun v => ⟨E.symm (extend v), ?_⟩, ?_, ?_⟩
  · apply (spectral_iff _ _).mpr
    intro a ha
    change E (E.symm (extend v)) a = 0
    simp [extend, ha]
  · intro d
    apply Subtype.ext
    apply E.injective
    change E (E.symm _) = tr d.val
    rw [E.apply_symm_apply]
    funext a
    by_cases ha : a ∈ lost M
    · simp [extend, ha]
    · simp only [extend, dif_neg ha]
      exact ((spectral_iff _ _).mp d.property a ha).symm
  · intro v
    funext a
    change E (E.symm (extend v)) a.val = _
    simp [extend]

lemma ker_eq_pow {r : Nat} (M : Finset (K r)) : ker M = 11 ^ (lost M).card := by
  classical
  have h := Fintype.card_congr (kerEquiv M)
  simpa [ker, Fintype.card_subtype, Fintype.card_fun, F] using h


def axis (a : Fin 16) : Fin 3 :=
  (![0,2,2,2,2,2,1,1,2,2,1,1,2,2,1,1] : Fin 16 → Fin 3) a

def botW {r : Nat} (a : W r) : K r := Finset.univ.filter fun i => axis (a i) = 1
def topW {r : Nat} (a : W r) : K r := Finset.univ.filter fun i => axis (a i) ≠ 0

def orig {r : Nat} (U : Finset (K r)) : Finset (K r) := U.image fun S => Sᶜ

lemma mem_orig {r : Nat} (U : Finset (K r)) (e : K r) : e ∈ orig U ↔ eᶜ ∈ U := by
  constructor
  · rintro he
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp he
    simpa using hS
  · intro h
    exact Finset.mem_image.mpr ⟨eᶜ, h, compl_compl _⟩

lemma orig_inv {r : Nat} (U : Finset (K r)) : orig (orig U) = U := by
  ext e
  simp [mem_orig]

lemma card_orig {r : Nat} (U : Finset (K r)) : (orig U).card = U.card := by
  exact Finset.card_image_of_injective _ compl_injective

lemma local_eig_iff (b : Bool) (a : Fin 16) : eig b a ≠ 0 ↔
    (axis a = 1 → b = false) ∧ (b = false → axis a ≠ 0) := by decide +revert

lemma bot_le_top {r : Nat} (a : W r) : botW a ⊆ topW a := by
  intro i hi
  simp only [botW, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp [topW, hi]

lemma eigW_nz {r : Nat} (a : W r) (S : K r) :
    eigW Sᶜ a ≠ 0 ↔ botW a ⊆ S ∧ S ⊆ topW a := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  simp only [eigW, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies, local_eig_iff,
    decide_eq_false_iff_not, Finset.mem_compl, not_not, Finset.subset_iff, botW, topW,
    Finset.mem_filter, true_and, forall_and]

abbrev covered {r : Nat} (U : Finset (K r)) (B T : K r) := ∀ S, B ⊆ S → S ⊆ T → S ∈ U

lemma lost_iff_cov {r : Nat} (U : Finset (K r)) (a : W r) :
    a ∈ lost (Finset.univ \ orig U) ↔ covered U (botW a) (topW a) := by
  simp only [lost, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, mem_orig]
  constructor
  · intro h S hb ht
    by_contra hn
    exact (eigW_nz a S).mpr ⟨hb,ht⟩ (h Sᶜ (by simpa using hn))
  · intro h e he
    by_contra hn
    apply he
    apply h
    · exact ((eigW_nz a eᶜ).mp (by simpa using hn)).1
    · exact ((eigW_nz a eᶜ).mp (by simpa using hn)).2

def wordFiber {r : Nat} (B T : K r) :=
  (Finset.univ : Finset (W r)).filter fun a => botW a = B ∧ topW a = T

def choices (b t : Bool) := (Finset.univ : Finset (Fin 16)).filter fun k =>
  (axis k = 1 ↔ b = true) ∧ (axis k ≠ 0 ↔ t = true)

lemma choices_card (b t : Bool) : (choices b t).card =
    if b then (if t then 6 else 0) else (if t then 9 else 1) := by decide +revert

lemma wordFiber_eq {r : Nat} (B T : K r) : wordFiber B T =
    Fintype.piFinset (fun i => choices (decide (i ∈ B)) (decide (i ∈ T))) := by
  ext a
  simp only [wordFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.ext_iff,
    Fintype.mem_piFinset, choices, decide_eq_true_eq, botW, topW, forall_and]

lemma wordFiber_card {r : Nat} {B T : K r} (h : B ⊆ T) :
    (wordFiber B T).card = 6 ^ B.card * 9 ^ (T.card - B.card) := by
  rw [wordFiber_eq, Fintype.card_piFinset]
  have hh (i : Fin r) : (choices (decide (i ∈ B)) (decide (i ∈ T))).card =
      (if i ∈ B then 6 else 1) * (if i ∈ T \ B then 9 else 1) := by
    by_cases hb : i ∈ B
    · simp [choices_card, hb, h hb]
    · by_cases ht : i ∈ T <;> simp [choices_card, hb, ht]
  simp only [hh, Finset.prod_mul_distrib]
  simp [Finset.prod_ite]
  have he : Finset.univ.filter (fun x => x ∈ T ∧ x ∉ B) = T \ B := by ext; simp
  rw [he,Finset.card_sdiff_of_subset h]

def layer {r : Nat} (U : Finset (K r)) (T : K r) : Nat :=
  ∑ B ∈ T.powerset, if covered U B T then 6^B.card * 9^(T.card - B.card) else 0

def loss {r : Nat} (U : Finset (K r)) := ∑ T ∈ U, layer U T

lemma lost_count {r : Nat} (U : Finset (K r)) : (lost (Finset.univ \ orig U)).card = loss U := by
  classical
  let L := lost (Finset.univ \ orig U)
  have ht : ∀ a ∈ L, topW a ∈ U := fun a ha => (lost_iff_cov U a).mp ha _ (bot_le_top a) (by rfl)
  change L.card = _
  rw [Finset.card_eq_sum_card_fiberwise (f := topW) ht]
  unfold loss
  apply Finset.sum_congr rfl
  intro T hT
  let L' := L.filter fun a => topW a = T
  have hb : ∀ a ∈ L', botW a ∈ T.powerset := by
    intro a ha
    exact Finset.mem_powerset.mpr ((Finset.mem_filter.mp ha).2 ▸ bot_le_top a)
  change L'.card = _
  rw [Finset.card_eq_sum_card_fiberwise (f := botW) hb]
  unfold layer
  apply Finset.sum_congr rfl
  intro B hB
  have iffmem (a : W r) : (a ∈ (L'.filter fun u => botW u = B)) ↔
      (botW a = B ∧ topW a = T) ∧ covered U B T := by
    simp only [L', L, Finset.mem_filter, lost_iff_cov]
    constructor
    · rintro ⟨⟨hc, ht'⟩, hb'⟩
      exact ⟨⟨hb', ht'⟩, hb' ▸ ht' ▸ hc⟩
    · rintro ⟨⟨hb', ht'⟩, hc⟩
      exact ⟨⟨hb' ▸ ht' ▸ hc, ht'⟩, hb'⟩
  by_cases hc : covered U B T
  · rw [if_pos hc, ← wordFiber_card (Finset.mem_powerset.mp hB)]
    congr 1
    ext a
    rw [iffmem]
    simp only [wordFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_left hc
  · rw [if_neg hc, Finset.card_eq_zero]
    exact Finset.eq_empty_iff_forall_notMem.mpr fun a ha => hc ((iffmem a).mp ha).2

lemma cov_self {r : Nat} (U : Finset (K r)) (T : K r) : covered U T T ↔ T ∈ U := by
  constructor
  · intro h; exact h T (by rfl) (by rfl)
  · intro h S h₁ h₂; exact Finset.Subset.antisymm h₂ h₁ ▸ h

lemma cov_step {r : Nat} (U : Finset (K r)) (B : K r) (i : Fin r) :
    covered U B (insert i B) ↔ B ∈ U ∧ insert i B ∈ U := by
  constructor
  · intro h
    exact ⟨h B (by rfl) (Finset.subset_insert ..), h _ (Finset.subset_insert ..) (by rfl)⟩
  · rintro ⟨hb, ht⟩ S hbs hst
    by_cases hi : i ∈ S
    · exact Finset.Subset.antisymm hst (Finset.insert_subset hi hbs) ▸ ht
    · have hsb : S ⊆ B := fun x hx => (Finset.mem_insert.mp (hst hx)).resolve_left (fun h => hi (h ▸ hx))
      exact Finset.Subset.antisymm hsb hbs ▸ hb

lemma layer_private {r : Nat} (U : Finset (K r)) {T : K r} (h : T ∈ U) : 6^T.card ≤ layer U T := by
  unfold layer
  apply le_trans _ (Finset.single_le_sum (f := fun B : K r => if covered U B T then 6^B.card * 9^(T.card - B.card) else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_powerset.mpr (Finset.Subset.refl T)))
  simp [cov_self, h]

lemma layer_empty {r : Nat} (U : Finset (K r)) (h : ∅ ∈ U) : layer U ∅ = 1 := by
  simp [layer, cov_self, h]

lemma layer_single {r : Nat} (U : Finset (K r)) (i : Fin r) (h : {i} ∈ U) :
    layer U {i} = 6 + (if ∅ ∈ U then 9 else 0) := by
  have hcov : covered U ∅ {i} ↔ ∅ ∈ U := (cov_step U ∅ i).trans (and_iff_left h)
  have hp : ({i} : K r).powerset = {∅,{i}} := by ext S; simp [Finset.subset_singleton_iff]
  simp [layer, hp, hcov, cov_self, h, add_comm]

lemma layer_pair_ge {r : Nat} (U : Finset (K r)) (i j : Fin r) (hij : i ≠ j) (h : {i,j} ∈ U) :
    36 + (if {i} ∈ U then 54 else 0) + (if {j} ∈ U then 54 else 0) ≤ layer U {i,j} := by
  let P : Finset (K r) := {{i,j}, {i}, {j}}
  have hP : P ⊆ ({i,j} : K r).powerset := by simp [P,Finset.insert_subset_iff]
  have hi : covered U {i} {i,j} ↔ {i} ∈ U := by
    rw [Finset.pair_comm, cov_step]; simp [Finset.pair_comm j i, h]
  have hj : covered U {j} {i,j} ↔ {j} ∈ U := (cov_step U {j} i).trans (and_iff_left h)
  have h0 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun B : K r => if covered U B {i,j}
    then 6^B.card * 9^(({i,j} : K r).card - B.card) else 0) hP (fun _ _ _ => Nat.zero_le _)
  have h₁ : ({i,j} : K r) ≠ {i} := by intro hh; have := congrArg Finset.card hh; simp [hij] at this
  have h₂ : ({i,j} : K r) ≠ {j} := by intro hh; have := congrArg Finset.card hh; simp [hij] at this
  simpa [P, layer, h₁, h₂, hij, cov_self, h, hi, hj, Nat.add_assoc] using h0

def units {r : Nat} (U : Finset (K r)) : K r := Finset.univ.filter fun i => {i} ∈ U
def rest {r : Nat} (U : Finset (K r)) := U.filter fun T => 2 ≤ T.card

def csize {r : Nat} (U : Finset (K r)) : Nat := if ∅ ∈ U then 1 else 0
def uprice {r : Nat} (U : Finset (K r)) : Nat := if ∅ ∈ U then 15 else 6

lemma decomp {r : Nat} (U : Finset (K r)) : U =
    ((if ∅ ∈ U then {∅} else ∅) ∪ ((units U).image fun i => {i})) ∪ rest U := by
  ext T
  simp only [Finset.mem_union, Finset.mem_image, units, Finset.mem_filter, Finset.mem_univ, true_and, rest]
  by_cases h0 : T = ∅
  · subst T; by_cases h : ∅ ∈ U <;> simp [h]
  · by_cases h1 : T.card = 1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h1
      by_cases h : ∅ ∈ U <;> simp [h]
    · have h2 : 2 ≤ T.card := by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0); omega
      have hh : ¬∃ i : Fin r, {i} ∈ U ∧ {i} = T := by rintro ⟨i,_,rfl⟩; simp at h1
      by_cases h : ∅ ∈ U <;> simp [h, h0, h2, hh]

lemma decomp_sum {r : Nat} (U : Finset (K r)) (f : K r → Nat) :
    ∑ T ∈ U, f T = (if ∅ ∈ U then f ∅ else 0) + (∑ i ∈ units U, f {i}) + ∑ T ∈ rest U, f T := by
  have h0 : Disjoint (if ∅ ∈ U then ({∅} : Finset (K r)) else ∅) ((units U).image fun i => {i}) := by
    by_cases h : ∅ ∈ U <;> simp [h, Finset.disjoint_left]
  have h1 : Disjoint ((if ∅ ∈ U then ({∅} : Finset (K r)) else ∅) ∪ ((units U).image fun i => {i})) (rest U) := by
    rw [Finset.disjoint_left]
    intro T hT hR
    have h2 := (Finset.mem_filter.mp hR).2
    rcases Finset.mem_union.mp hT with h | h
    · by_cases hc : ∅ ∈ U <;> simp [hc] at h
      subst T; simp at h2
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      simp at h2
  calc
    _ = ∑ T ∈ ((if ∅ ∈ U then {∅} else ∅) ∪ ((units U).image fun i => {i})) ∪ rest U, f T := by rw [← decomp]
    _ = _ := by
      rw [Finset.sum_union h1, Finset.sum_union h0, Finset.sum_image (fun _ _ _ _ h => Finset.singleton_injective h)]
      by_cases h : ∅ ∈ U <;> simp [h]

lemma size_split {r : Nat} (U : Finset (K r)) : U.card = csize U + (units U).card + (rest U).card := by
  simpa [csize] using decomp_sum U (fun _ => 1)

lemma loss_split {r : Nat} (U : Finset (K r)) : loss U =
    csize U + (units U).card * uprice U + ∑ T ∈ rest U, layer U T := by
  rw [loss, decomp_sum]
  have hs : ∀ i ∈ units U, layer U {i} = uprice U := by
    intro i hi
    rw [layer_single _ _ (Finset.mem_filter.mp hi).2]
    by_cases h : ∅ ∈ U <;> simp [uprice,h]
  rw [Finset.sum_congr rfl hs]
  by_cases h : ∅ ∈ U <;> simp [h, csize, layer_empty]

lemma rest_private {r : Nat} (U : Finset (K r)) {T : K r} (hT : T ∈ rest U) : 36 ≤ layer U T := by
  have h := Finset.mem_filter.mp hT
  exact (Nat.pow_le_pow_right (by decide : 0 < 6) h.2).trans (layer_private _ h.1)

lemma big_price {r : Nat} (U : Finset (K r)) {X : K r} (hX : X ∈ rest U) (h3 : 3 ≤ X.card) :
    216 + 36 * ((rest U).card - 1) ≤ ∑ T ∈ rest U, layer U T := by
  have h216 : 216 ≤ layer U X := (Nat.pow_le_pow_right (by decide : 0 < 6) h3).trans
    (layer_private _ (Finset.mem_filter.mp hX).1)
  have h36 := Finset.sum_le_sum (s := (rest U).erase X) (f := fun _ => 36) (g := fun T => layer U T)
    (fun _ ht => rest_private _ (Finset.mem_of_mem_erase ht))
  rw [← Finset.add_sum_erase (rest U) (layer U) hX]
  simp [Finset.card_erase_of_mem hX, Nat.mul_comm] at h36
  omega

lemma small_price {r : Nat} (U : Finset (K r)) (hsmall : ∀ T ∈ rest U, T.card = 2) :
    let t := (units U)ᶜ.card
    let d := (rest U).card
    (36 * d + 54 * (d - t.choose 2) ≤ ∑ T ∈ rest U, layer U T) ∧
      (t = 0 → 144 * d ≤ ∑ T ∈ rest U, layer U T) := by
  classical
  let G := (rest U).filter fun T => T ⊆ (units U)ᶜ
  let D := rest U \ G
  have hg : G ⊆ rest U := Finset.filter_subset _ _
  have hcg : G.card ≤ (units U)ᶜ.card.choose 2 := by
    rw [← Finset.card_powersetCard]
    apply Finset.card_le_card
    intro T ht
    have h := Finset.mem_filter.mp ht
    exact Finset.mem_powersetCard.mpr ⟨h.2, hsmall T h.1⟩
  have hcd : D.card = (rest U).card - G.card := Finset.card_sdiff_of_subset hg
  have hsum := Finset.sum_sdiff hg (f := layer U)
  have hG := Finset.sum_le_sum (s := G) (f := fun _ => 36) (g := layer U) (fun _ h => rest_private U (hg h))
  have hD := Finset.sum_le_sum (s := D) (f := fun _ => 90) (g := layer U) (by
    intro T h
    obtain ⟨hr, hn⟩ := Finset.mem_sdiff.mp h
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (hsmall T hr)
    have hp := layer_pair_ge U i j hij (Finset.mem_filter.mp hr).1
    by_cases hi : {i} ∈ U <;> by_cases hj : {j} ∈ U <;> simp [hi,hj] at hp
    all_goals first | omega | (exfalso; apply hn; simp [G,hr,units,hi,hj,Finset.insert_subset_iff]))
  constructor
  · change (∑ T ∈ D, layer U T) + ∑ T ∈ G, layer U T = _ at hsum
    have hg36 : 36 * G.card ≤ ∑ T ∈ G, layer U T := by simpa [Nat.mul_comm] using hG
    have hd90 : 90 * D.card ≤ ∑ T ∈ D, layer U T := by simpa [Nat.mul_comm] using hD
    have hadd : D.card + G.card = (rest U).card := by rw [hcd,Nat.sub_add_cancel (Finset.card_le_card hg)]
    have hsub : (rest U).card - (units U)ᶜ.card.choose 2 ≤ D.card := by rw [hcd]; omega
    omega
  · intro hz
    have hfull : (units U)ᶜ = ∅ := Finset.card_eq_zero.mp hz
    have hu : ∀ i : Fin r, {i} ∈ U := by
      intro i
      by_contra hn
      have hm : i ∈ (units U)ᶜ := by simp [units,hn]
      rw [hfull] at hm; exact Finset.notMem_empty _ hm
    have hh := Finset.sum_le_sum (s := rest U) (f := fun _ => 144) (g := layer U) (by
      intro T hT
      obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (hsmall T hT)
      simpa [hu] using layer_pair_ge U i j hij (Finset.mem_filter.mp hT).1)
    simpa [Nat.mul_comm] using hh

lemma price_arith {r k t s d c p : Nat}
    (hk : k = 1 ∨ k = 2) (hc : c = 0 ∨ c = 1) (hcard : c+s+d = r+k) (hu : s+t = r)
    (hp : 216 + 36*(d-1) ≤ p ∨ (36*d + 54*(d-t.choose 2) ≤ p ∧ (t=0 → 144*d ≤ p))) :
    (if c=1 then (if k=1 then 15*r+1 else 15*r+121) else (if k=1 then 6*r+144 else 6*r+192)) ≤
      c+s*(if c=1 then 15 else 6)+p := by
  rcases hc with rfl | rfl <;> rcases hk with rfl | rfl <;> norm_num at *
  all_goals rcases hp with hp | ⟨hp,hp0⟩
  all_goals first | omega | by_cases ht : 4 ≤ t
  all_goals first | omega | (interval_cases t <;> norm_num [Nat.choose] at * <;> omega)

lemma general_lower {r k : Nat} (U : Finset (K r)) (hk : k=1 ∨ k=2) (hU : U.card = r+k) :
    (if k=1 then min (15*r+1) (6*r+144) else min (15*r+121) (6*r+192)) ≤ loss U := by
  let c := csize U
  let s := (units U).card
  let d := (rest U).card
  let t := (units U)ᶜ.card
  let p := ∑ T ∈ rest U, layer U T
  have hu : s+t=r := by
    have he : (units U).card ≤ r := by simpa using Finset.card_le_univ (units U)
    simp [s,t,Finset.card_compl]; omega
  have hcard : c+s+d = r+k := (size_split U).symm.trans hU
  have hc : c=0 ∨ c=1 := by by_cases h : ∅ ∈ U <;> simp [c,csize,h]
  have hp : 216 + 36*(d-1) ≤ p ∨ (36*d + 54*(d-t.choose 2) ≤ p ∧ (t=0 → 144*d ≤ p)) := by
    by_cases hbig : ∃ T ∈ rest U, 3 ≤ T.card
    · obtain ⟨T,ht,h3⟩ := hbig
      exact Or.inl (big_price _ ht h3)
    · apply Or.inr
      apply small_price
      intro T hT
      have := (Finset.mem_filter.mp hT).2
      have hn : ¬ 3 ≤ T.card := fun h => hbig ⟨T,hT,h⟩
      omega
  have h := price_arith hk hc hcard hu hp
  have hl : loss U = c+s*(if c=1 then 15 else 6)+p := by
    rw [loss_split]; by_cases hb : ∅ ∈ U <;> simp [c,s,p,csize,uprice,hb]
  rw [hl]
  split_ifs at * <;> omega

def liftK {r : Nat} (T : K r) : K (r+1) := T.map Fin.castSuccEmb

def pad {r : Nat} (U : Finset (K r)) : Finset (K (r+1)) := insert {Fin.last r} (U.image liftK)

lemma lift_inj {r : Nat} : Function.Injective (@liftK r) := Finset.map_injective _

lemma last_not_lift {r : Nat} (T : K r) : Fin.last r ∉ liftK T := by
  intro h; obtain ⟨i,_,hi⟩ := Finset.mem_map.mp h
  exact Fin.castSucc_ne_last i hi

lemma lift_ne_new {r : Nat} (T : K r) : liftK T ≠ {Fin.last r} := by
  intro h; exact last_not_lift T (h ▸ Finset.mem_singleton_self _)

lemma new_not_image {r : Nat} (U : Finset (K r)) : {Fin.last r} ∉ U.image liftK := by
  rintro h; obtain ⟨T,_,ht⟩ := Finset.mem_image.mp h
  exact lift_ne_new T ht

lemma lift_mem_pad {r : Nat} (U : Finset (K r)) (T : K r) : liftK T ∈ pad U ↔ T ∈ U := by
  simp [pad, lift_ne_new, Finset.mem_image,lift_inj.eq_iff]

lemma pad_center {r : Nat} (U : Finset (K r)) : ∅ ∈ pad U ↔ ∅ ∈ U := by
  have h := lift_mem_pad U ∅
  simpa [liftK] using h

lemma pad_cov {r : Nat} (U : Finset (K r)) (B T : K r) :
    covered (pad U) (liftK B) (liftK T) ↔ covered U B T := by
  constructor
  · intro h A hba hat
    exact (lift_mem_pad _ _).mp (h (liftK A) (Finset.map_subset_map.mpr hba) (Finset.map_subset_map.mpr hat))
  · intro h S hb ht
    obtain ⟨A, hat, rfl⟩ := Finset.subset_map_iff.mp ht
    exact (lift_mem_pad _ _).mpr (h A (Finset.map_subset_map.mp hb) hat)

lemma lift_layer {r : Nat} (U : Finset (K r)) (T : K r) : layer (pad U) (liftK T) = layer U T := by
  have h : (liftK T).powerset = T.powerset.image liftK := by
    ext S
    simp only [Finset.mem_powerset, liftK, Finset.mem_image, Finset.subset_map_iff]
    constructor <;> rintro ⟨B,hB,hS⟩ <;> exact ⟨B,hB,hS.symm⟩
  rw [layer,h,Finset.sum_image lift_inj.injOn]
  simp only [pad_cov]
  simp [layer,liftK]

lemma pad_size {r : Nat} (U : Finset (K r)) : (pad U).card = U.card + 1 := by
  rw [pad, Finset.card_insert_of_notMem (new_not_image U), Finset.card_image_of_injective _ lift_inj]

lemma pad_loss {r : Nat} (U : Finset (K r)) : loss (pad U) = loss U + (if ∅ ∈ U then 15 else 6) := by
  have hm : {Fin.last r} ∈ pad U := Finset.mem_insert_self ..
  change (∑ T ∈ insert {Fin.last r} (U.image liftK), layer (pad U) T) = _
  rw [Finset.sum_insert (new_not_image U), Finset.sum_image lift_inj.injOn, layer_single _ _ hm]
  simp only [lift_layer, pad_center]
  by_cases h : ∅ ∈ U <;> simp [h,loss,Nat.add_comm]

def achieved (r l v : Nat) (c : Bool) : Prop :=
  ∃ U : Finset (K r), U.card = l ∧ loss U = v ∧ (∅ ∈ U ↔ c = true)

lemma achieved_pad {r l v : Nat} {c : Bool} (h : achieved r l v c) :
    achieved (r+1) (l+1) (v + if c then 15 else 6) c := by
  obtain ⟨U,hu,hv,hc⟩ := h
  exact ⟨pad U, by rw [pad_size,hu], by rw [pad_loss,hv]; simp only [hc], (pad_center _).trans hc⟩

lemma achieved_linear {m k b : Nat} {c : Bool}
    (h : achieved m (m+k) ((if c then 15 else 6)*m + b) c) (r : Nat) (hr : m ≤ r) :
    achieved r (r+k) ((if c then 15 else 6)*r + b) c := by
  induction r, hr using Nat.le_induction with
  | base => exact h
  | succ n hn ih => cases c <;> simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using achieved_pad ih

lemma seed_first_center : achieved 0 1 1 true := by
  refine ⟨{∅}, ?_⟩
  decide

lemma seed_first_outer : achieved 2 3 156 false := by
  refine ⟨{{0}, {1}, {0,1}}, ?_⟩
  decide

lemma seed_second_center : achieved 4 6 181 true := by
  refine ⟨insert ∅ (((Finset.univ : K 4).powersetCard 2).erase {0,1}), ?_⟩
  decide

lemma seed_second_outer : achieved 4 6 216 false := by
  refine ⟨(Finset.univ : K 4).powersetCard 2, ?_⟩
  decide

lemma seed_two : achieved 2 4 256 true := by
  refine ⟨Finset.univ, ?_⟩
  decide

lemma seed_three : achieved 3 5 211 true := by
  refine ⟨{∅, {0}, {1}, {0,2}, {1,2}}, ?_⟩
  decide

lemma small_lower_two (U : Finset (K 2)) (h : U.card = 4) : 256 ≤ loss U := by
  exact (by decide : ∀ U ∈ (Finset.univ : Finset (K 2)).powersetCard 4, 256 ≤ loss U) U
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h⟩)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
lemma small_lower_three (U : Finset (K 3)) (h : U.card = 5) : 211 ≤ loss U := by
  exact (by decide : ∀ U ∈ (Finset.univ : Finset (K 3)).powersetCard 5, 211 ≤ loss U) U
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h⟩)

def best (r l v : Nat) : Prop := (∀ U : Finset (K r), U.card = l → v ≤ loss U) ∧
  ∃ U : Finset (K r), U.card = l ∧ loss U = v

lemma achieved_ex {r l v : Nat} {c : Bool} (h : achieved r l v c) :
    ∃ U : Finset (K r), U.card = l ∧ loss U = v := by
  obtain ⟨U,hu,hv,_⟩ := h
  exact ⟨U,hu,hv⟩

lemma first_opt (r : Nat) : best r (r+1) (min (15*r+1) (6*r+144)) := by
  constructor
  · intro U h; simpa using general_lower U (k := 1) (Or.inl rfl) h
  · by_cases h : 15*r+1 ≤ 6*r+144
    · rw [min_eq_left h]
      exact achieved_ex (achieved_linear (c := true) (m := 0) (k := 1) (b := 1) seed_first_center r (Nat.zero_le _))
    · rw [min_eq_right (by omega)]
      exact achieved_ex (achieved_linear (c := false) (m := 2) (k := 1) (b := 144) seed_first_outer r (by omega))

lemma second_opt (r : Nat) (hr : 2 ≤ r) :
    best r (r+2) (if r=2 then 256 else if r=3 then 211 else min (15*r+121) (6*r+192)) := by
  by_cases h2 : r=2
  · subst r
    exact ⟨small_lower_two, achieved_ex seed_two⟩
  by_cases h3 : r=3
  · subst r
    exact ⟨small_lower_three, achieved_ex seed_three⟩
  rw [if_neg h2, if_neg h3]
  constructor
  · intro U h; simpa using general_lower U (k := 2) (Or.inr rfl) h
  · by_cases h : 15*r+121 ≤ 6*r+192
    · rw [min_eq_left h]
      exact achieved_ex (achieved_linear (c := true) (m := 4) (k := 2) (b := 121) seed_second_center r (by omega))
    · rw [min_eq_right (by omega)]
      exact achieved_ex (achieved_linear (c := false) (m := 4) (k := 2) (b := 192) seed_second_outer r (by omega))

lemma kernel_best {r l v : Nat} (h : best r l v) :
    (∀ U : Finset (K r), U.card = l → 11^v ≤ ker (Finset.univ \ U)) ∧
     ∃ U : Finset (K r), U.card = l ∧ ker (Finset.univ \ U) = 11^v := by
  constructor
  · intro U hu
    rw [← orig_inv U, ker_eq_pow, lost_count]
    apply Nat.pow_le_pow_right (by decide : 0 < 11)
    exact h.1 _ ((card_orig U).trans hu)
  · obtain ⟨U,hu,hv⟩ := h.2
    exact ⟨orig U, (card_orig U).trans hu, by rw [ker_eq_pow, lost_count,hv]⟩

end PEqualNP.Outside.L_lib_1168

theorem PEqualNP.Outside.L_lib_1168 : (∀ r : Nat,
  let Kind := Finset (Fin r)
  let Word := Fin r → Fin 16
  let kinds := (Finset.univ : Finset Kind)
  let cube := (Finset.univ : Finset Word)
  let sites := (Finset.univ : Finset (Fin r))
  let pass := fun (e : Kind) (z x : Word) => sites.toList.all (fun j =>
    let w := (z j).val ^^^ (x j).val
    (w &&& 3) != 0 && (w &&& 13) != (if j ∈ e then 1 else 0))
  let zeroRead := fun (d : Word → Fin 11) (q : Kind × Word) =>
    ((cube.filter (fun x => pass q.1 q.2 x)).sum (fun x => (d x).val)) % 11 = 0
  let kernelSize := fun (M : Finset Kind) =>
    ((Finset.univ : Finset (Word → Fin 11)).filter (fun d =>
      ∀ q ∈ M.product cube, zeroRead d q)).card
  let minimumAt := fun (l loss : Nat) =>
    (∀ U : Finset Kind, U.card = l → 11 ^ loss ≤ kernelSize (kinds \ U)) ∧
    ∃ U : Finset Kind, U.card = l ∧ kernelSize (kinds \ U) = 11 ^ loss
  minimumAt (r + 1) (min (15 * r + 1) (6 * r + 144)) ∧
    (2 ≤ r → minimumAt (r + 2)
      (if r = 2 then 256 else if r = 3 then 211 else min (15 * r + 121) (6 * r + 192)))) := by
  intro r
  simpa only [PEqualNP.Outside.L_lib_1168.ker, PEqualNP.Outside.L_lib_1168.readings, PEqualNP.Outside.L_lib_1168.passW, PEqualNP.Outside.L_lib_1168.localPass, Bool.decide_coe, decide_eq_true_eq] using And.intro (PEqualNP.Outside.L_lib_1168.kernel_best (PEqualNP.Outside.L_lib_1168.first_opt r)) (fun hr => PEqualNP.Outside.L_lib_1168.kernel_best (PEqualNP.Outside.L_lib_1168.second_opt r hr))
