import PEqualNP.Outside.SparseBoundedListPruning

namespace PEqualNP.Outside.SparseLayeredSearchMachine

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Universal
open PEqualNP.Outside.SatCodePrimitives
open PEqualNP.Outside.BackdoorPathCore (Word cut cut_cpt cut_eq)
open PEqualNP.Outside.RecordPairScan (wire)
open PEqualNP.Outside.RecordMapMachine (flatMapWord flatMapWord_cpt flatMapWord_enc)
open PEqualNP.Outside.SparseBoundedListPruning (trim trim_cpt trim_correct)

local notation "CPT" => ComputableInPolyTime (fun w : Word => w) (fun w : Word => w)
local notation "CPT₂" => ComputableInPolyTime encodePair (fun w : Word => w)

def pack (cap pad rs : Word) : Word := pairB cap (pairB pad rs)
def cap (z : Word) : Word := (unpairB z).1
def pad (z : Word) : Word := (unpairB (unpairB z).2).1
def records (z : Word) : Word := (unpairB (unpairB z).2).2

def round (f : Word × Word → Word) (branch : Word → Word) (z : Word) : Word :=
  pack (cap z) (pad z) (cut (pad z) (trim f (cap z, flatMapWord branch (records z))))

theorem round_cpt (f : Word × Word → Word) (branch : Word → Word) (hf : CPT₂ f) (hb : CPT branch) :
    CPT (round f branch) := by
  have hc : CPT cap := cpt_unpairB1
  have hp : CPT pad := cpt_unpairB1_1 cpt_unpairB2
  have hr : CPT records := cpt_unpairB2_1 cpt_unpairB2
  have ht := cpt_comp (cpt_pair hc (cpt_comp hr (flatMapWord_cpt branch hb))) (trim_cpt f hf)
  exact cptl (cpt_pairB2 hc (cpt_pairB2 hp (cut_cpt hp ht))) (fun _ => rfl)

def measure (z : Word) : ℕ := (pad z).length + 2

theorem measure_round (f : Word × Word → Word) (branch : Word → Word) (z : Word) :
    measure (round f branch z) ≤ measure z := by
  simp [measure, round, pack, pad, unpairB_pairB]

theorem round_size (f : Word × Word → Word) (branch : Word → Word) (z : Word) :
    (round f branch z).length ≤ z.length + measure z := by
  have hc := unpairB_length z
  have hp := unpairB_length (unpairB z).2
  have hb : (cut (pad z) (trim f (cap z, flatMapWord branch (records z)))).length ≤
      (pad z).length := by simp [cut_eq]
  simp only [round, pack, pairB_length, measure, cap, pad] at *
  omega

theorem measure_bound (z : Word) : measure z ≤ 2 * z.length + 2 := by
  have hc := unpairB_length z
  have hp := unpairB_length (unpairB z).2
  simp only [measure,pad]
  omega

def run (f : Word × Word → Word) (branch : Word → Word) (depth capWord padWord : Word → Word)
    (x : Word) : Word :=
  records ((round f branch)^[(depth x).length] (pack (capWord x) (padWord x) (wire [x])))

theorem run_cpt (f : Word × Word → Word) (branch : Word → Word) (depth capWord padWord : Word → Word)
    (hf : CPT₂ f) (hb : CPT branch) (hd : CPT depth) (hc : CPT capWord) (hp : CPT padWord) :
    CPT (run f branch depth capWord padWord) := by
  obtain ⟨m⟩ := round_cpt f branch hf hb
  have loop := Iter.iter_polyTime_measure (round f branch) m measure 2
    (measure_round f branch) (round_size f branch) measure_bound
  have hs : CPT (fun x => pack (capWord x) (padWord x) (wire [x])) :=
    cptl (cpt_pairB2 hc (cpt_pairB2 hp (cpt_pairB2 cpt_id (cpt_const [])))) (fun _ => rfl)
  have ho : CPT records := cpt_unpairB2_1 cpt_unpairB2
  exact cptl (cpt_comp (cpt_comp (cpt_pair hs hd) loop) ho) (fun _ => rfl)

theorem wire_size (rs : List Word) (n : ℕ) (h : ∀ a ∈ rs, a.length ≤ n) :
    (wire rs).length ≤ rs.length * (2*n+1) := by
  induction rs with
  | nil => simp [wire]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    rw [wire, pairB_length, List.length_cons, Nat.add_mul, one_mul]
    omega

def expand (B : Word → List Word) (rs : List Word) : List Word := rs.flatMap B

theorem round_correct
    (f : Word × Word → Word) (B : Word → List Word) (branch : Word → Word)
    (henc : ∀ y, branch y = wire (B y))
    (G : Language Bool) (S : Finset Word) (n : ℕ) (capWord padWord : Word)
    (hc : S.card < capWord.length) (hp : capWord.length * (2*n+1) ≤ padWord.length)
    (hred : ∀ a b : Word, a.length ≤ n → b.length ≤ n →
      (f (a,b) ∈ S ↔ a ∈ G ∨ b ∈ G))
    (rs : List Word) (hsize : ∀ y ∈ expand B rs, y.length ≤ n) :
    ∃ bs : List Word, round f branch (pack capWord padWord (wire rs)) =
      pack capWord padWord (wire bs) ∧ bs.Sublist (expand B rs) ∧
      ((∃ y ∈ bs, y ∈ G) ↔ ∃ y ∈ expand B rs, y ∈ G) := by
  obtain ⟨bs, htrim, hsub, hbs, he⟩ :=
    trim_correct f (· ∈ G) S capWord hc (expand B rs)
      (fun a ha b hb => hred a b (hsize a ha) (hsize b hb))
  have hlen : (wire bs).length ≤ padWord.length :=
    (wire_size bs n (fun y hy => hsize y (hsub.subset hy))).trans
      ((Nat.mul_le_mul_right _ hbs).trans hp)
  refine ⟨bs, ?_, hsub, he⟩
  simp only [round, cap, pad, records, pack, unpairB_pairB, flatMapWord_enc _ B henc]
  change pack capWord padWord (cut padWord (trim f (capWord,wire (expand B rs)))) = _
  rw [htrim, cut_eq, List.take_of_length_le hlen]
  rfl

theorem expand_exists (B : Word → List Word) (G : Language Bool)
    (hB : ∀ y, y ∈ G ↔ ∃ z ∈ B y, z ∈ G) (rs : List Word) :
    (∃ y ∈ expand B rs, y ∈ G) ↔ ∃ y ∈ rs, y ∈ G := by
  constructor
  · rintro ⟨y,hy,hyG⟩
    obtain ⟨z,hz,hzy⟩ := List.mem_flatMap.mp hy
    exact ⟨z,hz,(hB z).mpr ⟨y,hzy,hyG⟩⟩
  · rintro ⟨z,hz,hzG⟩
    obtain ⟨y,hy,hyG⟩ := (hB z).mp hzG
    exact ⟨y,List.mem_flatMap.mpr ⟨z,hz,hy⟩,hyG⟩

theorem run_invariant
    (f : Word × Word → Word) (B : Word → List Word) (branch : Word → Word)
    (henc : ∀ y, branch y = wire (B y)) (G : Language Bool) (S : Finset Word)
    (x capWord padWord : Word) (d limit : ℕ)
    (hc : S.card < capWord.length) (hp : capWord.length * (2*limit+1) ≤ padWord.length)
    (hg : ∀ y z : Word, z ∈ B y → z.length ≤ y.length+d)
    (hB : ∀ y, y ∈ G ↔ ∃ z ∈ B y, z ∈ G)
    (hred : ∀ a b : Word, a.length ≤ limit → b.length ≤ limit →
      (f (a,b) ∈ S ↔ a ∈ G ∨ b ∈ G))
    (n : ℕ) (hn : x.length+d*n ≤ limit) :
    ∃ rs : List Word,
      (round f branch)^[n] (pack capWord padWord (wire [x])) = pack capWord padWord (wire rs) ∧
      (∀ y ∈ rs, y.length ≤ x.length+d*n) ∧
      (∀ y ∈ rs, y ∈ (expand B)^[n] [x]) ∧
      ((∃ y ∈ rs, y ∈ G) ↔ x ∈ G) := by
  induction n with
  | zero => exact ⟨[x],rfl,by simp, fun _ h => h, by simp⟩
  | succ n ih =>
    have hstep : x.length + d*n ≤ limit := by
      rw [Nat.mul_succ] at hn
      omega
    obtain ⟨rs,hr,hlen,hreach,hyes⟩ := ih hstep
    have hlen' : ∀ y ∈ expand B rs, y.length ≤ x.length+d*(n+1) := by
      intro y hy
      obtain ⟨z,hz,hzy⟩ := List.mem_flatMap.mp hy
      have h₁ := hg z y hzy
      have h₂ := hlen z hz
      rw [Nat.mul_succ]
      omega
    obtain ⟨bs,hbs,hsub,he⟩ := round_correct f B branch henc G S limit capWord padWord hc hp hred rs
      (fun y hy => (hlen' y hy).trans hn)
    refine ⟨bs,?_,(fun y hy => hlen' y (hsub.subset hy)),?_,?_,⟩
    · rw [Function.iterate_succ_apply', hr, hbs]
    · intro y hy
      obtain ⟨z,hz,hzy⟩ := List.mem_flatMap.mp (hsub.subset hy)
      rw [Function.iterate_succ_apply']
      exact List.mem_flatMap.mpr ⟨z,hreach z hz,hzy⟩
    · exact he.trans ((expand_exists B G hB rs).trans hyes)

end PEqualNP.Outside.SparseLayeredSearchMachine
