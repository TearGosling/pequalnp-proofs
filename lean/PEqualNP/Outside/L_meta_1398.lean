import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1398

-- The low five bits test neighboring pairs in cyclic order. The next five
-- test the pairs at distance two, again in cyclic order.
def leaf (i : BitVec 3) : BitVec 10 :=
  if i = 0 then 305 else if i = 1 then 579 else if i = 2 then 166 else if i = 3 then 332 else 664

def gate (op : Bool) (a b : BitVec 10) : BitVec 10 := if op then a &&& b else a ||| b

def possible : ℕ → BitVec 10 → Prop
  | 0, w => ∃ i, w = leaf i
  | k + 1, w => ∃ op a b, possible k a ∧ possible k b ∧ w = gate op a b

def test (j : Fin 10) (i : Fin 5) := (leaf (BitVec.ofNat 3 i.val)).getLsbD j.val

def tracks (k : ℕ) (f : (Fin 5 → Bool) → Bool) :=
  ∃ w, possible k w ∧ ∀ j : Fin 10, f (test j) = w.getLsbD j.val

-- Repeating a child at an AND handles all the formulas shorter than three levels.
lemma carry {k f} (h : tracks k f) : tracks (k+1) f := by
  obtain ⟨w,hw,obs⟩ := h
  exact ⟨w,⟨true,w,w,hw,hw,by simp [gate]⟩,obs⟩

lemma combine {k f g} (hf : tracks k f) (hg : tracks k g) :
    tracks (k+1) (fun x => f x && g x) ∧ tracks (k+1) (fun x => f x || g x) := by
  obtain ⟨a,ha,fa⟩ := hf
  obtain ⟨b,hb,gb⟩ := hg
  exact ⟨⟨_,⟨true,a,b,ha,hb,rfl⟩,fun j => by simp [gate,fa j,gb j]⟩,
    ⟨_,⟨false,a,b,ha,hb,rfl⟩,fun j => by simp [gate,fa j,gb j]⟩⟩

def inputs : List (BitVec 10) := [305,579,166,332,664]

def one : List (BitVec 10) :=
  [1,2,4,8,16,32,64,128,166,256,305,332,381,439,494,512,579,664,702,731,743,847,883,953,988]

-- An OR child may not light up any diagonal. An AND child must light up all edges.
def below : List (BitVec 10) := [0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24]
def above : List (BitVec 10) := [383,447,511,703,735,767,863,895,959,991,1023]

abbrev limits (w : BitVec 10) : Prop :=
  (w &&& 31 = w → w ∈ below) ∧ (w &&& 31 = 31 → w ∈ above)

def allPairs (xs : List (BitVec 10)) (testPair : BitVec 10 → BitVec 10 → Bool) :=
  xs.all (fun a => xs.all (testPair a))

lemma pairAt {xs : List (BitVec 10)} {p : BitVec 10 → BitVec 10 → Bool}
    (check : allPairs xs p = true) {a b} (ha : a ∈ xs) (hb : b ∈ xs) : p a b = true :=
  List.all_eq_true.mp (List.all_eq_true.mp check a ha) b hb

lemma input_mem (i : BitVec 3) : leaf i ∈ inputs := by
  unfold leaf
  split_ifs <;> decide

lemma level_one {w} (hw : possible 1 w) : w ∈ one := by
  obtain ⟨op,_,_,⟨i,rfl⟩,⟨j,rfl⟩,rfl⟩ := hw
  have cert : allPairs inputs (fun a b => decide (a &&& b ∈ one ∧ a ||| b ∈ one)) = true := by decide +kernel
  obtain ⟨yes,no⟩ := of_decide_eq_true (pairAt cert (input_mem i) (input_mem j))
  cases op
  · exact no
  · exact yes

set_option maxHeartbeats 2000000 in
lemma level_two {w} (hw : possible 2 w) : limits w := by
  obtain ⟨op,a,b,ha,hb,rfl⟩ := hw
  have cert : allPairs one (fun a b => decide (limits (a &&& b) ∧ limits (a ||| b))) = true := by decide +kernel
  obtain ⟨yes,no⟩ := of_decide_eq_true (pairAt cert (level_one ha) (level_one hb))
  cases op
  · exact no
  · exact yes

lemma excludes (w : BitVec 10) (hw : possible 3 w) : w ≠ 31 := by
  obtain ⟨op,a,b,ha,hb,rfl⟩ := hw
  have la := level_two ha
  have lb := level_two hb
  intro eq
  cases op
  · change a ||| b = 31 at eq
    have parts : a &&& 31 = a ∧ b &&& 31 = b := by
      rw [← eq]
      constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
        simp only [BitVec.getLsbD_and,BitVec.getLsbD_or] <;>
        cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
    have cert : allPairs below (fun x y => decide (x ||| y ≠ 31)) = true := by decide +kernel
    exact of_decide_eq_true (pairAt cert (la.1 parts.1) (lb.1 parts.2)) eq
  · change a &&& b = 31 at eq
    have parts : a &&& 31 = 31 ∧ b &&& 31 = 31 := by
      rw [← eq]
      constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
        simp only [BitVec.getLsbD_and] <;>
        cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
    have cert : allPairs above (fun x y => decide (x &&& y ≠ 31)) = true := by decide +kernel
    exact of_decide_eq_true (pairAt cert (la.2 parts.1) (lb.2 parts.2)) eq

lemma tests_target : ∀ j : Fin 10,
    ((test j 0 && test j 1) || (test j 1 && test j 2) || (test j 2 && test j 3) ||
      (test j 3 && test j 4) || (test j 4 && test j 0)) = (31 : BitVec 10).getLsbD j.val := by decide

end PEqualNP.Outside.L_meta_1398

theorem PEqualNP.Outside.L_meta_1398 : ¬ (∀ T : ℕ → Set ((Fin 5 → Bool) → Bool), (∀ i : Fin 5, (fun x : Fin 5 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 5 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 5 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 5 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 5 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 5 → Bool => (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0)) ∈ T 3) := by
  intro alleged
  obtain ⟨w,hw,obs⟩ := alleged (fun k => {f | PEqualNP.Outside.L_meta_1398.tracks k f})
    (fun i => ⟨_,⟨BitVec.ofNat 3 i.val,rfl⟩,fun _ => rfl⟩)
    (fun _ _ => PEqualNP.Outside.L_meta_1398.carry)
    (fun _ _ _ => PEqualNP.Outside.L_meta_1398.combine)
  apply PEqualNP.Outside.L_meta_1398.excludes w hw
  exact BitVec.eq_of_getLsbD_eq fun j hj => (obs ⟨j,hj⟩).symm.trans (PEqualNP.Outside.L_meta_1398.tests_target ⟨j,hj⟩)
