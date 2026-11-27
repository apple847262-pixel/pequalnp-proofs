import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25510_aux

abbrev Sig := Int → Bool
def chi (a b c : Bool) := xor a (!b && c)
def rot (k s w : Nat) := ((w <<< (s%k)) ||| (w >>> (k-s%k))) % 2^k
def flipAt (f : Nat → Bool) (i : Nat) := (f i).toNat <<< i
lemma flipBit (f : Nat → Bool) (i j : Nat) :
    (flipAt f i).testBit j = (if j=i then f i else false) := by
  unfold flipAt; rw [Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
  rcases lt_trichotomy j i with hl|he|hg
  · simp [Nat.not_le.mpr hl,Nat.ne_of_lt hl]
  · simp [he]
  · simp [Nat.le_of_lt hg,show j-i≠0 by omega,Nat.ne_of_gt hg]
lemma packBit (f : Nat → Bool) (l : List Nat) (acc j : Nat) :
  (l.foldl (fun z i => z ||| flipAt f i) acc).testBit j =
    (acc.testBit j || (decide (j∈l) && f j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,flipBit]
    by_cases h : j=x
    · subst x; cases e : f j <;> simp [e,Bool.or_assoc]
    · simp [h]
def rawStep (k w : Nat) := (List.range k).foldl (fun z i =>
    z ||| flipAt (fun j => chi (w.testBit j) (w.testBit ((j+1)%k)) (w.testBit ((j+2)%k))) i) 0
lemma stepBit {k j} (h : j<k) (w : Nat) :
    (rawStep k w).testBit j = chi (w.testBit j) (w.testBit ((j+1)%k)) (w.testBit ((j+2)%k)) := by
  simp [rawStep,packBit,h]
lemma rotBit {k j s w : Nat} (h : j<k) (hs : s<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit (if j<s then k-s+j else j-s) := by
  simp only [rot,Nat.mod_eq_of_lt hs,Nat.testBit_mod_two_pow,h,decide_true,Bool.true_and,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases hj : j<s
  · simp [hj,Nat.not_le.mpr hj]
  · have big : w.testBit (k-s+j) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hj,Nat.le_of_not_gt hj,big]

def idx (k : Nat) (j : Int) := (j % (k : Int)).toNat
def bits (k w : Nat) (j : Int) := w.testBit (idx k j)
lemma idxlt {k : Nat} (kp : 0 < k) (j : Int) : idx k j < k := by
  have h := Int.emod_lt_of_pos j (show (0:Int)<k by omega)
  unfold idx;omega
lemma idxSub {k s : Nat} (hs : s<k) (j : Int) :
    idx k (j-(s:Int)) = if idx k j<s then k-s+idx k j else idx k j-s := by
  have hp : (0:Int)<k := by omega
  have a := Int.emod_nonneg j (ne_of_gt hp)
  have b := Int.emod_lt_of_pos j hp
  unfold idx; rw [← Int.emod_sub_emod j (k:Int) (s:Int)]; split
  · next h =>
    rw [←Int.add_emod_left,Int.emod_eq_of_lt (by omega) (by omega)];omega
  · next h => rw [Int.emod_eq_of_lt (by omega) (by omega)];omega
lemma bitsRot {k s w : Nat} (hs : s<k) (hw : w<2^k) (j : Int) :
    bits k (rot k s w) j = bits k w (j-(s:Int)) := by
  unfold bits;rw [rotBit (idxlt (by omega) _) hs hw,idxSub hs]
lemma idxAdd {k : Nat} (kp : 0<k) (j : Int) (s : Nat) :
    (idx k j+s)%k = idx k (j+(s:Int)) := by
  have a := Int.emod_nonneg j (show (k:Int)≠0 by omega)
  unfold idx
  rw [←Int.emod_add_emod j (k:Int) (s:Int)]
  have eq : (j%(k:Int)+(s:Int)).toNat = (j%(k:Int)).toNat + s := by omega
  rw [@Int.toNat_emod (j%(k:Int)+(s:Int)) (k:Int) (by omega) (by omega),eq]
  rfl
lemma bitsStep {k : Nat} (kp : 0<k) (w : Nat) (j : Int) :
    bits k (rawStep k w) j = chi (bits k w j) (bits k w (j+1)) (bits k w (j+2)) := by
  unfold bits; rw [stepBit (idxlt kp _), idxAdd kp j 1,idxAdd kp j 2]; rfl
lemma bitsXor (k a b : Nat) (j : Int) : bits k (a ^^^ b) j = xor (bits k a j) (bits k b j) := Nat.testBit_xor .. 
lemma stepBound (k w : Nat) : rawStep k w < 2^k := by
  have e : rawStep k w % 2^k = rawStep k w := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases h : i<k
    · simp [Nat.testBit_mod_two_pow,h]
    · simp [Nat.testBit_mod_two_pow,rawStep,packBit,h]
  rw [←e];exact Nat.mod_lt _ (by positivity)

theorem halves {α:Type} [Fintype α] (n r:Nat) (cap:r≤n) (g:α → Nat → Bool)
 (size:Fintype.card α=2^n)
 (law:∀t,t<r → ∃f:α→α, (∀a,f (f a)=a) ∧
   (∀a,g (f a) t= !(g a t)) ∧ (∀a j,j<t → g (f a) j=g a j)) :
   (Finset.univ.filter (fun a:α => decide (∀ t:Fin r,g a t.val=false))).card = 2^(n-r) := by
 classical
 let S := fun m:Nat=> Finset.univ.filter (fun a:α => ∀j,j<m → g a j=false)
 have sm (m:Nat) (a:α) : a∈S m ↔ ∀j,j<m → g a j=false := by simp [S]
 have recu (t:Nat) (ht:t<r) : (S t).card = 2*(S (t+1)).card := by
  obtain ⟨f,inv,neg,old⟩:=law t ht
  let p:=fun a => g a t=false
  have stay {a:α} (ha:a∈S t) : f a∈S t := (sm _ _).mpr (fun j hj=> (old a j hj).trans ((sm _ _).mp ha j hj))
  have aa : (S t).filter p = S (t+1) := by
   ext a
   simp only [Finset.mem_filter,sm,p]
   constructor
   · rintro ⟨h,e⟩ j hj
     by_cases eq:j=t
     · rwa [eq]
     · exact h j (by omega)
   · intro h; exact ⟨fun j hj=>h j (by omega),h t (by omega)⟩
  have ab : ((S t).filter p).card = ((S t).filter (fun a=>¬p a)).card := by
   apply Finset.card_nbij' f f
   · intro a ha
     obtain ⟨h,e⟩:=Finset.mem_filter.mp ha
     refine Finset.mem_filter.mpr ⟨stay h,?_⟩
     change g a t=false at e
     change ¬g (f a) t=false
     rw [neg,e]; decide
   · intro a ha
     obtain ⟨h,e⟩:=Finset.mem_filter.mp ha
     refine Finset.mem_filter.mpr ⟨stay h,?_⟩
     change ¬g a t=false at e
     change g (f a) t=false
     rw [neg];cases hval:g a t <;> simp_all
   · exact fun a _=>inv a
   · exact fun a _=>inv a
  have hs : ((S t).filter p).card + ((S t).filter (fun a=>¬p a)).card = (S t).card :=
   Finset.card_filter_add_card_filter_not p
  rw [← ab,aa] at hs
  omega
 have count (m:Nat) (hm:m≤r) : (S m).card=2^(n-m) := by
  induction m with
  | zero => simpa [S] using size
  | succ m ih =>
    have a:=ih (by omega)
    have b:=recu m (by omega)
    have e:n-m = n-(m+1)+1 := by omega
    rw [e,pow_succ] at a;omega
 have same : Finset.univ.filter (fun a:α => decide (∀t:Fin r,g a t.val=false))=S r := by
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,sm]
  exact ⟨fun h t ht => h ⟨t,ht⟩,fun h t=>h t.val t.isLt⟩
 rw [same];exact count _ le_rfl

namespace Bdy
def lin (s : Sig) (j : Int) := xor (xor (s j) (s (j-1))) (s (j+1))
def mix (s : Sig) (j : Int) := chi (lin s j) (lin s (j+1)) (lin s (j+2))
def state (x w : Sig) (c : Nat → Sig) : Nat → Sig
  | 0 => x
  | t+1 => fun j => xor (xor (mix (state x w c t) j) (w (j-2*(t:Int)))) (c (t+1) j)
def guard (x w : Sig) (c : Nat → Sig) (P : Int) (t : Nat) :=
  lin (state x w c t) (P-3*(t:Int)-2)
def start (k row w : Nat) := rot k 1 w ^^^ row
def constBits {k : Nat} (c : Nat → Fin (2^k)) (t : Nat) := bits k (c t).val

def rawMix (k x : Nat) := rawStep k (x ^^^ rot k 1 x ^^^ rot k (k-1) x)
def rawState (k : Nat) (c : Nat → Fin (2^k)) (row w t : Nat) :=
  (List.range t).foldl (fun x s => rawMix k x ^^^ rot k (2*s) w ^^^ (c (s+1)).val) (start k row w)

theorem rawSucc {k} (c : Nat → Fin (2^k)) (row w t : Nat) :
    rawState k c row w (t+1) = rawMix k (rawState k c row w t) ^^^ rot k (2*t) w ^^^ (c (t+1)).val := by
  simp [rawState,List.range_succ,List.foldl_append]

theorem startLt {k row : Nat} (w : Nat) (hr : row<2^k) : start k row w<2^k :=
  Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hr

theorem rawBound {k row : Nat} (c : Nat → Fin (2^k)) (w t : Nat) (hr : row<2^k) :
    rawState k c row w t < 2^k := by
  cases t with
  | zero => exact startLt w hr
  | succ t =>
    rw [rawSucc]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) (c _).isLt

theorem bitsMix {k x : Nat} (hk : 2≤k) (hx : x<2^k) (j : Int) :
    bits k (rawMix k x) j=mix (bits k x) j := by
  have linEq (z : Int) : bits k (x ^^^ rot k 1 x ^^^ rot k (k-1) x) z=lin (bits k x) z := by
    simp only [bitsXor,bitsRot (show 1<k by omega) hx,bitsRot (show k-1<k by omega) hx,lin]
    have e : z-((k-1:Nat):Int)=z+1-(k:Int) := by omega
    simp [bits,idx,e]
  simp only [rawMix,bitsStep (show 0<k by omega),linEq,mix]

theorem rawEq {k t row w : Nat} (c : Nat → Fin (2^k)) (hk : 2≤k) (ht : 2*t≤k)
    (hr : row<2^k) (hw : w<2^k) :
    bits k (rawState k c row w t)=state (bits k (start k row w)) (bits k w) (constBits c) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    rw [rawSucc]
    simp only [bitsXor,bitsMix hk (rawBound c w t hr),ih (by omega),bitsRot (show 2*t<k by omega) hw,state,constBits]
    congr 3 <;> omega

def flipped (k w : Nat) (q : Int) := w ^^^ (1 <<< (idx k q))

theorem flippedLt {k w : Nat} (hk : 0<k) (hw : w<2^k) (q : Int) : flipped k w q<2^k := by
  unfold flipped
  rw [Nat.one_shiftLeft]
  exact Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by decide) (idxlt hk q))

theorem flippedBit (k w : Nat) (q z : Int) :
    bits k (flipped k w q) z=xor (bits k w z) (decide (idx k q=idx k z)) := by
  simp [flipped,bits,Nat.testBit_xor,Nat.one_shiftLeft,Nat.testBit_two_pow,beq_iff_eq,eq_comm]

theorem idxSep {k : Nat} {q z : Int} (lo : q-(k:Int)<z) (hi : z<q) : idx k q ≠ idx k z := by
  intro h
  have kp : (0:Int)<k := by omega
  have em : z%(k:Int)=q%(k:Int) := by
    unfold idx at h
    have hz := Int.emod_nonneg z (ne_of_gt kp)
    have hq := Int.emod_nonneg q (ne_of_gt kp)
    omega
  have div : (k:Int) ∣ q-z := Int.modEq_iff_dvd.mp em
  have := Int.le_of_dvd (show 0<q-z by omega) div
  omega

theorem flipAway {k w : Nat} {q z : Int} (lo : q-(k:Int)<z) (hi : z<q) :
    bits k (flipped k w q) z = bits k w z := by
  rw [flippedBit]
  simp [idxSep lo hi]

theorem flipAtKey (k w : Nat) (q : Int) : bits k (flipped k w q) q = !(bits k w q) := by
  rw [flippedBit]
  simp

theorem flipWrapped (k w : Nat) (q : Int) : bits k (flipped k w q) (q-(k:Int)) = !(bits k w (q-(k:Int))) := by
  rw [flippedBit]
  simp [idx]

theorem linAgree {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+1 → a z=b z) : lin a j=lin b j := by
  unfold lin
  rw [same j (by omega) (by omega),same (j-1) (by omega) (by omega),same (j+1) (by omega) (by omega)]

theorem mixAgree {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+3 → a z=b z) : mix a j=mix b j := by
  have l (v : Int) (h1 : j≤v) (h2 : v≤j+2) := linAgree (a:=a) (b:=b) (j:=v)
    (fun z hl hr => same z (by omega) (by omega))
  unfold mix
  rw [l j (by omega) (by omega),l (j+1) (by omega) (by omega),l (j+2) (by omega) (by omega)]

theorem mixEdge {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+2 → a z=b z) :
    xor (mix a j) (mix b j) = (xor (a (j+3)) (b (j+3)) && !(lin a (j+1))) := by
  have l (v : Int) (h1 : j≤v) (h2 : v≤j+1) := linAgree (a:=a) (b:=b) (j:=v)
    (fun z hl hr => same z (by omega) (by omega))
  have F : ∀ v w p q : Bool, xor (chi v w p) (chi v w q)= (xor p q && !w) := by decide
  have H : ∀ v p q : Bool, xor (xor v p) (xor v q)=xor p q := by decide
  unfold mix
  rw [←l j (by omega) (by omega),←l (j+1) (by omega) (by omega),F]
  congr 1
  unfold lin
  rw [same (j+2) (by omega) (by omega),same (j+2-1) (by omega) (by omega),H,
    show j+2+1=j+3 by omega]

theorem injectDelta (a b u v c : Bool) :
    xor (xor (xor a u) c) (xor (xor b v) c) = xor (xor a b) (xor u v) := by
  revert a b u v c
  decide



lemma mixSame {x y:Sig} (j:Int) (h:∀b,j-1  ≤  b → b  ≤  j+3 → x b=y b) : mix x j=mix y j := by
 have l (i:Int) (a:j ≤ i) (b:i ≤ j+2) : lin x i=lin y i := by
  unfold lin;rw [h i (by omega) (by omega),h (i-1) (by omega) (by omega),h (i+1) (by omega) (by omega)]
 unfold mix
 rw [l _ (by omega) (by omega),l _ (by omega) (by omega),l _ (by omega) (by omega)]
lemma stateLocal {x w v:Sig} {c:Nat→Sig} (t:Nat) (j:Int) :
 (∀b, j-2*((t:Int)-1) ≤ b → b ≤ j+3*((t:Int)-1) → w b=v b) →
 state x w c t j=state x v c t j := by
 induction t generalizing j with
 | zero=>intro _;rfl
 | succ t ih=>
   intro ag
   have m:mix (state x w c t) j=mix (state x v c t) j:=by
    apply mixSame
    intro b h1 h2
    apply ih
    intro i il ir
    apply ag <;> omega
   simp only [state,m,ag (j-2*t) (by omega) (by omega)]
lemma guardLocal {x w v:Sig} {c:Nat→Sig} (P:Int) (t:Nat)
 (ag:∀j,P-5*(t:Int)-1 ≤ j → j ≤ P-4 → w j=v j) :
 guard x w c P t=guard x v c P t := by
 unfold guard lin
 have h (j:Int) (lo:P-3*(t:Int)-3 ≤ j) (hi:j ≤ P-3*(t:Int)-1) :
   state x w c t j=state x v c t j := by
  apply stateLocal
  intro b bl br
  apply ag <;> omega
 rw [h _ (by omega) (by omega),h _ (by omega) (by omega),h _ (by omega) (by omega)]

lemma guardFlip {x w v:Sig} {c:Nat→Sig} (P:Int) (n:Nat)
 (fp:v (P-5*((n+1:Nat):Int)-1) = !w (P-5*((n+1:Nat):Int)-1))
 (ag:∀j,P-5*((n+1:Nat):Int)-1<j → j ≤ P-4 → v j=w j) :
 guard x v c P (n+1) = !(guard x w c P (n+1)) := by
 let m:=P-3*((n+1:Nat):Int)-2
 have eq (j:Int) (lo:m ≤ j) (hi:j ≤ m+1) :
   state x v c (n+1) j = state x w c (n+1) j := by
  apply stateLocal
  intro b bl br;apply ag <;> dsimp [m] at * <;> omega
 have body : mix (state x v c n) (m-1)=mix (state x w c n) (m-1) := by
  apply mixSame
  intro b bl br
  apply stateLocal
  intro d dl dr;apply ag <;> dsimp [m] at * <;> omega
 have ha : state x v c (n+1) (m-1) = !(state x w c (n+1) (m-1)) := by
  simp only [state,body]
  rw [show m-1-2*(n:Int)=P-5*((n+1:Nat):Int)-1 by dsimp [m];omega,fp]
  generalize mix (state x w c n) (m-1)=b
  generalize w (P-5*((n+1:Nat):Int)-1)=a
  generalize c (n+1) (m-1)=d
  cases a <;> cases b <;> cases d <;> rfl
 change xor (xor (state x v c (n+1) m) (state x v c (n+1) (m-1))) (state x v c (n+1) (m+1))=_
 rw [eq m (by omega) (by omega),ha,eq (m+1) (by omega) (by omega)]
 change xor (xor (state x w c (n+1) m) (!(state x w c (n+1) (m-1)))) (state x w c (n+1) (m+1))=
    !(xor (xor (state x w c (n+1) m) (state x w c (n+1) (m-1))) (state x w c (n+1) (m+1)))
 generalize state x w c (n+1) m=a
 generalize state x w c (n+1) (m-1)=b
 generalize state x w c (n+1) (m+1)=d
 cases a <;> cases b <;> cases d <;> rfl

abbrev KPair (k:Nat) := Fin (2^k) × Fin (2^k)
def flipF {k:Nat} (h:0<k) (p:Int) (w:Fin (2^k)) : Fin (2^k) :=
 ⟨flipped k w.val p,flippedLt h w.isLt p⟩
lemma flipFtwice {k:Nat} (h:0<k) (p:Int) (w:Fin (2^k)) : flipF h p (flipF h p w)=w := by
 apply Fin.ext;simp [flipF,flipped]
lemma awayRight {k w:Nat} {p j:Int} (lo:p<j) (hi:j<p+(k:Int)) :
 bits k (flipped k w p) j = bits k w j := by
 rw [flippedBit]
 have ne: idx k p ≠ idx k j := Ne.symm (idxSep (q:=j) (z:=p) (by omega) lo)
 simp [ne]

def testG {k:Nat} (c:Nat→Fin (2^k)) (P:Int) (a:KPair k) (t:Nat) :=
 guard (bits k a.1.val) (bits k a.2.val) (constBits c) P t

lemma firstGuard {k:Nat} (hk:3 ≤ k) (x w:Nat) (c:Nat→Fin (2^k)) (P:Int):
 guard (bits k (flipped k x (P-3))) (bits k w) (constBits c) P 0 =
 !(guard (bits k x) (bits k w) (constBits c) P 0) := by
 let v:=bits k x
 let v':=bits k (flipped k x (P-3))
 simp only [guard,Nat.cast_zero,mul_zero,sub_zero,state,lin]
 change xor (xor (v' (P-2)) (v' (P-2-1))) (v' (P-2+1)) =
  !(xor (xor (v (P-2)) (v (P-2-1))) (v (P-2+1)))
 rw [show P-2-1=P-3 by omega]
 have a:v' (P-3)= !(v (P-3)) := flipAtKey .. 
 have b:v' (P-2)=v (P-2) := awayRight (by omega) (by omega)
 have d:v' (P-2+1)=v (P-2+1) := awayRight (by omega) (by omega)
 rw [a,b,d]
 cases v (P-2) <;> cases v (P-3) <;> cases v (P-2+1) <;> rfl



def prep {k:Nat} (a:KPair k) : KPair k :=
 (⟨start k a.1.val a.2.val,startLt _ a.1.isLt⟩,a.2)
lemma prepInv {k:Nat} (a:KPair k) : prep (prep a)=a := by
 apply Prod.ext
 · apply Fin.ext;simp [prep,start]
 · rfl



def guards510 (x w : Sig) (c : Nat → Sig) (P : Int) (t : Nat) (d : Fin 3) :=
  lin (state x w c t) (P-3*(t:Int)-3+(d.val:Int))

def upper (L U B C : Bool) := xor (!B && C) (!(xor B L) && xor C (xor L U))
def advance (L U A B C : Bool) : Bool × Bool := (L && !A,upper L U B C)

def run510 (g : Nat → Fin 3 → Bool) : Nat → Bool × Bool
  | 0 => (true,false)
  | t+1 => let pair := run510 g t
           advance pair.1 pair.2 (g t 0) (g t 1) (g t 2)

theorem guards510_guard (x w : Sig) (c : Nat → Sig) (P : Int) (t : Nat) (d : Fin 3) :
    guards510 x w c P t d = guard x w c (P-1+(d.val:Int)) t := by
  unfold guards510 guard
  congr 1
  omega

private theorem linDelta (a b : Sig) (j : Int) :
    xor (lin a j) (lin b j) = xor (xor (xor (a j) (b j)) (xor (a (j-1)) (b (j-1))))
      (xor (a (j+1)) (b (j+1))) := by
  have e : ∀ a b c d e f : Bool,
    xor (xor (xor a b) c) (xor (xor d e) f) =
      xor (xor (xor a d) (xor b e)) (xor c f) := by decide
  exact e .. 

theorem mixTwin {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+1 → a z=b z) :
    xor (mix a j) (mix b j) =
      upper (xor (a (j+2)) (b (j+2))) (xor (a (j+3)) (b (j+3))) (lin a (j+1)) (lin a (j+2)) := by
  have d1 := linDelta a b (j+1)
  rw [same (j+1) (by omega) (by omega),same (j+1-1) (by omega) (by omega),show j+1+1=j+2 by omega] at d1
  simp only [Bool.xor_self,Bool.false_xor] at d1
  have d2 := linDelta a b (j+2)
  rw [same (j+2-1) (by omega) (by omega),show j+2+1=j+3 by omega] at d2
  simp only [Bool.xor_self,Bool.xor_false] at d2
  have tab : ∀ a b bb c cc l u : Bool, xor b bb=l → xor c cc=xor l u →
    xor (chi a b c) (chi a bb cc) = upper l u b c := by decide
  unfold mix
  rw [←linAgree same]
  exact tab _ _ _ _ _ _ _ d1 d2

theorem frontier510 {x x' w w' : Sig} (c : Nat → Sig) {I P : Int} {r : Nat} (rp : 0<r)
    (hp : P=I+3*(r:Int))
    (bx : ∀ j : Int, I-(r:Int) ≤ j → j<P-1 → x j=x' j)
    (exL : xor (x (P-1)) (x' (P-1))=true) (exU : xor (x P) (x' P)=false)
    (kw : ∀ t : Nat, t+1<r → ∀ j : Int, I-(r:Int)+(t:Int)+1 ≤ j → j ≤ P-3*((t:Int)+1) →
      w (j-2*(t:Int)) = w' (j-2*(t:Int)))
    (ke : xor (w (I-2*((r:Int)-1))) (w' (I-2*((r:Int)-1)))=true) :
    state x w c r I = state x' w' c r I ↔ (run510 (guards510 x w c P) r).2=true := by
  let F (t : Nat) := P-3*(t:Int)
  let L (t : Nat) := I-(r:Int)+(t:Int)
  let a := state x w c
  let b := state x' w' c
  let g := guards510 x w c P
  let E := run510 g
  have ga (t : Nat) : g t 0=lin (a t) (F t-3) := by
    change lin (a t) (F t - 3 + 0) = _
    rw [add_zero]
  have gb (t : Nat) : g t 1=lin (a t) (F t-2) := by
    change lin (a t) (F t - 3 + 1) = _
    rw [show F t-3+1=F t-2 by omega]
  have gc (t : Nat) : g t 2=lin (a t) (F t-1) := by
    change lin (a t) (F t - 3 + 2) = _
    rw [show F t-3+2=F t-1 by omega]
  let Right (t : Nat) := xor (a t (F t)) (b t (F t)) = (E t).2
  let Left (t : Nat) := xor (a t (F t-1)) (b t (F t-1)) = (E t).1
  let Earlier (t : Nat) := ∀ z : Int, L t ≤ z → z<F t-1 → a t z=b t z
  have mixRight (t : Nat) (ht : t<r) (same : Earlier t) (el : Left t) (er : Right t) :
      xor (mix (a t) (F (t+1))) (mix (b t) (F (t+1))) = (E (t+1)).2 := by
    have f2 : F (t+1)+2=F t-1 := by dsimp [F];omega
    have f3 : F (t+1)+3=F t := by dsimp [F];omega
    have f1 : F (t+1)+1=F t-2 := by dsimp [F];omega
    have m := mixTwin (a:=a t) (b:=b t) (j:=F (t+1)) (by
      intro z lo hi
      apply same z
      · dsimp [L,F] at lo ⊢
        omega
      · omega)
    rw [f2,f3,f1,el,er,←gb t,←gc t] at m
    exact m
  have inv (t : Nat) (ht : t<r) : Earlier t ∧ Left t ∧ Right t := by
    induction t with
    | zero =>
      simpa [Earlier,Left,Right,L,F,a,b,state,E,run510] using And.intro bx (And.intro exL exU)
    | succ t ih =>
      obtain ⟨same,el,er⟩ := ih (by omega)
      have ksame (j : Int) (jl : L (t+1)≤j) (jr : j≤F (t+1)) :
          w (j-2*(t:Int))=w' (j-2*(t:Int)) :=
        kw t ht j (by dsimp [L] at jl;omega) (by dsimp [F] at jr;omega)
      have f3 : F (t+1)+3=F t := by dsimp [F];omega
      refine ⟨?_,?_,?_⟩
      · intro j jl jr
        have ma : mix (a t) j=mix (b t) j := by
          apply mixAgree
          intro z lo hi
          apply same z
          · dsimp [L] at jl ⊢;omega
          · omega
        change xor (xor (mix (a t) j) _) _=xor (xor (mix (b t) j) _) _
        rw [ma,ksame j jl (by omega)]
      · let j := F (t+1)-1
        have jl : L (t+1)≤j := by dsimp [j,L,F];omega
        have jr : j ≤ F (t+1) := by dsimp [j];omega
        have m := mixEdge (a:=a t) (b:=b t) (j:=j) (by
          intro z lo hi
          apply same z
          · dsimp [L] at jl ⊢;omega
          · dsimp [j] at hi;omega)
        rw [show j+3=F t-1 by dsimp [j];omega,el,
          show j+1=F t-3 by dsimp [j];omega,←ga t] at m
        change xor (xor (xor (mix (a t) j) _) _) (xor (xor (mix (b t) j) _) _)=(E (t+1)).1
        rw [injectDelta,ksame j jl jr,m]
        simp [E,run510,advance,j]
      · have m := mixRight t (by omega) same el er
        change xor (xor (xor (mix (a t) (F (t+1))) _) _) (xor (xor (mix (b t) (F (t+1))) _) _)=(E (t+1)).2
        rw [injectDelta,m,ksame (F (t+1)) (by dsimp [L,F];omega) (by omega)]
        simp
  obtain ⟨s,rs⟩ : ∃ s : Nat,r=s+1 := ⟨r-1,by omega⟩
  obtain ⟨early,le,ri⟩ := inv s (by omega)
  have m := mixRight s (by omega) early le ri
  have fi : F (s+1)=I := by dsimp [F];omega
  rw [fi] at m
  have delta : xor (a (s+1) I) (b (s+1) I)=!((E (s+1)).2) := by
    change xor (xor (xor (mix (a s) I) _) _) (xor (xor (mix (b s) I) _) _)=_
    rw [injectDelta,m,show I-2*(s:Int)=I-2*((r:Int)-1) by omega,ke]
    simp
  have finish : ∀ s b y : Bool, xor s b = !y → (s=b ↔ y=true) := by decide
  rw [rs]
  exact finish _ _ _ delta

private theorem naturalBit {k w : Nat} (i : Fin k) : bits k w (i.val:Int)=w.testBit i.val := by
  unfold bits idx
  rw [Int.emod_eq_of_lt (by omega) (by have := i.isLt;omega)]
  rfl

theorem missed510 {k r : Nat} (c : Nat → Fin (2^k)) (i : Fin k) (hr : 5≤r)
    (hk : k+4=5*r) (row w : Fin (2^k)) :
    (rawState k c row.val w.val r).testBit i.val =
      (rawState k c row.val (w.val ^^^ (1 <<< ((i.val+3*r-2)%k))) r).testBit i.val ↔
    (run510 (guards510 (bits k (start k row.val w.val)) (bits k w.val) (constBits c) ((i.val:Int)+3*(r:Int))) r).2=true := by
  let I : Int := i.val
  let P := I+3*(r:Int)
  let q := P-2
  let f := flipped k w.val q
  let x := bits k (start k row.val w.val)
  let x' := bits k (start k row.val f)
  have fbound : f<2^k := flippedLt (by omega) w.isLt q
  have index : idx k q=(i.val+3*r-2)%k := by
    unfold idx
    rw [Int.toNat_emod (by dsimp [q,P,I];omega) (by omega)]
    congr 1
    dsimp [q,P,I]
    omega
  have nf : w.val ^^^ (1 <<< ((i.val+3*r-2)%k)) = f := by
    change _ = w.val ^^^ (1 <<< (idx k q))
    rw [index]
  rw [nf,←naturalBit (w:=rawState k c row.val w.val r) i,←naturalBit (w:=rawState k c row.val f r) i,
      rawEq c (by omega) (by omega) row.isLt w.isLt,rawEq c (by omega) (by omega) row.isLt fbound]
  change state x (bits k w.val) (constBits c) r I = state x' (bits k f) (constBits c) r I ↔ _
  apply frontier510 (constBits c) (P:=P) (by omega) rfl
  · intro j jl jh
    have e := flipAway (k:=k) (w:=w.val) (q:=q) (z:=j-((1:Nat):Int))
      (by dsimp [q,P] at *;omega) (by dsimp [q];omega)
    simp only [x,x',start,bitsXor,bitsRot (show 1<k by omega) w.isLt,bitsRot (show 1<k by omega) fbound]
    rw [show bits k f (j-((1:Nat):Int))=bits k w.val (j-((1:Nat):Int)) from e]
  · simp only [x,x',start,bitsXor,bitsRot (show 1<k by omega) w.isLt,bitsRot (show 1<k by omega) fbound]
    rw [show P-1-((1:Nat):Int)=q by dsimp [q];omega,show bits k f q=!(bits k w.val q) from flipAtKey ..]
    cases bits k w.val q <;> cases bits k row.val (P-1) <;> rfl
  · have ne : idx k q ≠ idx k (q+1) := (idxSep (k:=k) (q:=q+1) (z:=q) (by omega) (by omega)).symm
    have equ : bits k f (q+1) = bits k w.val (q+1) := by
      change bits k (flipped k w.val q) _ = _
      rw [flippedBit]
      simp [ne]
    simp only [x,x',start,bitsXor,bitsRot (show 1<k by omega) w.isLt,bitsRot (show 1<k by omega) fbound]
    rw [show P-((1:Nat):Int) = q+1 by dsimp [q];omega,equ]
    simp
  · intro t tr j jl jh
    apply (flipAway (k:=k) (w:=w.val) (q:=q) ?_ ?_).symm
    · dsimp [q,P] at *
      omega
    · dsimp [q,P] at *
      omega
  · rw [show I-2*((r:Int)-1)=q-(k:Int) by dsimp [q,P];omega,
      show bits k f (q-(k:Int))=!(bits k w.val (q-(k:Int))) from flipWrapped ..]
    cases bits k w.val (q-(k:Int)) <;> rfl

def threeTest {k:Nat} (c:Nat→Fin (2^k)) (P:Int) (a:KPair k) (t:Nat) (d:Fin 3) :=
 testG c (P-1+(d.val:Int)) a t
def position (j:Nat) : Fin 3 := ⟨2-j%3,by omega⟩
def specG {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (tgt:Fin r→Fin 3→Bool) (a:KPair k) (j:Nat) :=
 xor (threeTest c P a (j/3) (position j))
     (if h:j/3<r then tgt ⟨j/3,h⟩ (position j) else false)

lemma g0Agree {k:Nat} (x w:Nat) (c:Nat→Fin (2^k)) (P p:Int)
 (lo:p<P-3) (hi:P-1<p+(k:Int)) :
 guard (bits k (flipped k x p)) (bits k w) (constBits c) P 0 =
 guard (bits k x) (bits k w) (constBits c) P 0 := by
 simp only [guard,Nat.cast_zero,mul_zero,sub_zero,state,lin]
 rw [awayRight (p:=p) (by omega) (by omega),awayRight (p:=p) (by omega) (by omega),awayRight (p:=p) (by omega) (by omega)]

lemma negXor510 (a b:Bool): xor (!a) b= !(xor a b) := by cases a <;> cases b <;> rfl

lemma pairFlip510 (k r:Nat) (c:Nat→Fin (2^k)) (P:Int) (hr:5 ≤ r) (hk:k+4=5*r)
 (j:Nat) (hj:j<3*r) :
 ∃f:KPair k→KPair k, (∀a,f (f a)=a) ∧
   (∀a,threeTest c P (f a) (j/3) (position j)= !(threeTest c P a (j/3) (position j))) ∧
   (∀a m,m<j → threeTest c P (f a) (m/3) (position m)=threeTest c P a (m/3) (position m)) := by
 let p0:=P-1+((position j).val:Int)
 have kp:0<k:=by omega
 by_cases zero:j/3=0
 · let f := fun (a:KPair k)=>(flipF kp (p0-3) a.1,a.2)
   refine ⟨f,?_,?_,?_⟩
   · intro a;apply Prod.ext <;> simp [f,flipFtwice]
   · intro a;rw [zero];exact firstGuard (by omega) a.1.val a.2.val c p0
   · intro a m hm
     have mt:m/3=0 := by omega
     rw [mt];apply g0Agree <;> dsimp [p0,position] <;> omega
 · obtain ⟨t,et⟩ : ∃t,j/3=t+1 := ⟨j/3-1,by omega⟩
   let p:=p0-5*((t+1:Nat):Int)-1
   let f:=fun (a:KPair k)=>(a.1,flipF kp p a.2)
   refine ⟨f,?_,?_,?_⟩
   · intro a;apply Prod.ext <;> simp [f,flipFtwice]
   · intro a;rw [et];apply guardFlip
     · exact flipAtKey _ _ _
     · intro i il ir;apply awayRight <;> dsimp [p,p0,position] at * <;> omega
   · intro a m hm
     apply guardLocal
     intro i il ir
     apply awayRight <;> dsimp [p,p0,position] at * <;> omega

lemma historyCount (k r:Nat) (c:Nat→Fin (2^k)) (P:Int) (hr:5 ≤ r) (hk:k+4=5*r)
 (tgt:Fin r→Fin 3→Bool):
 (Finset.univ.filter (fun a:KPair k=>decide (∀t:Fin r,∀d:Fin 3,threeTest c P a t.val d=tgt t d))).card=2^(2*k-3*r) := by
 let g:=specG c P tgt
 have num:=PEqualNP.Outside.L_meta_25510_aux.halves (2*k) (3*r) (by omega) g
       (by simp [KPair,pow_add,Nat.two_mul]) (fun j hj=>by
    obtain ⟨f,iv,neg,h⟩:=pairFlip510 k r c P hr hk j hj
    refine ⟨f,iv,?_,?_⟩
    · intro a;unfold g specG;rw [neg,negXor510]
    · intro a m hm;unfold g specG;rw [h _ _ hm])
 rw [←num];congr 1;ext a
 simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
 constructor
 · intro h j
   have hj:j.val/3<r:=by have:=j.isLt;omega
   change xor _ (if h:j.val/3<r then tgt ⟨_,h⟩ _ else false)=false
   simp [hj,h ⟨j.val/3,hj⟩ (position j.val)]
 · intro h t d
   let j:=3*t.val+(2-d.val)
   have v:d.val<3:=d.isLt
   have h1:j<3*r:=by dsimp [j];have:=t.isLt;omega
   have h2:j/3=t.val:=by dsimp [j];omega
   have h3:position j=d := by apply Fin.ext;dsimp [position,j];omega
   have eq:=h ⟨j,h1⟩
   change xor (threeTest c P a (j/3) (position j)) (if h:j/3<r then tgt ⟨j/3,h⟩ (position j) else false)=false at eq
   simp only [h2,h3,dif_pos t.isLt] at eq
   simpa using eq

abbrev Schedule (r:Nat) := Fin r → Fin 3 → Bool
def extendSched {r:Nat} (h:Schedule r) (t:Nat) (d:Fin 3) :=
 if ht:t<r then h ⟨t,ht⟩ d else false
abbrev accepts {r:Nat} (h:Schedule r) := (run510 (extendSched h) r).2=true
def history {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (a:KPair k) : Schedule r :=
 fun t d=> threeTest c P a t.val d

lemma historyFiber {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (hr:5 ≤ r) (hk:k+4=5*r) (h:Schedule r) :
 (Finset.univ.filter (fun a:KPair k=>history c P a=h)).card=2^(2*k-3*r) := by
 rw [←historyCount k r c P hr hk h]
 congr 1;ext a
 simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
 exact ⟨fun eq t d=>congrFun (congrFun eq t) d,fun hyp=>funext (fun t=>funext (hyp t))⟩

theorem runCongr510 {g f:Nat→Fin 3→Bool} (n:Nat) (eq:∀t,t<n → ∀d,g t d=f t d) :
 run510 g n=run510 f n := by
 induction n with
 | zero=>rfl
 | succ n ih=>
   simp only [run510,ih (fun t ht=>eq t (by omega)),eq n (by omega)]

theorem isAccepted {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (a:KPair k) :
 accepts (r:=r) (history c P a) ↔
 (run510 (guards510 (bits k a.1.val) (bits k a.2.val) (constBits c) P) r).2=true := by
 unfold accepts
 rw [runCongr510 r (g:=extendSched (history (r:=r) c P a))
   (f:=guards510 (bits k a.1.val) (bits k a.2.val) (constBits c) P) (fun t ht d=>by
     simp only [extendSched,dif_pos ht,history,threeTest,testG,guards510_guard])]

theorem countSchedules {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (hr:5 ≤ r) (hk:k+4=5*r)
 (histSize:(Finset.univ.filter (fun h:Schedule r=>decide (accepts h))).card=(r+1)*2^(3*r-(r+1))) :
 (Finset.univ.filter (fun a:KPair k=>decide (accepts (r:=r) (history c P a)))).card=
 (r+1)*2^(2*k-(r+1)) := by
 classical
 let H:=Finset.univ.filter (fun h:Schedule r=>decide (accepts h))
 let f:=history (r:=r) c P
 have co:=Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (KPair k)) H f
 have ef : Finset.univ.filter (fun a:KPair k=>decide (accepts (f a)))=
           Finset.univ.filter (fun a:KPair k=>f a∈H) := by ext a;simp [H]
 change (Finset.univ.filter (fun a:KPair k=>decide (accepts (f a)))).card=_
 rw [ef,←co]
 simp_rw [show ∀h:Schedule r,(Finset.univ.filter (fun a:KPair k=>f a=h)).card=2^(2*k-3*r) from historyFiber c P hr hk]
 simp only [Finset.sum_const,smul_eq_mul]
 change H.card*_ = _
 have hcard:H.card=(r+1)*2^(3*r-(r+1)):=histSize
 rw [hcard,Nat.mul_assoc,←pow_add]
 congr 2 <;> omega

theorem rawCount510 {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (hr:5 ≤ r) (hk:k+4=5*r)
 (histSize:(Finset.univ.filter (fun h:Schedule r=>decide (accepts h))).card=(r+1)*2^(3*r-(r+1)))
 (miss:KPair k → Prop) [DecidablePred miss]
 (crit:∀a,miss a↔(run510 (guards510 (bits k (start k a.1.val a.2.val)) (bits k a.2.val) (constBits c) P) r).2=true):
 (Finset.univ.filter miss).card=(r+1)*2^(2*k-(r+1)) := by
 rw [←countSchedules c P hr hk histSize]
 apply Finset.card_nbij' prep prep
 · intro a ha
   simp only [Finset.mem_coe,Finset.mem_filter, Finset.mem_univ,true_and,decide_eq_true_eq] at *
   exact (isAccepted c P (prep a)).mpr ((crit a).mp ha)
 · intro a ha
   simp only [Finset.mem_coe,Finset.mem_filter, Finset.mem_univ,true_and,decide_eq_true_eq] at *
   apply (crit (prep a)).mpr
   have e:= (isAccepted (r:=r) c P (prep (prep a))).mp
   apply e
   rwa [prepInv]
 · exact fun a _=>prepInv a
 · exact fun a _=>prepInv a

namespace Sched
abbrev Alpha := Fin 3 → Bool
abbrev Hist (n : Nat) := Fin n → Alpha
def extendHist {n : Nat} (f : Hist n) (t : Nat) (d : Fin 3) :=
  if ht : t<n then f ⟨t,ht⟩ d else false
def finalState {n : Nat} (f : Hist n) := run510 (extendHist f) n
def histEquiv (n : Nat) : Hist (n+1) ≃ Hist n × Alpha where
  toFun f := (fun j => f j.castSucc,f (Fin.last n))
  invFun p := fun j => Fin.lastCases p.2 p.1 j
  left_inv f := by funext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  right_inv p := by cases p; ext <;> simp
lemma runAgree (n : Nat) (g h : Nat → Alpha) (eqn : ∀ t < n, g t=h t) :
    run510 g n = run510 h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run510,ih (fun t ht => eqn t (by omega)),eqn n (by omega)]
lemma finalStep {n : Nat} (f : Hist n) (a : Alpha) :
    finalState ((histEquiv n).symm (f,a)) =
      advance (finalState f).1 (finalState f).2 (a 0) (a 1) (a 2) := by
  let v := (histEquiv n).symm (f,a)
  have hv0 (q : Fin n) : v q.castSucc = f q := by
    change Fin.lastCases a f q.castSucc = f q
    simp
  have hvL : v (Fin.last n) = a := by
    change Fin.lastCases a f (Fin.last n) = a
    simp
  have hp : run510 (extendHist v) n = finalState f := by
    apply runAgree
    intro t ht
    funext j
    simp only [extendHist,dif_pos ht,dif_pos (show t<n+1 by omega)]
    exact congrFun (hv0 ⟨t,ht⟩) j
  have ha : extendHist v n = a := by
    funext j
    simp only [extendHist,dif_pos (Nat.lt_succ_self n)]
    exact congrFun hvL j
  change advance (run510 (extendHist v) n).1 (run510 (extendHist v) n).2 _ _ _ = _
  rw [hp,ha]

def seen (p : Bool × Bool → Bool) (s : Bool × Bool) := (p s).toNat
def count (n : Nat) (p : Bool × Bool → Bool) : Nat := ∑ f : Hist n, seen p (finalState f)
def lbit (s : Bool × Bool) := s.1
def ubit (s : Bool × Bool) := s.2
def onlyU (s : Bool × Bool) := !s.1 && s.2
def total (p : Bool × Bool → Bool) (s : Bool × Bool) := ∑ a : Alpha, seen p (advance s.1 s.2 (a 0) (a 1) (a 2))
lemma stepCount (n : Nat) (p : Bool × Bool → Bool) :
    count (n+1) p = ∑ f : Hist n, total p (finalState f) := by
  unfold count total
  rw [←(histEquiv n).symm.sum_comp, Fintype.sum_prod_type]
  simp only [finalStep]
lemma lTotal (s : Bool × Bool) : total lbit s = 4*seen lbit s := by
  rcases s with ⟨a,b⟩;cases a <;> cases b <;> decide +kernel
lemma oTotal (s : Bool × Bool) : total onlyU s = 2*seen lbit s + 4*seen onlyU s := by
  rcases s with ⟨a,b⟩;cases a <;> cases b <;> decide +kernel
lemma uTotal (s : Bool × Bool) : total ubit s = 4*seen lbit s + 4*seen onlyU s := by
  rcases s with ⟨a,b⟩;cases a <;> cases b <;> decide +kernel
lemma lCount (n : Nat) : count n lbit = 4^n := by
  induction n with
  | zero => decide +kernel
  | succ n ih => rw [stepCount];simp only [lTotal,←Finset.mul_sum];change 4 * count n lbit = _; rw [ih,pow_succ];omega
lemma oCount (n : Nat) : 2 * count n onlyU = n*4^n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [stepCount];simp only [oTotal,Finset.sum_add_distrib,←Finset.mul_sum]
    change 2*(2*count n lbit+4*count n onlyU) = _
    rw [lCount, pow_succ];nlinarith only [ih]
lemma uCount (n : Nat) : count (n+1) ubit = (n+2)*2^(2*n+1) := by
  rw [stepCount];simp only [uTotal,Finset.sum_add_distrib,←Finset.mul_sum]
  change 4*count n lbit+4*count n onlyU = _
  have h : 4^n = 2^(2*n) := by rw [pow_mul];rfl
  rw [lCount,pow_succ,←h]
  nlinarith only [oCount n]
end Sched
lemma scheduleCount (r : Nat) (hr : 5 ≤ r) :
    (Finset.univ.filter (fun h : Fin r → Fin 3 → Bool => (run510 (fun t d => if ht:t<r then h ⟨t,ht⟩ d else false) r).2 = true)).card =
       (r+1)*2^(3*r-(r+1)) := by
  cases r with
  | zero => omega
  | succ n =>
    have e := Sched.uCount n
    have cv : Sched.count (n+1) Sched.ubit = (Finset.univ.filter (fun h : Sched.Hist (n+1) => (Sched.finalState h).2 = true)).card := by
      unfold Sched.count Sched.seen Sched.ubit
      have hb (b : Bool) : b.toNat = if b=true then 1 else 0 := by cases b <;> rfl
      simp [hb,Finset.sum_boole]
    rw [cv] at e
    rw [show 3*(n+1)-(n+1+1)=2*n+1 by omega]
    exact e
end Bdy
end PEqualNP.Outside.L_meta_25510_aux

open PEqualNP.Outside.L_meta_25510_aux PEqualNP.Outside.L_meta_25510_aux.Bdy in
theorem PEqualNP.Outside.L_meta_25510 :
∀ (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (i : Fin k),
  5 ≤ r → k + 4 = 5 * r →
  let rot := fun (s word : ℕ) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : ℕ) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (row key : ℕ) =>
    (List.range r).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (constants (t + 1)).val) (rot 1 key ^^^ row)
  let flip := fun key : ℕ => key ^^^ (1 <<< ((i.val + 3 * r - 2) % k))
  ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    (state pair.1.val pair.2.val).testBit i.val =
      (state pair.1.val (flip pair.2.val)).testBit i.val)).card =
    (r + 1) * 2 ^ (2 * k - (r + 1)) := by
  intro k r c i hr hk
  let P := (i.val:Int)+3*(r:Int)
  let M := fun a : KPair k =>
    (rawState k c a.1.val a.2.val r).testBit i.val =
     (rawState k c a.1.val (a.2.val ^^^ (1 <<< ((i.val+3*r-2)%k))) r).testBit i.val
  change (Finset.univ.filter M).card=(r+1)*2^(2*k-(r+1))
  refine rawCount510 c P hr hk ?_ M ?_
  · rw [←scheduleCount r hr]
    congr 1
  · intro a
    exact missed510 c i hr hk a.1 a.2
