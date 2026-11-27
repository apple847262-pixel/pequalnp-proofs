import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25509_aux

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

def survives (x w : Sig) (c : Nat → Sig) (P : Int) : Nat → Bool
  | 0 => true
  | t+1 => survives x w c P t && !(guard x w c P t)

theorem survives_iff (x w : Sig) (c : Nat → Sig) (P : Int) (r : Nat) :
    survives x w c P r=true ↔ ∀ t<r, guard x w c P t=false := by
  induction r with
  | zero => simp [survives]
  | succ r ih =>
    rw [survives,Bool.and_eq_true_iff,ih]
    simp only [Bool.not_eq_true']
    constructor
    · rintro ⟨h,e⟩ t ht
      by_cases b : t=r
      · simpa [b] using e
      · exact h t (by omega)
    · intro h
      exact ⟨fun t ht => h t (by omega),h r (by omega)⟩

theorem frontier509 {x x' w w' : Sig} (c : Nat → Sig) {I P : Int} {r : Nat} (rp : 0<r)
    (hp : P=I+3*(r:Int))
    (bx : ∀ j : Int, I-(r:Int) ≤ j → j<P → x j=x' j) (ex : xor (x P) (x' P)=true)
    (kw : ∀ t : Nat, t<r → ∀ j : Int, I-(r:Int)+(t:Int)+1 ≤ j → j ≤ P-3*((t:Int)+1) →
      (t+1≠r ∨ j≠I) → w (j-2*(t:Int)) = w' (j-2*(t:Int)))
    (ke : xor (w (I-2*((r:Int)-1))) (w' (I-2*((r:Int)-1)))=true) :
    state x w c r I = state x' w' c r I ↔ ∀ s<r, guard x w c P s=false := by
  let F (t : Nat) := P-3*(t:Int)
  let L (t : Nat) := I-(r:Int)+(t:Int)
  let a := state x w c
  let b := state x' w' c
  have inv (t : Nat) (ht : t≤r) :
      (∀ j : Int, L t ≤ j → j<F t → a t j=b t j) ∧
      xor (a t (F t)) (b t (F t)) =
        if t=r then !(survives x w c P t) else survives x w c P t := by
    induction t with
    | zero =>
      simpa [L,F,a,b,state,survives,Nat.ne_of_lt rp] using And.intro bx ex
    | succ t ih =>
      obtain ⟨same,edge⟩ := ih (by omega)
      have tr : t<r := by omega
      rw [if_neg tr.ne] at edge
      have f : F (t+1)+3=F t := by dsimp [F];omega
      have fmid : F (t+1)+1=P-3*(t:Int)-2 := by dsimp [F];omega
      have ksame (j : Int) (jl : L (t+1)≤j) (jr : j≤F (t+1)) (hn : t+1≠r ∨ j≠I) :
          w (j-2*(t:Int))=w' (j-2*(t:Int)) :=
        kw t tr j (by dsimp [L] at jl;omega) (by dsimp [F] at jr;omega) hn
      constructor
      · intro j jl jr
        have ma : mix (a t) j = mix (b t) j := by
          apply mixAgree
          intro z zl zr
          apply same z
          · dsimp [L] at jl ⊢;omega
          · omega
        have nk : t+1≠r ∨ j≠I := by dsimp [F] at jr;omega
        change xor (xor (mix (a t) j) _) _ = xor (xor (mix (b t) j) _) _
        rw [ma,ksame j jl (by omega) nk]
      · have m := mixEdge (a:=a t) (b:=b t) (j:=F (t+1)) (by
          intro z zl zr
          apply same z
          · dsimp [L,F] at zl ⊢
            omega
          · omega)
        rw [f,edge,fmid] at m
        change xor (mix (a t) (F (t+1))) (mix (b t) (F (t+1))) = survives x w c P (t+1) at m
        change xor (xor (xor (mix (a t) (F (t+1))) _) _) (xor (xor (mix (b t) (F (t+1))) _) _) = _
        rw [injectDelta,m]
        by_cases last : t+1=r
        · have fj : F (t+1)=I := by dsimp [F];omega
          have eq : F (t+1)-2*(t:Int)=I-2*((r:Int)-1) := by rw [fj];omega
          rw [eq,ke,if_pos last]
          simp
        · have e := ksame (F (t+1)) (by dsimp [L,F];omega) (by omega) (Or.inl last)
          rw [e,if_neg last]
          simp
  have e := (inv r le_rfl).2
  have fr : F r=I := by dsimp [F];omega
  rw [fr,if_pos rfl] at e
  rw [←survives_iff]
  change a r I = b r I ↔ _
  have finish : ∀ s b y : Bool, xor s b = !y → (s=b ↔ y=true) := by decide
  exact finish _ _ _ e

theorem natBit {k w : Nat} (i : Fin k) : bits k w (i.val:Int)=w.testBit i.val := by
  unfold bits idx
  rw [Int.emod_eq_of_lt (by omega) (by have := i.isLt;omega)]
  rfl

theorem missed509 {k r : Nat} (c : Nat → Fin (2^k)) (i : Fin k) (hr : 4≤r)
    (hk : k+3=5*r) (row w : Fin (2^k)) :
    (rawState k c row.val w.val r).testBit i.val =
      (rawState k c row.val (w.val ^^^ (1 <<< ((i.val+3*r-1)%k))) r).testBit i.val ↔
    ∀ t<r, guard (bits k (start k row.val w.val)) (bits k w.val) (constBits c) ((i.val:Int)+3*(r:Int)) t=false := by
  let I : Int := i.val
  let P := I+3*(r:Int)
  let q := P-1
  let f := flipped k w.val q
  let x := bits k (start k row.val w.val)
  let x' := bits k (start k row.val f)
  have fbound : f<2^k := flippedLt (by omega) w.isLt q
  have index : idx k q=(i.val+3*r-1)%k := by
    unfold idx
    rw [Int.toNat_emod (by dsimp [q,P,I];omega) (by omega)]
    congr 1
    dsimp [q,P,I]
    omega
  have nf : w.val ^^^ (1 <<< ((i.val+3*r-1)%k)) = f := by
    change _ = w.val ^^^ (1 <<< (idx k q))
    rw [index]
  rw [nf,←natBit (w:=rawState k c row.val w.val r) i,←natBit (w:=rawState k c row.val f r) i,
      rawEq c (by omega) (by omega) row.isLt w.isLt,rawEq c (by omega) (by omega) row.isLt fbound]
  change state x (bits k w.val) (constBits c) r I = state x' (bits k f) (constBits c) r I ↔ _
  apply frontier509 (constBits c) (P:=P) (by omega) rfl
  · intro j jl jh
    have e := flipAway (k:=k) (w:=w.val) (q:=q) (z:=j-((1:Nat):Int))
      (by dsimp [q,P] at *;omega) (by dsimp [q];omega)
    simp only [x,x',start,bitsXor,bitsRot (show 1<k by omega) w.isLt,bitsRot (show 1<k by omega) fbound]
    rw [show bits k f (j-((1:Nat):Int))=bits k w.val (j-((1:Nat):Int)) from e]
  · simp only [x,x',start,bitsXor,bitsRot (show 1<k by omega) w.isLt,bitsRot (show 1<k by omega) fbound]
    rw [show P-((1:Nat):Int)=q by rfl,show bits k f q=!(bits k w.val q) from flipAtKey ..]
    cases bits k w.val q <;> cases bits k row.val P <;> rfl
  · intro t tr j jl jh ex
    apply (flipAway (k:=k) (w:=w.val) (q:=q) ?_ ?_).symm
    · dsimp [q,P] at *
      omega
    · dsimp [q,P] at *
      omega
  · rw [show I-2*((r:Int)-1)=q-(k:Int) by dsimp [q,P];omega,
      show bits k f (q-(k:Int))=!(bits k w.val (q-(k:Int))) from flipWrapped ..]
    cases bits k w.val (q-(k:Int)) <;> rfl

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

lemma countG (k r:Nat) (c:Nat→Fin (2^k)) (P:Int) (hr:4 ≤ r) (hk:k+3=5*r) :
 (Finset.univ.filter (fun a:KPair k=>decide (∀t:Fin r,testG c P a t.val=false))).card = 2^(2*k-r) := by
 apply PEqualNP.Outside.L_meta_25509_aux.halves (2*k) r (by omega) (testG c P)
 · simp [KPair,pow_add,Nat.two_mul]
 · intro t ht
   have kp:0<k:=by omega
   cases t with
   | zero =>
     let f:= fun (a:KPair k) => (flipF kp (P-3) a.1,a.2)
     refine ⟨f,?_,?_,?_⟩
     · intro a;apply Prod.ext <;> simp [f,flipFtwice]
     · intro a;exact firstGuard (by omega) a.1.val a.2.val c P
     · intro a j h;omega
   | succ n =>
     let p:=P-5*((n+1:Nat):Int)-1
     let f:=fun (a:KPair k)=>(a.1,flipF kp p a.2)
     refine ⟨f,?_,?_,?_⟩
     · intro a;apply Prod.ext <;> simp [f,flipFtwice]
     · intro a;apply guardFlip
       · exact flipAtKey _ _ _
       · intro j hl hi
         exact awayRight hl (by omega)
     · intro a j hj
       apply guardLocal
       intro l h1 h2
       apply awayRight <;> dsimp [p] at * <;> omega

def prep {k:Nat} (a:KPair k) : KPair k :=
 (⟨start k a.1.val a.2.val,startLt _ a.1.isLt⟩,a.2)
lemma prepInv {k:Nat} (a:KPair k) : prep (prep a)=a := by
 apply Prod.ext
 · apply Fin.ext;simp [prep,start]
 · rfl

lemma countMiss {k r:Nat} (c:Nat→Fin (2^k)) (P:Int) (hr:4 ≤ r) (hk:k+3=5*r)
 (miss:KPair k → Prop) [DecidablePred miss]
 (crit:∀ a, miss a ↔ ∀t:Fin r,testG c P (prep a) t.val=false):
 (Finset.univ.filter miss).card = 2^(2*k-r) := by
 rw [←countG k r c P hr hk]
 apply Finset.card_nbij' prep prep
 · intro a ha
   simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq] at *
   exact (crit a).mp ha
 · intro a ha
   simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq] at *
   apply (crit (prep a)).mpr
   rwa [prepInv]
 · exact fun a _=>prepInv a
 · exact fun a _=>prepInv a

end Bdy
end PEqualNP.Outside.L_meta_25509_aux

open PEqualNP.Outside.L_meta_25509_aux PEqualNP.Outside.L_meta_25509_aux.Bdy in
theorem PEqualNP.Outside.L_meta_25509 :
∀ (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (i : Fin k),
  4 ≤ r → k + 3 = 5 * r →
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
  let flip := fun key : ℕ => key ^^^ (1 <<< ((i.val + 3 * r - 1) % k))
  ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    (state pair.1.val pair.2.val).testBit i.val =
      (state pair.1.val (flip pair.2.val)).testBit i.val)).card = 2 ^ (2 * k - r) := by
  intro k r c i hr hk
  let P := (i.val:Int)+3*(r:Int)
  let M := fun a : KPair k =>
    (rawState k c a.1.val a.2.val r).testBit i.val =
     (rawState k c a.1.val (a.2.val ^^^ (1 <<< ((i.val+3*r-1)%k))) r).testBit i.val
  change (Finset.univ.filter M).card=2^(2*k-r)
  apply countMiss c P hr hk M
  intro a
  have e:=missed509 c i hr hk a.1 a.2
  change _ ↔ ∀t:Fin r,guard (bits k (start k a.1.val a.2.val)) (bits k a.2.val) (constBits c) P t.val=false
  exact e.trans ⟨fun h t=>h t.val t.isLt, fun h t ht=>h ⟨t,ht⟩⟩
