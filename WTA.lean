open Classical

theorem const_func_ext [Nonempty α] {a b : β} : (fun _ : α => a) = (fun _ => b) → (a = b) := by  
  intro h
  have ha : (fun _ : α => a) (choice inferInstance) = a := rfl
  have hb : (fun _ : α => b) (choice inferInstance) = b := rfl
  rw [←ha, ←hb, h]

def Vector (α : Type) (n : Nat) := Fin n → α  

infix:95 "⋆" => Vector

def Vector.ε : α⋆0 := (nomatch ·)

def Vector.ε' (h : n = 0) : α⋆n := 
  fun ⟨_, h'⟩ => by simp [h] at h'; contradiction

def Vector.prefix (as : α⋆(n + 1)) : α⋆n := 
  fun i => as ⟨i.val, Nat.lt_succ_of_le $ Nat.le_of_lt i.isLt⟩

def Vector.all (v : α⋆n) (p : α → Prop) : Prop :=
  ∀ i, p (v i)

def Vector.map (v : α⋆n) (f : α → β) : β⋆n := 
  (f $ v ·)

abbrev Op (α : Type) (n : Nat) := α⋆n → α

instance : CoeHead (Op α 0) α where
  coe op := op Vector.ε

abbrev BinOp (α : Type) := α → α → α

instance : Coe (Op α 2) (BinOp α) where
  coe op a₁ a₂ := op fun | 0 => a₁ | 1 => a₂

instance : CoeTail (BinOp α) (Op α 2) where
  coe op as := op (as 0) (as 1)

def ExistsUnique (p : α → Prop) := ∃ x, p x ∧ ∀ y, p y → y = x

open Lean TSyntax.Compat in
macro "∃! " xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

class Fintype (α : Type)

def Set (α : Type _) := α → Prop

instance : Membership α (Set α) where
  mem a s := s a

instance : CoeSort (Set α) Type where
  coe s := { a : α // s a }

abbrev Set.empty : Set α := fun _ => False

instance : EmptyCollection (Set α) := ⟨Set.empty⟩

def Set.Nonempty (s : Set α) : Prop := s ≠ ∅

def Set.Nonempty.iff_exists_mem : Set.Nonempty s ↔ ∃ a, a ∈ s := by
  sorry

abbrev Set.univ : Set α := fun _ => True

abbrev Set.singleton (a : α) : Set α := (· = a)

theorem Set.mem_univ : a ∈ Set.univ := .intro

def Set.image (f : α → β) : Set β := 
  (∃ a, f a = ·)

theorem Set.mem_image_iff : (b ∈ Set.image f) ↔ (∃ a, f a = b) := ⟨id, id⟩

theorem Set.image_choose {b : β} : (h : b ∈ Set.image f) → (f $ choose h) = b :=
  choose_spec

def Set.union (s₁ s₂ : Set α) := fun a => a ∈ s₁ ∨ a ∈ s₂

def Set.bUnion (s : Set (Set α)) : Set α := 
  fun a => ∃ m, m ∈ s ∧ a ∈ m

def Set.Subset (s₁ s₂ : Set α) : Prop :=
  ∀ a, a ∈ s₁ → a ∈ s₂

infix:50 " ⊆ " => Set.Subset

theorem Set.mem_ext {s₁ s₂ : Set α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  fun h => funext (fun a => propext (h a))

abbrev Vector.lift {s : Set α} (v : s⋆n) : α⋆n := (v ·)

abbrev Word (α : Type) := List α

postfix:95 "⋆" => Word

abbrev Word.ε : α⋆ := []

@[match_pattern]
abbrev Word.prepend : α → α⋆ → α⋆ := List.cons

abbrev Word.append (u : α⋆) (i : α) : α⋆ := u ++ [i]

infixl:70 "⬝" => Word.prepend

infixl:70 "•" => Word.append

def Word.prefixes : α⋆ → Set (α⋆)
  | .ε => Set.singleton .ε
  | i⬝v => fun u => (u = i⬝v) ∨ (u ∈ prefixes v)

@[simp] 
theorem Set.mem_singleton : a ∈ Set.singleton a := by
  simp [singleton, Membership.mem]

theorem Word.ε_mem_prefixes (u : Word α) : .ε ∈ u.prefixes := by
  induction u
  case nil => simp [prefixes, Set.mem_singleton]
  case cons i v hi => 
    simp [prefixes] 
    simp [Membership.mem] at *
    exact hi

def Vector.word : {n : Nat} → α⋆n → α⋆
  | 0,     _ => []
  | n + 1, as => as.prefix.word ++ [as ⟨n, Nat.lt_succ_self _⟩]

def Vector.prefixes : {n : Nat} → (α⋆n) → Set (α⋆)
  | 0,     _  => Set.singleton .ε
  | _ + 1, as => fun u => (u = as.word) ∨ (u ∈ as.prefix.prefixes)

def Function.Injective (f : α → β) : Prop :=
  ∀ a₁ a₂, (f a₁ = f a₂) → a₁ = a₂

def Function.Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

structure Function.Bijective (f : α → β) : Prop where
  inj : Function.Injective f
  surj : Function.Surjective f


-----------------------------------------------------------------------------------------


class Alphabet (α : Type) where
  [nonempty : Nonempty α]
  [finite : Fintype α]

structure RankedAlphabet where
  alphabet : Type
  rank : alphabet → Nat
  [isAlphabet : Alphabet alphabet]

instance : CoeSort RankedAlphabet Type where
  coe Δ := Δ.alphabet

structure Algebra (Δ : RankedAlphabet) where
  carrier : Type
  θ : (σ : Δ) → Op carrier (Δ.rank σ)  

def Algebra.ops (alg : Algebra Δ) : Set (Σ k : Nat, Op alg.carrier k) :=
  fun ⟨k, op⟩ => ∃ (σ : Δ) (h : Δ.rank σ = k), (alg.θ σ = h ▸ op)

def Closed (alg : Algebra Δ) (sub : Set alg.carrier) : Prop :=
  ∀ σ (cs : Vector sub $ Δ.rank σ), (alg.θ σ cs.lift) ∈ sub

theorem Algebra.carrier_closed (alg : Algebra Δ) : Closed alg Set.univ := by
  simp [Closed, Set.mem_univ]

-- Note that this defines a `Set`.
inductive Closure (sub : Set α) (ops : Set (Σ k : Nat, Op α k)) : α → Prop
  | root : (a ∈ sub) → Closure sub ops a
  | app {v : Vector α k} : (⟨k, op⟩ ∈ ops) → (∀ i, Closure sub ops $ v i) → Closure sub ops (op v)

abbrev closure (sub : Set α) (ops : Set (Σ k : Nat, Op α k)) : Set α := 
  Closure sub ops

structure Subalgebra (alg : Algebra Δ) where
  carrier : Set alg.carrier
  θ : (σ : Δ) → Op alg.carrier (Δ.rank σ)
  restricted : ∀ σ cs, cs.all (· ∈ carrier) → θ σ cs = alg.θ σ cs
  closed : Closed alg carrier 

def Subalgebra.algebra {alg : Algebra Δ} (s : Subalgebra alg) : Algebra Δ where
  carrier := s.carrier
  θ σ cs := {
    val := s.θ σ cs.lift
    property := by 
      have h : cs.lift.all (· ∈ s.carrier) := by
        simp [Vector.all, Vector.lift]
        intro i
        exact (cs i).property
      rw [s.restricted _ _ h]
      apply s.closed
  }

instance {alg : Algebra Δ} : Coe (Subalgebra alg) (Algebra Δ) where
  coe := Subalgebra.algebra

structure Hom (alg₁ alg₂ : Algebra Δ) where
  hom : alg₁.carrier → alg₂.carrier
  property : ∀ σ cs, hom (alg₁.θ σ cs) = (alg₂.θ σ) (hom ∘ cs)

theorem Hom.ext (hom₁ hom₂ : Hom alg₁ alg₂) : hom₁.hom = hom₂.hom → hom₁ = hom₂ := by
  intro h
  cases hom₁ <;> cases hom₂
  simp at h
  simp [h]

instance : CoeFun (Hom alg₁ alg₂) (fun _ => alg₁.carrier → alg₂.carrier) where
  coe h := h.hom

theorem lemma_2_6_2 (hom : Hom alg₁ alg₂) : Closed alg₂ (Set.image hom) := by
  intro σ cs₂
  simp [Closed, Set.mem_image_iff]
  let cs₁ := (cs₂ · |>.property |> choose)
  have h := hom.property σ cs₁
  exists alg₁.θ σ cs₁
  rw [h]
  congr 
  funext i
  apply Set.image_choose

-- Lemma 2.6.3  
def Hom.compose (hom₁₂ : Hom alg₁ alg₂) (hom₂₃ : Hom alg₂ alg₃) : Hom alg₁ alg₃ where
  hom := hom₂₃ ∘ hom₁₂
  property := by
    intro σ cs₁
    simp [hom₁₂.property σ cs₁, hom₂₃.property σ $ hom₁₂ ∘ cs₁]
    rfl

infixr:90 " ∘ " => Hom.compose

structure Iso (alg₁ alg₂ : Algebra Δ) extends Hom alg₁ alg₂ where
  bij : Function.Bijective hom

def Isomorphic (alg₁ alg₂ : Algebra Δ) : Prop :=
  Nonempty (Iso alg₁ alg₂)

infix:50 " ≅ " => Isomorphic

structure FreelyGenerated (alg : Algebra Δ) (gen : Set alg.carrier) (k : Set $ Algebra Δ) : Prop where
  mem : alg ∈ k
  generated : ∀ c, c ∈ closure gen alg.ops
  free : ∀ (alg' : Algebra Δ) (f : gen → alg'.carrier), (alg' ∈ k) → 
         ∃! hom : Hom alg alg', ∀ c : gen, f c = hom c
  
-- Note, we immediately restrict this definition to the set of all algebras,
-- as this is the only one we ever need.
noncomputable def FreelyGenerated.hom {alg : Algebra Δ} {H} 
  (h : FreelyGenerated alg H Set.univ) (target : Algebra Δ) (f : H → target.carrier) : 
  Hom alg target :=
  choose (h.free target f Set.mem_univ)

theorem FreelyGenerated.hom_extends (h : FreelyGenerated alg gen Set.univ) {f}: 
  ∀ c : gen, f c = (h.hom target f) c := 
  (choose_spec (h.free target f Set.mem_univ) |>.left ·)
  

-----------------------------------------------------------------------------------------


def BinOp.Associative (op : BinOp α) : Prop :=
  ∀ a b c, op (op a b) c = op a (op b c)

def BinOp.Commutative (op : BinOp α) : Prop :=
  ∀ a b, op a b = op b a

def BinOp.Idempotent (op : BinOp α) : Prop :=
  ∀ a, op a a = a

structure BinOp.Identity (op : BinOp α) (e : α) : Prop where
  left  : ∀ a, op e a = a
  right : ∀ a, op a e = a

theorem BinOp.Identity.unique (op : BinOp α) : (Identity op e) → (Identity op e') → e = e' := by
  intro h h'
  rw [←h'.left e, h.right e']

structure BinOp.Inverse (op : BinOp α) (a a' : α) : Prop where
  left  : ∀ {e}, (Identity op e) → op a a' = e
  right : ∀ {e}, (Identity op e) → op a' a = e

def BinOp.RightDistrib (mul add : BinOp α) : Prop :=
  ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)

def BinOp.LeftDistrib (mul add : BinOp α) : Prop :=
  ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

structure BinOp.Distrib (mul add : BinOp α) : Prop where
  right : RightDistrib mul add
  left : LeftDistrib mul add

structure Semigroup where
  carrier : Type
  op : BinOp carrier
  assoc : BinOp.Associative op

protected inductive Semigroup.Alphabet 
  | «⊙»

abbrev Semigroup.ranked : RankedAlphabet where
  alphabet := Semigroup.Alphabet
  rank | .«⊙» => 2
  isAlphabet := sorry

def Semigroup.algebra (s : Semigroup) : Algebra ranked where
  carrier := s.carrier
  θ | .«⊙» => s.op

structure Monoid extends Semigroup where
  id : Op carrier 0
  idIsIdentity : BinOp.Identity op id

protected inductive Monoid.Alphabet 
  | «⊙»
  | e

abbrev Monoid.ranked : RankedAlphabet where
  alphabet := Monoid.Alphabet
  rank 
    | .«⊙» => 2 
    | .e   => 0
  isAlphabet := sorry

def Monoid.algebra (m : Monoid) : Algebra Monoid.ranked where
  carrier := m.carrier
  θ 
    | .«⊙» => m.op 
    | .e   => m.id

def Monoid.Commutative (m : Monoid) : Prop :=
  BinOp.Commutative m.op

structure StrongBimonoid where
  carrier : Type
  add  : BinOp carrier
  mul  : BinOp carrier
  zero : Op carrier 0
  one  : Op carrier 0
  addComm : BinOp.Commutative add
  zeroNeOne : zero ≠ one
  leftAbsorption : ∀ c, mul zero c = zero
  rightAbsorption : ∀ c, mul c zero = zero

protected inductive StrongBimonoid.Alphabet 
  | «⊕»
  | «⊗»
  | «𝟘»
  | «𝟙»

abbrev StrongBimonoid.ranked : RankedAlphabet where
  alphabet := StrongBimonoid.Alphabet
  rank 
    | .«⊕» => 2
    | .«⊗» => 2
    | .«𝟘» => 0
    | .«𝟙» => 0
  isAlphabet := sorry

def StrongBimonoid.algebra (s : StrongBimonoid) : Algebra StrongBimonoid.ranked where
  carrier := s.carrier
  θ 
    | .«⊕» => s.add
    | .«⊗» => s.mul
    | .«𝟘» => s.zero
    | .«𝟙» => s.one

structure Semiring extends StrongBimonoid where
  distributive : BinOp.Distrib mul add


-----------------------------------------------------------------------------------------


namespace Term

inductive TermSymbol (Δ : RankedAlphabet) (H : Type)
  | alph (sym : Δ)
  | var (v : H)
  | «(»
  | «)»
  | «,»

-- Note, we have to use the raw representation of a vector for `v` here.
inductive _root_.Term (Δ : RankedAlphabet) (H : Type)
  | var (h : H)
  | app (σ : Δ) (v : Fin (Δ.rank σ) → (Term Δ H))

-- Note, we could replace this with a coercion from H to a set of terms,
-- but that would have to be a `CoeDep` which isn't reliable enough.
def Vars (Δ : RankedAlphabet) (H : Type) : Set (Term Δ H)
  | .var .. => True
  | .app .. => False

protected def algebra (Δ : RankedAlphabet) (H : Type) : Algebra Δ where
  carrier := Term Δ H
  θ := app

-- Implementation detail of `Term.algebraHom`.
private def algebraHomImpl (target : Algebra Δ) (f : Vars Δ H → target.carrier) : (Term.algebra Δ H).carrier → target.carrier
  | .var c => f ⟨.var c, by simp [Vars]⟩
  | .app σ cs => target.θ σ (algebraHomImpl target f $ cs ·)

-- Implementation detail of `Term.algebra_freelyGenerated`.
private def algebraHom (target : Algebra Δ) (f : Vars Δ H → target.carrier) : Hom (Term.algebra Δ H) target where
  hom := algebraHomImpl target f
  property := fun _ _ => by simp [algebraHomImpl, Function.comp]

-- Theorem 2.9.3
theorem algebra_freelyGenerated : FreelyGenerated (Term.algebra Δ H) (Vars Δ H) Set.univ where
  mem := Set.mem_univ
  generated := by
    intro c
    simp [closure]
    induction c
    case var h => 
      apply Closure.root 
      simp [Membership.mem, Vars]
    case app σ v hi =>
      refine Closure.app ?_ hi
      simp [Term.algebra, Algebra.ops, Membership.mem]
      exists σ, rfl
  free := by
    intro target f _
    simp [ExistsUnique]
    exists algebraHom target f
    constructor
    case left =>
      intro ⟨v, hv⟩
      cases v
      case app => contradiction
      case var => simp [algebraHom, algebraHomImpl]
    case right =>
      intro hom h
      apply Hom.ext
      funext c
      induction c
      case a.h.var => simp [algebraHom, algebraHomImpl, h _]
      case a.h.app σ cs hi =>
        simp [algebraHom, algebraHomImpl]
        have h := hom.property σ cs
        simp [Term.algebra] at h
        simp [h]
        congr
        funext i
        exact hi i

protected noncomputable def algebra.hom (target : Algebra Δ) (f : Vars Δ H → target.carrier) : 
  Hom (Term.algebra Δ H) target :=
  (algebra_freelyGenerated).hom target f

theorem algebra.hom_extends (target) (f : _ → target.carrier) : 
  ∀ v : Vars Δ H, f v = (Term.algebra.hom target f) v.val :=
  Term.algebra_freelyGenerated.hom_extends


-----------------------------------------------------------------------------------------


abbrev posAlgebra (Δ) : Algebra Δ where
  carrier := Set (Nat⋆)
  θ σ cs
    | .ε => True
    | i ⬝ tl => ∃ h : i < Δ.rank σ, tl ∈ cs ⟨i, h⟩
        
noncomputable def pos {Δ H} := 
  Term.algebra.hom (H := H) (posAlgebra Δ) (fun _ => Set.singleton .ε)

theorem pos_var : (@pos Δ H) (var v) = Set.singleton [] :=
  Eq.symm <| Term.algebra.hom_extends (posAlgebra Δ) (fun _ => Set.singleton .ε) ⟨var v, by simp [Vars]⟩

theorem pos_app (σ cs) : (@pos Δ H) (app σ cs) = 
  (fun | .ε => True | i ⬝ tl => ∃ h : i < Δ.rank σ, tl ∈ pos (cs ⟨i, h⟩)) :=
  pos.property σ cs

theorem pos_zero (h : Δ.rank σ = 0) : (@pos Δ H) (app σ $ Vector.ε' h) = Set.singleton .ε := by
  simp [pos_app (H := H) σ (Vector.ε' h)]
  refine Set.mem_ext ?_
  intro w
  constructor
  all_goals
    intro h'
    simp [Set.singleton, Membership.mem] at *
  case mpr => simp [h']
  case mp =>
    split at h'
    · rfl
    · have ⟨h', _⟩ := h'
      rw [h] at h'
      contradiction

theorem mem_pos : (i ⬝ w) ∈ (@pos Δ H) (app σ cs) → ∃ h : i < Δ.rank σ, (w ∈ pos (cs ⟨i, h⟩)) := by
  intro h
  rw [pos_app] at h
  simp [Membership.mem] at h
  exact h

theorem ε_mem_pos : .ε ∈ (@pos Δ H) ξ := by
  sorry

structure TP (Δ H) where
  ξ : Term Δ H
  w : { w // w ∈ pos ξ }

def label : TP Δ H → (Sum Δ H)
  | ⟨var v, _⟩ => .inr v
  | ⟨app σ _, ⟨.ε, _⟩⟩ => .inl σ
  | ⟨app σ ξs, ⟨i ⬝ w', h⟩⟩ => label { 
      ξ := ξs ⟨i, choose $ mem_pos h⟩, 
      w := ⟨w', choose_spec $ mem_pos h⟩
    }
termination_by label tp => tp.w.val.length

-- TODO: Figure out if this is ok.
notation ξ "°" w => Term.label (TP.mk ξ w)

def subtree : TP Δ H → Term Δ H
  | ⟨var v, _⟩ => var v
  | ⟨ξ, ⟨.ε, _⟩⟩ => ξ
  | ⟨app σ ξs, ⟨i ⬝ w', h⟩⟩ => subtree { 
      ξ := ξs ⟨i, choose $ mem_pos h⟩, 
      w := ⟨w', choose_spec $ mem_pos h⟩
    }
termination_by subtree tp => tp.w.val.length

-- TODO: Figure out if this is ok.
notation ξ "∣" w => Term.subtree (TP.mk ξ w)

def replacement (tp : TP Δ H) (ζ : Term Δ H) : Term Δ H :=
  match tp with
  | ⟨var _, _⟩ | ⟨_, ⟨.ε, _⟩⟩ => ζ
  | ⟨app σ ξs, ⟨i ⬝ w', h⟩⟩ => 
    let tp' := { ξ := ξs ⟨i, choose $ mem_pos h⟩, w := ⟨w', choose_spec $ mem_pos h⟩ }
    app σ (fun j => if i = j then replacement tp' ζ else ξs j)
termination_by replacement tp _ => tp.w.val.length

-- TODO: Figure out if this is ok.
notation ξ "[" ζ "]" w => Term.replacement (TP.mk ξ w) ζ

end Term


-----------------------------------------------------------------------------------------


def RankedAlphabet.lift (Γ : Type) [Alphabet Γ] : RankedAlphabet where
  alphabet := Option Γ
  rank
    | some _ => 1
    | none => 0
  isAlphabet := {
    nonempty := inferInstance
    finite := sorry
  }

def stringAlgebra (Γ : Type) [Alphabet Γ] : Algebra (RankedAlphabet.lift Γ) where
  carrier := (Γ⋆)
  θ 
    | some σ => fun ws => σ ⬝ (ws ⟨0, by simp [RankedAlphabet.lift]⟩)
    | none => fun _ => .ε

def treeₑ [Alphabet Γ] : Γ⋆ → Term (RankedAlphabet.lift Γ) Empty
  | .ε => (Term.algebra (RankedAlphabet.lift Γ) Empty).θ none (nomatch ·) 
  | σ⬝w => .app (some σ) (fun _ => treeₑ w)

theorem Term.algebra_iso_stringAlgebra (Γ : Type) [Alphabet Γ] : 
  Isomorphic (stringAlgebra Γ) (Term.algebra (RankedAlphabet.lift Γ) Empty) := by
  unfold Isomorphic
  apply Nonempty.intro
  exact {
    hom := treeₑ
    property := by
      intro σ w
      cases σ
      all_goals simp [Term.algebra, stringAlgebra]
      case none =>
        simp [Function.comp, treeₑ, Term.algebra]
        funext ⟨_, h⟩
        simp [RankedAlphabet.lift] at h
        contradiction
      case some σ =>
        simp [stringAlgebra, RankedAlphabet.lift] at w
        generalize hw : w ⟨0, stringAlgebra.proof_1⟩ = w'
        simp [treeₑ, Function.comp]
        funext ⟨i, hi⟩
        have hi : i = 0 := by 
          simp [RankedAlphabet.lift] at hi
          cases i
          case zero => rfl
          case succ => contradiction
        simp [hw, hi]
    bij := {
      inj := by 
        simp [Function.Injective]
        intro σ₁ σ₂ h
        induction σ₁ generalizing σ₂ <;> cases σ₂ <;> simp [treeₑ, Term.algebra] at *
        case cons.cons σ _ hi _ _ =>
          have ⟨h₁, h₂⟩ := h
          injection h₁ with h₁          
          have : Nonempty (Fin $ (RankedAlphabet.lift Γ).rank $ some σ) := 
            .intro ⟨0, by simp [RankedAlphabet.lift]⟩ 
          simp [h₁, hi _ (const_func_ext h₂)]
      surj := by
        simp [Function.Surjective]
        intro a
        induction a
        case var => contradiction
        case app σ w hi =>
          cases σ 
          case none => 
            exists .ε
            simp [treeₑ, Term.algebra]
            funext ⟨_, h⟩
            simp [RankedAlphabet.lift] at h
            contradiction
          case some σ => 
            have ⟨a, h⟩ := hi ⟨0, by simp [RankedAlphabet.lift]⟩
            exists σ⬝a
            simp [h, treeₑ]
            refine congrArg _ ?_
            funext ⟨i, hi⟩
            have hi : i = 0 := by 
              simp [RankedAlphabet.lift] at hi
              cases i
              case zero => rfl
              case succ => contradiction
            simp [hi]
    }
  }

-----------------------------------------------------------------------------------------


-- TODO: Change W to be a Finset.
structure TreeDomain (W : Set (Nat⋆)) : Prop where
  nonempty : Set.Nonempty W
  prefixClosed : Set.bUnion (Set.image Word.prefixes) ⊆ W
  leftClosed : ∀ u i, (u•i ∈ W) → u•(i - 1) ∈ W

theorem TreeDomain.ε_mem : TreeDomain W → .ε ∈ W := by
  intro h
  apply h.prefixClosed .ε
  simp [Set.bUnion, Membership.mem]
  have ⟨m, _⟩ := Set.Nonempty.iff_exists_mem.mp h.nonempty
  exists m.prefixes
  constructor
  case left => exists m
  case right => apply Word.ε_mem_prefixes

theorem Term.pos_treeDomain (ξ : Term Δ H) : TreeDomain (pos ξ) where
  nonempty := Set.Nonempty.iff_exists_mem.mpr ⟨_, Term.ε_mem_pos⟩
  prefixClosed := sorry
  leftClosed := sorry

-- TEMPORARY
def Set.size : Set α → Nat := sorry

structure TreeMapping {Δ : RankedAlphabet} {W : Set (Nat⋆)} (t : W → Δ) where
  domain : TreeDomain W
  rankPreservation : ∀ w, Set.size (fun j => w.val•j ∈ W) = Δ.rank (t w)
