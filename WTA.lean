open Classical

def Vector (α : Type) (n : Nat) := Fin n → α  

def Vector.empty : Vector α 0 := (nomatch ·)

def Vector.empty' (h : n = 0) : Vector α n := 
  fun ⟨_, h'⟩ => by simp [h] at h'; contradiction

def Vector.prefix (v : Vector α (n + 1)) : Vector α n := 
  fun i => v ⟨i.val, Nat.lt_succ_of_le $ Nat.le_of_lt i.isLt⟩

def Vector.list : {n : Nat} → Vector α n → List α
  | 0,     _ => []
  | n + 1, v => v.prefix.list ++ [v ⟨n, Nat.lt_succ_self _⟩]

def Vector.all (v : Vector α n) (p : α → Prop) : Prop :=
  ∀ i, p (v i)

def Vector.map (v : Vector α n) (f : α → β) : Vector β n := 
  (f $ v ·)

abbrev Op (α : Type) (arity : Nat) := (Vector α arity) → α

instance : CoeHead (Op α 0) α where
  coe op := op Vector.empty

abbrev BinOp (α : Type) := α → α → α

instance : Coe (Op α 2) (BinOp α) where
  coe op a₁ a₂ := op fun | 0 => a₁ | 1 => a₂

instance : CoeTail (BinOp α) (Op α 2) where
  coe op as := op (as 0) (as 1)

-- < Mathlib 4
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

abbrev Set.univ : Set α := fun _ => True

abbrev Set.singleton (a : α) : Set α := (· = a)

theorem Set.mem_univ : a ∈ Set.univ := .intro

def Set.image (f : α → β) : Set β := 
  (∃ a, f a = ·)

theorem Set.mem_image_iff : (b ∈ Set.image f) ↔ (∃ a, f a = b) := ⟨id, id⟩

theorem Set.image_choose {b : β} : (h : b ∈ Set.image f) → (f $ choose h) = b :=
  choose_spec

def Set.union (s₁ s₂ : Set α) := fun a => a ∈ s₁ ∨ a ∈ s₂

theorem Set.mem_ext {s₁ s₂ : Set α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  fun h => funext (fun a => propext (h a))

abbrev Vector.lift {s : Set α} (v : Vector s n) : Vector α n := (v ·)

-- Mathlib 4 >

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

theorem Algebra.closed (alg : Algebra Δ) : Closed alg Set.univ := by
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

abbrev Pos := List Nat

abbrev Pos.ε : Pos := []

infixl:50 " ⬝ " => List.cons

abbrev posAlgebra (Δ) : Algebra Δ where
  carrier := Set Pos
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

theorem pos_zero (h : Δ.rank σ = 0) : (@pos Δ H) (app σ $ Vector.empty' h) = Set.singleton .ε := by
  simp [pos_app (H := H) σ (Vector.empty' h)]
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

structure TP (Δ H) where
  ξ : Term Δ H
  w : { w // w ∈ pos ξ }

-- TODO: How should vars be handled?
def label : TP Δ H → Δ 
  | ⟨var v, _⟩ => sorry
  | ⟨app σ ξs, ⟨.ε, _⟩⟩ => σ
  | ⟨app σ ξs, ⟨i ⬝ w', h⟩⟩ => label { 
      ξ := ξs ⟨i, choose $ mem_pos h⟩, 
      w := ⟨w', choose_spec $ mem_pos h⟩
    }
termination_by label tp => tp.w.val.length

-- TODO: Figure out if this is ok.
notation ξ "(" w ")" => Term.label (TP.mk ξ w)

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
