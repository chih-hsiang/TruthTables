import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Nat public
  using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Nat public
  using (_+_; _*_) renaming (_-_ to _∸_)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-distribˡ-+)
open import Data.Nat using (ℕ; _≤_; s≤s; z≤n; _<_)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Function using (_∘_)
open import Data.List using (List; []; _∷_ ; _++_; length; reverse; map; foldr; downFrom)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Data.Vec.Base using (Vec; _[_]=_; _++_)

variable A B C : Set

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

×-proj-eq : {a a₁ : A} → {P : A → Set} → a ≡ a₁ → P a ≡ P a₁ → ⟨ a , P a ⟩ ≡ ⟨ a₁ , P a₁ ⟩
×-proj-eq refl refl = refl

-- Σ-proj-eq : {P : A → Set} → (a b : Σ A P) → (proj₁ a ≡ proj₁ b) → (proj₂ a ≡ proj₂ b) → a ≡ b
-- Σ-proj-eq a b e1 e2 = ?

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

-- create a truth table, and consider a transition from circuit to truth table

predℕ : ℕ → ℕ 
predℕ zero = zero
predℕ (suc n) = n

ℕ-∸ : (n : ℕ) → n ∸ n ≡ zero
ℕ-∸ zero = refl
ℕ-∸ (suc n) = ℕ-∸ n

ℕ-∸-suc : (n : ℕ) → (suc n) ∸ n ≡ suc zero
ℕ-∸-suc zero = refl
ℕ-∸-suc (suc n) = ℕ-∸-suc n

≤-ref : (n : ℕ) → n ≤ n
≤-ref zero = z≤n
≤-ref (suc n) = s≤s (≤-ref n)

-- ℕ-∸-suc-mn : (m n : ℕ) → n ≤ m → ∃[ x ] ((suc m) ∸ n ≡ suc x)
-- ℕ-∸-suc-mn m zero le = ⟨ m , refl ⟩
-- ℕ-∸-suc-mn (suc m) (suc n) (s≤s le) = ⟨ (proj₁ (ℕ-∸-suc-mn m n le)) , (proj₂ (ℕ-∸-suc-mn m n le)) ⟩

ℕ-∸-suc-mn : (m n : ℕ) → n ≤ m → suc m ∸ n ≡ suc (m ∸ n)
ℕ-∸-suc-mn m zero le = refl
ℕ-∸-suc-mn (suc m) (suc n) (s≤s le) = ℕ-∸-suc-mn m n le

+-l-zero : (m : ℕ) → m + zero ≡ m
+-l-zero zero = refl
+-l-zero (suc m) = Eq.cong suc (+-l-zero m)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

_^_ : ℕ → ℕ → ℕ
n ^ zero = suc(zero)
n ^ suc(m) = n * (n ^ m)

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- variable l : ℕ

data Table : ℕ → Set where
    decision : {l : ℕ} → (Table l) → (Table l) → (Table (suc l))
    output : Bool → Table 0


-- data Maybe A : Set where
--     Just : (a : A) → Maybe A
--     Nothing : Maybe A

-- _>>=_ : Maybe A → (A → Maybe B) → Maybe B
-- Just a >>= f = f a
-- Nothing >>= f = Nothing


-- BinLength : Bin → ℕ
-- BinLength ⟨⟩ = 0
-- BinLength (b O) = suc (BinLength b)
-- BinLength (b I) = suc (BinLength b)
 

-- ReadTable : Table l → (b : Bin) → Maybe(Table (l ∸ BinLength b))
-- ReadTable t ⟨⟩ = Just t 
-- ReadTable (decision t t₁) (b O) = ReadTable t b
-- ReadTable (output x) (b O) = Nothing
-- ReadTable (decision t t₁) (b I) = ReadTable t₁ b
-- ReadTable (output x) (b I) = Nothing

-- ReadOutput_help : Table l → Maybe Bool
-- ReadOutput_help (decision t t₁) = Nothing
-- ReadOutput_help (output x) = Just x

-- ReadOutput : Table l → (b : Bin) → Maybe Bool
-- ReadOutput t b = (ReadTable t b) >>= ReadOutput_help

translate₁ : (Bool → Bool) → Table 1
translate₁ f = decision (output (f false)) (output (f true))

translate₂ : (Bool → Bool → Bool) → Table 2
translate₂ f = decision (translate₁ (f false)) (translate₁ (f true))

data Bool_func : ℕ → Set where
    const : Bool → Bool_func 0
    input : {n : ℕ} → (Bool → Bool_func n) → Bool_func (suc n)
    
    -- AND : {n : ℕ} → Bool_func n → Bool_func n → Bool_func n

-- translateₙ : (n : ℕ) → Bool_func n → Table n
-- translateₙ zero (const x) = output x
-- translateₙ (suc n) (input g) = decision (translateₙ n (g false)) (translateₙ n (g true))

translateₙ : {n : ℕ} → Bool_func n → Table n
translateₙ (const x) = output x
translateₙ (input g) = decision (translateₙ (g false)) (translateₙ (g true))

-- detranslate : (n : ℕ) → Table n → Bool_func n
-- detranslate (suc n) (decision t t₁) = input (λ {false → detranslate n t
--                                       ; true → detranslate n t₁})
-- detranslate zero (output x) = const x

detranslate : {n : ℕ} → Table n → Bool_func n
detranslate (decision t t₁) = input (λ {false → detranslate t
                                      ; true → detranslate t₁})
detranslate (output x) = const x

func_≃ : (n : ℕ) → Bool_func n ≃ Table n
func zero ≃ = record { to = translateₙ ; from = detranslate ; from∘to = λ {(const x) → refl} ; to∘from = λ {(output x) → refl} }
func suc n ≃ = record { 
  to = translateₙ ; 
  from = detranslate ; 
  from∘to = from∘to_helper (suc n) ; 
  to∘from = to∘from_helper (suc n) }
  where
  from∘to_helper : (n : ℕ) → (x : Bool n func) → detranslate (translateₙ (x)) ≡ x
  from∘to zero helper (const x) = refl
  from∘to suc n helper (input x) = Eq.cong input (extensionality (λ {false → from∘to_helper n (x false)
                                                                   ; true → from∘to_helper n (x true)}))
  to∘from_helper : (n : ℕ) → (x : Table n) → translateₙ (detranslate (x)) ≡ x
  to∘from zero helper (output x) = refl
  to∘from suc n helper (decision x x₁) = Eq.cong₂ decision (to∘from_helper n x) (to∘from_helper n x₁)

-- func_≃ : {n : ℕ} → Bool_func n ≃ Table n
-- func_≃ = record { 
--   to = translateₙ ; 
--   from = detranslate ; 
--   from∘to = {!   !} ; 
--   to∘from = {!   !} }
--   where
--   from∘to_helper : (n : ℕ) → (x : Bool n func) → detranslate (translateₙ (x)) ≡ x
--   from∘to zero helper (const x) = refl
--   from∘to suc n helper (input x) = Eq.cong input (extensionality (λ {false → from∘to_helper n (x false)
--                                                                    ; true → from∘to_helper n (x true)}))

func-table-≃ : {n : ℕ} → Bool_func n ≃ Table n
func-table-≃ {n} = record { 
  to = translateₙ ; 
  from = detranslate ; 
  from∘to = from∘to_helper n ; 
  to∘from = to∘from_helper n }
  where
  from∘to_helper : (n : ℕ) → (x : Bool n func) → detranslate (translateₙ (x)) ≡ x
  from∘to zero helper (const x) = refl
  from∘to suc n helper (input x) = Eq.cong input (extensionality (λ {false → from∘to_helper n (x false)
                                                                   ; true → from∘to_helper n (x true)}))
  to∘from_helper : (n : ℕ) → (x : Table n) → translateₙ (detranslate (x)) ≡ x
  to∘from zero helper (output x) = refl
  to∘from suc n helper (decision x x₁) = Eq.cong₂ decision (to∘from_helper n x) (to∘from_helper n x₁)

-- Q : how to translate a truth table into a quantifiable index?

ANDfunc : Bool_func 2
ANDfunc = input (λ x → input (λ y → const( x ∧ y)))

ORfunc : Bool_func 2
ORfunc = input (λ x → input (λ y → const( x ∨ y)))

2infuc : (Bool → Bool → Bool) → Bool_func 2
2infuc f = input (λ x → input (λ y → const (f x y)))

-- don't care : min 0 1
-- Set all the (normal) boolean circuit as the same?

func_AND : {n : ℕ} → Bool_func n → Bool_func n → Bool_func n
func const x AND (const y) = const (x ∧ y) 
func input x AND (input y) = input (λ b → func (x b) AND (y b))
  
Table_AND : {n : ℕ} → Table n → Table n → Table n
Table decision s s₁ AND (decision t t₁) = decision (Table_AND s t) (Table_AND s₁ t₁)
Table output x AND (output x₁) = output (x ∧ x₁)

AND_eq_table : {n : ℕ} → (x : Bool_func n) → (y : Bool_func n) → (translateₙ {n} (func_AND {n} x y)) ≡ Table_AND {n} (translateₙ x) (translateₙ y)
AND const x eq const x₁ table = refl 
AND input x eq input x₁ table = Eq.cong₂ decision AND (x false) eq (x₁ false) table AND (x true) eq (x₁ true) table

AND_eq_func : {n : ℕ} → (x : Table n) → (y : Table n) → (detranslate {n} (Table_AND {n} x y)) ≡ func_AND {n} (detranslate x) (detranslate y)
AND decision x x₁ eq decision y y₁ func = Eq.cong input (extensionality (λ {false → AND_eq_func x y
                                                                          ; true → AND_eq_func x₁ y₁}))
AND output x eq output x₁ func = refl

func_NOT : {n : ℕ} → Bool_func n → Bool_func n
func const x NOT = const (not x) 
func input x NOT = input (λ b → func (x b) NOT)

Table_NOT : {n : ℕ} → Table n → Table n
Table decision t t₁ NOT = decision (Table_NOT t) (Table_NOT t₁)
Table output x NOT = output (not x)

NOT_eq_table : {n : ℕ} → (x : Bool_func n) → (translateₙ {n} (func_NOT {n} x)) ≡ Table_NOT {n} (translateₙ x)
NOT_eq_table (const x) = refl
NOT_eq_table (input x) = Eq.cong₂ decision (NOT_eq_table (x false)) (NOT_eq_table (x true))

NOT_eq_func : {n : ℕ} → (x : Table n) → (detranslate {n} (Table_NOT {n} x)) ≡ func_NOT {n} (detranslate x)
NOT_eq_func (decision x x₁) = Eq.cong input (extensionality (λ {false → NOT_eq_func x
                                                              ; true → NOT_eq_func x₁}))
NOT_eq_func (output x) = refl

Table_OR : {n : ℕ} → Table n → Table n → Table n
Table decision s s₁ OR (decision t t₁) = decision (Table_OR s t) (Table_OR s₁ t₁)
Table output x OR (output x₁) = output (x ∨ x₁)

-- data Σ (A : Set) (B : A → Set) : Set where
--   ⟨_,_⟩ : (x : A) → B x → Σ A B

-- Σ-syntax = Σ
-- infix 2 Σ-syntax
-- syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

-- ∃ : ∀ {A : Set} (B : A → Set) → Set
-- ∃ {A} B = Σ A B

-- ∃-syntax = ∃
-- syntax ∃-syntax (λ x → B) = ∃[ x ] B

general_eq_table : (n : ℕ) → (f : Bool_func n → Bool_func n) → ∃[ g ] (translateₙ ∘ f ≡ g ∘ translateₙ )
general zero eq f table = ⟨ (λ {(output x) → translateₙ (f (const x))}) , extensionality (λ {(const x) → refl}) ⟩
general suc n eq f table = ⟨ (λ y → translateₙ (f (detranslate y))) , 
                             extensionality (λ x → Eq.cong translateₙ (Eq.cong f (Eq.sym (from∘to func suc n ≃ x)))) ⟩
  where
  helper : (n : ℕ) → (f : Bool_func n → Bool_func n) →  ∃[ g ] (translateₙ ∘ f ≡ g ∘ translateₙ) → (Table n → Table n)
  helper n f ⟨ g , eq ⟩ = g
  -- choose-0 : {n : ℕ} → Bool_func (suc n) → Bool_func n
  -- choose-0 (input x) = x false 
  -- helper-f-0 : (n : ℕ) → (f : Bool_func (suc n) → Bool_func (suc n)) → (Bool_func n → Bool_func n)
  -- helper-f-0 n f = λ x → choose-0 (f (input (λ b → x)))
  -- choose-1 : {n : ℕ} → Bool_func (suc n) → Bool_func n
  -- choose-1 (input x) = x true
  -- helper-f-1 : (n : ℕ) → (f : Bool_func (suc n) → Bool_func (suc n)) → (Bool_func n → Bool_func n)
  -- helper-f-1 n f = λ x → choose-1 (f (input (λ b → x)))


-- encode₀ : Bool → Bool_func 0
-- encode₀ b = const b

-- encode₁ : (Bool → Bool) → Bool_func 1
-- encode₁ f = input (λ x → encode₀ (f x))

-- encode₂ : (Bool → Bool → Bool) → Bool_func 2
-- encode₂ f = input (λ x → encode₁ (f x))

-- decode₀ : Bool_func 0 → Bool
-- decode₀ (const x) = x

-- decode₁ : Bool_func 1 → (Bool → Bool)
-- decode₁ (input x) = λ b → decode₀ (x b)

-- decode₂ : Bool_func 2 → (Bool → Bool → Bool)
-- decode₂ (input x) = λ b → decode₁ (x b)

-- bi-compose : (m n : ℕ) → Bool_func m → Bool_func n → Bool_func 2 → Bool_func (m + n)
-- bi-compose zero zero (const x) (const x₁) a = const ((decode₂ a) x x₁)
-- bi-compose zero (suc n) f (input x) a = input (λ b → bi-compose zero n f (x b) a)
-- bi-compose (suc m) n (input x) g a = input (λ b → bi-compose m n (x b) g a)

-- bi-compose-free : {m n : ℕ} → Bool_func m → Bool_func n → Bool_func 2 → Bool_func (m + n)
-- bi-compose-free {m} {n} f g a = bi-compose m n f g a

Const1 : Bool_func 0
Const1 = const true

-- C1-left-AND-id : {n : ℕ} → (f : Bool_func n) → (bi-compose-free Const1 f ANDfunc) ≡ f
-- C1-left-AND-id (const x) = refl
-- C1-left-AND-id (input x) = Eq.cong input (extensionality (λ {b → C1-left-AND-id (x b)}))

n+0-funceq : {n : ℕ} → Bool_func (n + 0) ≃ Bool_func n
n+0-funceq {n} = record { to = funceq-to n ; from = funceq-from n ; from∘to = funceq-from∘to n ; to∘from = funceq-to∘from n }
  where
  funceq-to : (n : ℕ) → Bool_func (n + 0) → Bool_func n
  funceq-to zero f = f
  funceq-to (suc n) (input x) = input (λ b → funceq-to n (x b))
  funceq-from : (n : ℕ) → Bool_func n → Bool_func (n + 0)
  funceq-from zero f = f
  funceq-from (suc n) (input x) = input (λ b → funceq-from n (x b))
  funceq-from∘to : (n : ℕ) → (x : Bool_func (n + 0)) → funceq-from n (funceq-to n x) ≡ x
  funceq-from∘to zero (const x) = refl
  funceq-from∘to (suc n) (input x) = Eq.cong input (extensionality (λ b → funceq-from∘to n (x b)))
  funceq-to∘from : (n : ℕ) → (y : Bool n func) → funceq-to n (funceq-from n y) ≡ y
  funceq-to∘from zero (const x) = refl
  funceq-to∘from (suc n) (input x) = Eq.cong input (extensionality (λ b → funceq-to∘from n (x b)))
  
const-Table : (n : ℕ) → Bool → Table n
const-Table zero b = output b
const-Table (suc n) b = decision (const-Table n b) (const-Table n b)

const-Table-NOT : (n : ℕ) → (b : Bool) → Table (const-Table n b) NOT ≡ const-Table n (not b)
const-Table-NOT zero b = refl
const-Table-NOT (suc n) b = Eq.cong₂ decision (const-Table-NOT n b) (const-Table-NOT n b)

∧-rightid : (b : Bool) → b ∧ true ≡ b
∧-rightid false = refl
∧-rightid true = refl

∧-rightfalse : (b : Bool) → b ∧ false ≡ false
∧-rightfalse false = refl
∧-rightfalse true = refl

∨-righttrue : (b : Bool) → b ∨ true ≡ true
∨-righttrue false = refl
∨-righttrue true = refl

-- C1-right-AND-id : {n : ℕ} → (f : Bool_func n) → to n+0-funceq (bi-compose-free f Const1 ANDfunc) ≡ f
-- C1-right-AND-id (const x) = Eq.cong const (∧-rightid x)
-- C1-right-AND-id (input x) = Eq.cong input (extensionality (λ b → C1-right-AND-id (x b)))

C1-Table-right-OR : {n : ℕ} → (s : Table n) → Table s OR (const-Table n true) ≡ (const-Table n true)
C1-Table-right-OR (decision s s₁) = Eq.cong₂ decision (C1-Table-right-OR s) (C1-Table-right-OR s₁)
C1-Table-right-OR (output x) = Eq.cong output (∨-righttrue x)

C1-Table-right-AND : {n : ℕ} → (s : Table n) → Table s AND (const-Table n true) ≡ s
C1-Table-right-AND (decision s s₁) = Eq.cong₂ decision (C1-Table-right-AND s) (C1-Table-right-AND s₁)
C1-Table-right-AND (output x) = Eq.cong output (∧-rightid x)

C0-Table-right-AND : {n : ℕ} → (s : Table n) → Table s AND (const-Table n false) ≡ const-Table n false
C0-Table-right-AND (decision s s₁) = Eq.cong₂ decision (C0-Table-right-AND s) (C0-Table-right-AND s₁)
C0-Table-right-AND (output x) = Eq.cong output (∧-rightfalse x)

data L3 : Set where
    true : L3
    dcare : L3
    false : L3


insert-table : {n : ℕ} → (m : ℕ) → Bool → Table n → Table n
insert-table zero false (decision t t₁) = decision t t
insert-table zero true (decision t t₁) = decision t₁ t₁
insert-table (suc m) b (decision t t₁) = decision (insert-table m b t) (insert-table m b t₁)
insert-table m b (output x) = output x


data literal : Set where
  pos : ℕ → literal
  neg : ℕ → literal

-- data List (A : Set) : Set where
--   []  : List A
--   _∷_ : A → List A → List A

-- data l-order : literal → literal → Set where
--   pos-pos : {x y : ℕ} → (x ≤ y) → l-order (pos x) (pos y)
--   pos-neg : {x y : ℕ} → (x ≤ y) → l-order (pos x) (neg y)
--   neg-pos : {x y : ℕ} → (x ≤ y) → l-order (neg x) (pos y)
--   neg-neg : {x y : ℕ} → (x ≤ y) → l-order (neg x) (neg y)


-- data term : (n : ℕ) → (List literal) → Set where
--   triv : {n : ℕ} → term n []
--   first : {n : ℕ} → (x : literal) → term n (x ∷ [])
--   next : {n : ℕ} →  {L : List literal} → (x y : literal) → l-order x y → term n (y ∷ (x ∷ L))

data term : Set where
  ∅ : term
  _＆_ : term → literal → term

data DNF : Set where
  const0 : DNF
  _＋_ : DNF → term → DNF

  -- terms : term → DNF

-- term-table : {n : ℕ} → {L : List literal} → term n L → Table n
-- term-table te = {!   !}

-- const-Table : (n : ℕ) → Bool → Table n
-- const-Table zero b = output b
-- const-Table (suc n) b = decision (const-Table n b) (const-Table n b)

-- term-table : (n : ℕ) → term → Table n
-- term-table n ∅ = const-Table n true
-- term-table n (te ＆ pos x) = insert-table x true (term-table n te)
-- term-table n (te ＆ neg x) = insert-table x false (term-table n te)

lit-table : (n : ℕ) → literal → Table n
lit-table zero lit = output true
lit-table (suc n) (pos zero) = decision (const-Table n false) (const-Table n true)
lit-table (suc n) (pos (suc x)) = decision (lit-table n (pos x)) (lit-table n (pos x))
lit-table (suc n) (neg zero) = decision (const-Table n true) (const-Table n false)
lit-table (suc n) (neg (suc x)) = decision (lit-table n (neg x)) (lit-table n (neg x))

-- lit-table : (n : ℕ) → literal → Table n
-- lit-table'' zero lit = output true
-- lit-table'' (suc n) (pos zero) = output true
-- lit-table'' (suc n) (pos (suc x)) = decision (lit-table n (pos x)) (lit-table n (pos x))
-- lit-table'' (suc n) (neg zero) = output true
-- lit-table'' (suc n) (neg (suc x)) = decision (lit-table n (neg x)) (lit-table n (neg x))

lit-table' : (n : ℕ) → literal → Table n
lit-table' n (pos x) = lit-table n (pos (n ∸ suc x))
lit-table' n (neg x) = lit-table n (neg (n ∸ suc x))

term-table' : (n : ℕ) → term → Table n
term-table' n ∅ = const-Table n true
term-table' n (te ＆ x) = Table (term-table' n te) AND (lit-table' n x)

-- term-table' : (n : ℕ) → term → Table n
-- term-table' n ∅ = const-Table n true
-- term-table' n (te ＆ x) = Table (term-table' n te) AND (lit-table' n x)

clause-reverse : term → term
clause-reverse te = reverse-helper te ∅
  where
    reverse-helper : term → term → term
    reverse-helper ∅ b = b
    reverse-helper (a ＆ x) b = reverse-helper a (b ＆ x)

term-descend : term → term
term-descend ∅ = ∅
term-descend (te ＆ pos zero) = term-descend te
term-descend (te ＆ pos (suc x)) = (term-descend te) ＆ pos x
term-descend (te ＆ neg zero) = term-descend te
term-descend (te ＆ neg (suc x)) = (term-descend te) ＆ neg x

term-ascend : term → term
term-ascend ∅ = ∅
term-ascend (te ＆ pos n) = (term-ascend te) ＆ pos (suc n)
term-ascend (te ＆ neg n) = (term-ascend te) ＆ neg (suc n)

--reconstruct term table
term-table'' : (n : ℕ) → term → Table n
term-table'' n te = tt-helper'' n te
  where
    tt-helper'' : (n : ℕ) → term → Table n
    tt-helper'' zero te = output true
    tt-helper'' (suc n) ∅ = const-Table (suc n) true
    tt-helper'' (suc n) (te ＆ pos zero) = decision (const-Table n false) (tt-helper'' n (term-descend te))
    tt-helper'' (suc n) (te ＆ pos (suc x)) = decision (tt-helper'' n ((term-descend te) ＆ pos x)) ((tt-helper'' n ((term-descend te) ＆ pos x)))
    tt-helper'' (suc n) (te ＆ neg zero) = decision (tt-helper'' n (term-descend te)) (const-Table n false)
    tt-helper'' (suc n) (te ＆ neg (suc x)) = decision ((tt-helper'' n ((term-descend te) ＆ neg x))) ((tt-helper'' n ((term-descend te) ＆ neg x)))

term-table''-zero : (x : term) → term-table'' 0 x ≡ output true
term-table''-zero ∅ = refl
term-table''-zero (x ＆ x₁) = refl

DNF-table : (n : ℕ) → DNF → Table n
DNF-table n const0 = const-Table n false
DNF-table n (C ＋ x) = Table (DNF-table n C) OR (term-table' n x)
-- DNF-table n (terms x) = term-table' n x

DNF-test : DNF-table 2 ((const0 ＋ (∅ ＆ (pos 0))) ＋ (∅ ＆ (pos 1))) ≡ translateₙ ORfunc
DNF-test = refl

DNF-AIG-cost : DNF → ℕ
DNF-AIG-cost const0 = 0
DNF-AIG-cost (C ＋ ∅) = DNF-AIG-cost C + 1
DNF-AIG-cost (C ＋ (x ＆ x₁)) = DNF-AIG-cost (C ＋ x) + 1

Table_IMP : {n : ℕ} → Table n → Table n → Table n
Table decision t₁ t₂ IMP (decision t₃ t₄) = decision (Table t₁ IMP t₃) (Table t₂ IMP t₄)
Table output x IMP (output x₁) = output( (not x) ∨ x₁ )

-- clhelper : (n : ℕ) → List term → List term
-- clhelper n [] = (∅ ＆ pos n) ∷ (∅ ＆ neg n ∷ [])
-- clhelper n (x ∷ l) = (x ＆ pos n) ∷ (x ＆ neg n ∷ (x ∷ (clhelper n l)))

-- clauses : (n : ℕ) → List term
-- clauses zero = []
-- clauses (suc n) = clhelper n (clauses n)

clhelper : (n : ℕ) → List term → List term
clhelper n [] = []
clhelper n (x ∷ l) = (x ＆ pos n) ∷ (x ＆ neg n ∷ (x ∷ (clhelper n l)))

clauses : (n : ℕ) → List term
clauses zero = ∅ ∷ []
clauses (suc n) = clhelper n (clauses n)

clauses' : (n : ℕ) → List term
clauses' n = map clause-reverse (clauses n)

List-length : {A : Set} → List A → ℕ
List-length l = foldr (λ x n → suc n) 0 l

-- cl-test-r-helper : (n : ℕ) → (l : List term) → List-length (clhelper n l) ≡ 3 * (List-length l) + 2
-- cl-test-r-helper n [] = refl
-- cl-test-r-helper n (x ∷ l) = 
--   begin
--     List-length ((x ＆ pos n) ∷ (x ＆ neg n) ∷ x ∷ clhelper n l)
--     ≡⟨ refl ⟩
--     3 + List-length (clhelper n l)
--     ≡⟨ Eq.cong suc (Eq.cong suc (Eq.cong suc (cl-test-r-helper n l))) ⟩
--     3 + (3 * (List-length l) + 2)
--     ≡⟨ Eq.cong (_+ (3 * (List-length l) + 2)) (Eq.sym (+-identityʳ 3)) ⟩
--     (3 * 1) + (3 * List-length l + 2)
--     ≡⟨ Eq.sym (+-assoc (3 * 1) (3 * List-length l) 2) ⟩
--     (3 * 1 + 3 * List-length l) + 2
--     ≡⟨ Eq.cong (_+ 2) (Eq.sym (*-distribˡ-+ 3 1 (List-length l))) ⟩
--     (3 * (1 + List-length l)) + 2
--     ≡⟨ refl ⟩
--     (3 * (List-length (x ∷ l)) + 2)
--     ∎

cl-test-r-helper : (n : ℕ) → (l : List term) → List-length (clhelper n l) ≡ 3 * (List-length l)
cl-test-r-helper n [] = refl
cl-test-r-helper n (x ∷ l) = 
  begin
    List-length ((x ＆ pos n) ∷ (x ＆ neg n) ∷ x ∷ clhelper n l)
    ≡⟨ refl ⟩
    3 + List-length (clhelper n l)
    ≡⟨ Eq.cong suc (Eq.cong suc (Eq.cong suc (cl-test-r-helper n l))) ⟩
    3 + (3 * (List-length l))
    ≡⟨ Eq.cong (_+ (3 * (List-length l))) (Eq.sym (+-identityʳ 3)) ⟩
    (3 * 1) + (3 * List-length l)
    ≡⟨ (Eq.sym (*-distribˡ-+ 3 1 (List-length l))) ⟩
    (3 * (1 + List-length l))
    ≡⟨ refl ⟩
    (3 * (List-length (x ∷ l)))
    ∎


-- ≡⟨ Eq.trans (Eq.sym (+-assoc 3 (3 * (List-length l)) 2)) ({!   !}) ⟩
-- 3 + 3 * List-length l + 2 ≡ 3 * (1 + List-length l) + 2

cl-test-r : {n : ℕ} → List-length (clauses (suc n)) ≡ 3 * List-length (clauses n)
cl-test-r {n} = cl-test-r-helper n (clauses n)

List-filter : {A : Set} → List A → (A → Bool) → List A
List-filter [] P = []
List-filter (x ∷ l) P = List-filter-helper (x ∷ l) P (P x)
  where
    List-filter-helper : {A : Set} → List A → (A → Bool) → Bool → List A
    List-filter-helper [] P b = []
    List-filter-helper (x ∷ l) P false = List-filter l P
    List-filter-helper (x ∷ l) P true = x ∷ (List-filter l P)

Bool-dec : {A : Set} → (f : A → Bool) → Decidable (λ x → (f x) ≡ true)
Bool-dec f x with f x
Bool-dec f x     | true = yes refl
Bool-dec f x     | false = no (λ {()})

List-filter' : {A : Set} → {f : A → Bool} → Decidable (λ x → (f x) ≡ true) → List A → List (Σ[ x ∈ A ] (f x ≡ true))
List-filter' P? [] = []
List-filter' P? (x ∷ l) with P? x
... | no  _ = List-filter' P? l
... | yes y = ⟨ x , y ⟩ ∷ List-filter' P? l

List-forget : {A : Set} → {P : A → Set} → List (Σ[ x ∈ A ] P x) → List A
List-forget [] = []
List-forget (x ∷ l) = (proj₁ x) ∷ (List-forget l)

List-P-filter-∈ : {f : A → Bool} → (x : A) → (l : List A) → (x ∈ l) → (P : f x ≡ true) → x ∈ List-forget (List-filter' {A} {f} (Bool-dec f) l)
List-P-filter-∈ {A} {f} x (x₁ ∷ l) (here eq) P with ((Bool-dec f) x₁)
... | no  y = ⊥-elim (y (Eq.trans (Eq.sym (Eq.cong f eq)) P))
... | yes y = here eq
List-P-filter-∈ {A} {f} x (x₁ ∷ l) (there e) P with ((Bool-dec f) x₁)
... | no  y = List-P-filter-∈ x l e P
... | yes y = there (List-P-filter-∈ x l e P)

-- List-filter' : {A : Set} → List A → (f : A → Bool) → List (Σ[ x ∈ A ] (f x ≡ true))
-- List-filter' [] f = []
-- List-filter' (x ∷ l) f = {!   !}
--   where
--     List-filter-helper : {A : Set} → List A → (x : A) → (f : A → Bool) → ((f x) : Bool) → List (Σ[ x ∈ A ] ((f x) ≡ true))
--     List-filter-helper l x f b = {!   !} ∷ {!   !}

-- List-attach : {A : Set} → (l : List A) → (f : A → Bool) → (List-filter {A} l f) → List (Σ[ x ∈ A ] (f x ≡ true))
-- List-attach l f l' = ?

-- List-filter' : {A : Set} → (f : A → Bool) → List A → List (Σ[ x ∈ A ] (f x ≡ true))
-- List-filter' p [] = []
-- List-filter' p (x ∷ xs) with p x
-- List-filter' p (x ∷ xs)    | true  = ⟨ x , {! refl  !} ⟩ ∷ List-filter' p xs
-- List-filter' p (x ∷ xs)    | false = List-filter' p xs

Check-Const1 : {n : ℕ} → Table n → Bool
Check-Const1 (decision t t₁) = (Check-Const1 t) ∧ (Check-Const1 t₁)
Check-Const1 (output x) = x

Check-Exist1 : {n : ℕ} → Table n → Bool
Check-Exist1 (decision t t₁) = (Check-Exist1 t) ∨ (Check-Exist1 t₁)
Check-Exist1 (output x) = x

Cover-Sets : {n : ℕ} → Table n → List term
Cover-Sets {n} t = List-filter (clauses n) (λ x → Check-Const1 (Table (term-table' n x) IMP t))

Cover-Sets-P : {n : ℕ} → (t : Table n) → List (Σ[ x ∈ term ] (Check-Const1 (Table (term-table' n x) IMP t) ≡ true))
Cover-Sets-P {n} t = List-filter' (Bool-dec ((λ x → Check-Const1 (Table (term-table' n x) IMP t)))) (clauses n)

Cover-Sets-test : (Cover-Sets (translateₙ ANDfunc)) ≡ ((∅ ＆ pos 0) ＆ pos 1) ∷ []
Cover-Sets-test = refl

Cover-DNF : {n : ℕ} → Table n → DNF
Cover-DNF t = foldr (λ te C → C ＋ te) const0 (List-forget (Cover-Sets-P t))

Table_EQ : {n : ℕ} → Table n → Table n → Table n
Table decision s s₁ EQ (decision t t₁) = decision (Table s EQ t) (Table s₁ EQ t₁)
Table output x EQ (output x₁) = output ((x ∧ x₁) ∨ ((not x) ∧ (not x₁)))

-- an idea for (table) equivalance : two tables both imply one another

infix 0 _↔_
record _↔_ {n : ℕ} (s t : Table n) : Set where
  field
    to   : Check-Const1(Table_IMP s t) ≡ true
    from : Check-Const1(Table_IMP t s) ≡ true
open _↔_

∧-split : (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-split true true e = ⟨ refl , refl ⟩

∧-combine : (a b : Bool) → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-combine .true .true refl refl = refl

Check-Const1-split : {n : ℕ} → (s t : Table n) → Check-Const1(decision s t) ≡ true → (Check-Const1 s ≡ true) × (Check-Const1 t ≡ true) 
Check-Const1-split s t = ∧-split (Check-Const1 s) (Check-Const1 t)

Check-Const1-form : {n : ℕ} → (t : Table n) → Check-Const1(t) ≡ true → t ≡ const-Table n true
Check-Const1-form (decision t t₁) e = Eq.cong₂ decision (Check-Const1-form t (proj₁ (∧-split (Check-Const1 t) (Check-Const1 t₁) e))) (Check-Const1-form t₁ (proj₂ (∧-split (Check-Const1 t) (Check-Const1 t₁) e)))
Check-Const1-form (output .true) refl = refl

Check-Const1-case : {n : ℕ} → (t : Table n) → t ≡ const-Table n true → Check-Const1(t) ≡ true
Check-Const1-case {suc n} (decision .(const-Table _ true) .(const-Table _ true)) refl = ∧-combine (Check-Const1 (const-Table n true)) (Check-Const1 (const-Table n true)) (Check-Const1-case (const-Table n true) refl) (Check-Const1-case (const-Table n true) refl)
Check-Const1-case {zero} (output .true) refl = refl

↔-split : {n : ℕ} → (s t u v : Table n) → decision s u ↔ decision t v → (s ↔ t) × (u ↔ v)
↔-split s t u v i = ⟨ (record { to = proj₁ (Check-Const1-split (Table s IMP t) (Table u IMP v) (to i)) ; from = proj₁ (Check-Const1-split (Table t IMP s) (Table v IMP u) (from i)) }) 
                     , record { to = proj₂ (Check-Const1-split (Table s IMP t) (Table u IMP v) (to i)) ; from = proj₂ (Check-Const1-split (Table t IMP s) (Table v IMP u) (from i)) } ⟩

≡-split : {n : ℕ} → (s t u v : Table n) → decision s u ≡ decision t v → (s ≡ t) × (u ≡ v)
≡-split s .s u .u refl = ⟨ refl , refl ⟩

decision-table-eq : {n : ℕ} → (s t u v : Table n) → s ≡ t → u ≡ v → decision s u ≡ decision t v
decision-table-eq s .s u .u refl refl = refl

table-output-eq : {n : ℕ} → (s t : Table n) → s ↔ t → s ≡ t
table-output-eq (decision s s₁) (decision t t₁) i = decision-table-eq s t s₁ t₁ (table-output-eq s t (proj₁ (↔-split s t s₁ t₁ i))) (table-output-eq s₁ t₁ (proj₂ (↔-split s t s₁ t₁ i)))
table-output-eq (output false) (output false) i = refl
table-output-eq (output true) (output true) i = refl

-- from : certify that every term from cover list implies the table

List-IMP : {n : ℕ} → Table n → List term → Bool
List-IMP {n} t [] = true
List-IMP {n} t (x ∷ l) = (Check-Const1 (Table (term-table' n x) IMP t)) ∧ List-IMP t l

-- check that every term implies the table means that their DNF also implies the table

Table-OR-IMP : {n : ℕ} → (s t u : Table n) → Check-Const1(Table_IMP s u) ≡ true → Check-Const1(Table_IMP t u) ≡ true → Check-Const1(Table_IMP (Table_OR s t) u) ≡ true
Table-OR-IMP (decision s s₁) (decision t t₁) (decision u u₁) e1 e2 = ∧-combine (Check-Const1 (Table Table s OR t IMP u)) (Check-Const1 (Table Table s₁ OR t₁ IMP u₁)) 
                                                                     (Table-OR-IMP s t u 
                                                                     (proj₁ (∧-split (Check-Const1 (Table s IMP u)) (Check-Const1 (Table s₁ IMP u₁)) e1)) 
                                                                     (proj₁ (∧-split (Check-Const1 (Table t IMP u)) (Check-Const1 (Table t₁ IMP u₁)) e2))) 
                                                                     (Table-OR-IMP s₁ t₁ u₁ 
                                                                     (proj₂ (∧-split (Check-Const1 (Table s IMP u)) (Check-Const1 (Table s₁ IMP u₁)) e1)) 
                                                                     (proj₂ (∧-split (Check-Const1 (Table t IMP u)) (Check-Const1 (Table t₁ IMP u₁)) e2)))
Table-OR-IMP (output false) (output false) (output false) e1 e2 = refl
Table-OR-IMP (output false) (output false) (output true) e1 e2 = refl
Table-OR-IMP (output false) (output true) (output true) e1 e2 = refl
Table-OR-IMP (output true) (output false) (output true) e1 e2 = refl
Table-OR-IMP (output true) (output true) (output true) e1 e2 = refl

Table-IMP-OR-left' : {n : ℕ} → (s t : Table n) → Check-Const1 (Table s IMP (Table t OR s)) ≡ true
Table-IMP-OR-left' (decision s s₁) (decision t t₁) = ∧-combine (Check-Const1 (Table s IMP (Table t OR s))) (Check-Const1 (Table s₁ IMP (Table t₁ OR s₁))) (Table-IMP-OR-left' s t) (Table-IMP-OR-left' s₁ t₁)
Table-IMP-OR-left' (output false) (output x₁) = refl
Table-IMP-OR-left' (output true) (output x₁) = ∨-righttrue x₁

∨-comm : (a b c : Bool) → a ∨ (b ∨ c) ≡ (a ∨ b) ∨ c 
∨-comm false b c = refl
∨-comm true b c = refl

Table-IMP-OR-right : {n : ℕ} → (s t u : Table n) → Check-Const1 (Table s IMP t) ≡ true → Check-Const1 (Table s IMP (Table t OR u)) ≡ true
Table-IMP-OR-right (decision s s₁) (decision t t₁) (decision u u₁) eq = ∧-combine (Check-Const1 (Table s IMP (Table t OR u))) (Check-Const1 (Table s₁ IMP (Table t₁ OR u₁))) (Table-IMP-OR-right s t u (proj₁ (∧-split (Check-Const1 (Table s IMP t)) (Check-Const1 (Table s₁ IMP t₁)) eq))) (Table-IMP-OR-right s₁ t₁ u₁ ( proj₂ (∧-split (Check-Const1 (Table s IMP t)) (Check-Const1 (Table s₁ IMP t₁)) eq) ))
Table-IMP-OR-right (output x) (output x₁) (output x₂) eq = Eq.trans (∨-comm (not x) x₁ x₂) (Eq.trans (Eq.cong (_∨ x₂) eq) refl)

Const0-bottom : (n : ℕ) → (t : Table n) → Check-Const1 (Table const-Table n false IMP t) ≡ true
Const0-bottom (suc n) (decision t t₁) = ∧-combine (Check-Const1 (Table const-Table n false IMP t)) (Check-Const1 (Table const-Table n false IMP t₁)) (Const0-bottom n t) (Const0-bottom n t₁)
Const0-bottom zero (output x) = refl

Const1-top : (n : ℕ) → (t : Table n) → Check-Const1 (Table t IMP (const-Table n true)) ≡ true
Const1-top (suc n) (decision t t₁) = ∧-combine (Check-Const1 (Table t IMP (const-Table n true))) (Check-Const1 (Table t₁ IMP (const-Table n true))) (Const1-top n t) (Const1-top n t₁)
Const1-top zero (output x) = ∨-righttrue (not x)

List-OR-IMP : {n : ℕ} → (t : Table n) → (l : List (Σ[ x ∈ term ] (Check-Const1 (Table (term-table' n x) IMP t) ≡ true))) → Check-Const1 (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (List-forget l))) IMP t) ≡ true
List-OR-IMP {n} t [] = Const0-bottom n t
List-OR-IMP {n} t (x ∷ l) = Table-OR-IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 (List-forget l))) (term-table' n (proj₁ x)) t (List-OR-IMP t l) (proj₂ x)

-- Table-OR-IMP (Table DNF-table n (foldr (λ te C → C ＋ te) const0 (List-forget l))) ((term-table' n (proj₁ x))) t

Cover-DNF-cert-from : {n : ℕ} → (t : Table n) → Check-Const1 (Table DNF-table n (Cover-DNF t) IMP t) ≡ true
Cover-DNF-cert-from t = List-OR-IMP t (Cover-Sets-P t)

-- full-cover : {n : ℕ} → (t : Table n) → (l : List term) → ((t' : Table n) → ( Check-Const1(Table t' IMP t) ≡ true → ∃[ x ] (x ∈ l) × (Check-Const1(Table t' IMP (term-table' n x)) ≡ true) )) → Check-Const1 (Table t IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 (l)))) ≡ true
-- full-cover t l P = {!   !}

-- ∈-cover : {n : ℕ} → (t : Table n) → (l : List (Table n)) → 

-- full-cover : {n : ℕ} → (t : Table n) → (l : List (Table n)) → ((t' : Table n) → ( Check-Const1(Table t' IMP t) ≡ true → ∃[ x ] (x ∈ l) × (Check-Const1(Table t' IMP x) ≡ true) )) → Check-Const1 (Table t IMP (foldr (Table_OR) (const-Table n false) (l))) ≡ true
-- full-cover (decision t t₁) l P = {!   !}
-- full-cover (output false) l P = Const0-bottom 0 (foldr Table_OR (output false) l)
-- full-cover (output true) l P = {!   !}

data entries : ℕ → Set where
  element : {n : ℕ} → Table n → Vec Bool n → entries n

-- build a list (vector) for every entries
-- arguement on table based on its entries

Table-entry : {n : ℕ} → entries n → Table 0
Table-entry (element (decision t t₁) (false Vec.∷ v)) = Table-entry (element t v)
Table-entry (element (decision t t₁) (true Vec.∷ v)) = Table-entry (element t₁ v)
Table-entry (element (output x) Vec.[]) = output x

entry-Table : {n : ℕ} → entries n → Table n
entry-Table (element t x₁) = t

Entries-enumerate : (n : ℕ) → Table n → Vec (entries n) (2 ^ n)
Entries-enumerate zero t = (element t Vec.[]) Vec.∷ Vec.[]
Entries-enumerate (suc n) (decision t t₁) = Data.Vec.Base.map (enumerate-helper n (decision t t₁) false) (Entries-enumerate n t) Data.Vec.Base.++ Eq.subst (Vec (entries (suc n))) (Eq.sym (+-l-zero (2 ^ n))) (Data.Vec.Base.map (enumerate-helper n (decision t t₁) true) (Entries-enumerate n t₁))
  where
    enumerate-helper : (n : ℕ) → Table (suc n) → Bool → (entries n) → (entries (suc n))
    enumerate-helper n t b (element t' vb) = element t (b Vec.∷ vb)
    
Entry-test : Data.Vec.Base.toList(Data.Vec.Base.map (Table-entry) (Entries-enumerate 2 (translateₙ ANDfunc))) ≡ output false ∷ output false ∷ output false ∷ output true ∷ []
Entry-test = refl

Entry-test' : Data.Vec.Base.toList(Data.Vec.Base.map (Table-entry) (Entries-enumerate 2 (translateₙ ORfunc))) ≡ output false ∷ output true ∷ output true ∷ output true ∷ []
Entry-test' = refl

Entry-term : (n : ℕ) → Vec Bool n → term
Entry-term zero Vec.[] = ∅
Entry-term (suc n) (false Vec.∷ v) = (Entry-term n v) ＆ neg n
Entry-term (suc n) (true Vec.∷ v) = (Entry-term n v) ＆ pos n

term-length : term → ℕ
term-length ∅ = 0
term-length (te ＆ x) = suc (term-length te)

Term-entry : (te : term) → Vec Bool (term-length te)
Term-entry ∅ = Vec.[]
Term-entry (te ＆ pos x) = true Vec.∷ (Term-entry te)
Term-entry (te ＆ neg x) = false Vec.∷ (Term-entry te)

TE-length : {n : ℕ} → (v : Vec Bool n) → term-length (Entry-term n v) ≡ n
TE-length Vec.[] = refl
TE-length (false Vec.∷ v) = Eq.cong suc (TE-length v)
TE-length (true Vec.∷ v) = Eq.cong suc (TE-length v)

-- subst-vec-bool : {m n : ℕ} → {k : Vec Bool m} → {l : Vec Bool n} → (x : Bool) → (eq : n ≡ m) → k ≡ Eq.subst (Vec Bool) eq l → (x Vec.∷ k) ≡ Eq.subst (Vec Bool) (Eq.cong suc eq) (x Vec.∷ l) 
-- subst-vec-bool x eq el = {!   !}

subst-vec-bool : {m n : ℕ} → (l : Vec Bool n) → (x : Bool) → (eq : n ≡ m) → (x Vec.∷ (Eq.subst (Vec Bool) eq l)) ≡ Eq.subst (Vec Bool) (Eq.cong suc eq) (x Vec.∷ l) 
subst-vec-bool l x refl = refl

TE-embedd : {n : ℕ} → (v : Vec Bool n) → v ≡ Eq.subst (Vec Bool) ((TE-length v)) (Term-entry (Entry-term n v))
TE-embedd Vec.[] = refl
TE-embedd {suc n} (false Vec.∷ v) = Eq.trans (Eq.cong (false Vec.∷_) (TE-embedd v)) (subst-vec-bool (Term-entry (Entry-term n v)) false (TE-length v))
TE-embedd {suc n} (true Vec.∷ v) = Eq.trans (Eq.cong (true Vec.∷_) (TE-embedd v)) (subst-vec-bool (Term-entry (Entry-term n v)) true (TE-length v))

Entry-place : {n : ℕ} → entries n → term
Entry-place {n} (element t v) = Entry-term n v
    
-- after digging out all the term, the table becomes constant false

cf-helper-true : {n : ℕ} → (v : Vec Bool n) → (l : List term) → Entry-term n v ∈ l → (Entry-term n v ＆ pos n) ∈ clhelper n (l)
cf-helper-true {n} v (x ∷ l) (here e) = here (Eq.cong (_＆ pos n) e)
cf-helper-true {n} v (x ∷ l) (there c) = there (there (there (cf-helper-true v l c)))
cf-helper-false : {n : ℕ} → (v : Vec Bool n) → (l : List term) → Entry-term n v ∈ l → (Entry-term n v ＆ neg n) ∈ clhelper n (l)
cf-helper-false {n} v (x ∷ l) (here e) = there (here (Eq.cong (_＆ neg n) e))
cf-helper-false {n} v (x ∷ l) (there c) = there (there (there (cf-helper-false v l c)))

clauses-full : (n : ℕ) → (e : entries n) → Entry-place e ∈ clauses n
clauses-full zero (element t Vec.[]) = here refl
clauses-full (suc n) (element (decision t t₁) (false Vec.∷ vb)) = cf-helper-false vb (clauses n) (clauses-full n (element t vb))
clauses-full (suc n) (element (decision t t₁) (true Vec.∷ vb)) = cf-helper-true vb (clauses n) (clauses-full n (element t₁ vb))

element-table : {n : ℕ} → (v : Vec Bool n) → Table n
element-table Vec.[] = output true
element-table {suc n} (false Vec.∷ v) = decision (element-table v) (const-Table n false)
element-table {suc n} (true Vec.∷ v) = decision (const-Table n false) (element-table v)

-- element-term-↔ : {n : ℕ} → (v : Vec Bool n) → term-table' n (Entry-term n v) ↔ element-table v
-- element-term-↔ v = {!   !}

-- Table-AND-filter-left : {n : ℕ} → {s t : Table n} → Table (decision s t) AND (decision (const-Table n true) (const-Table n false)) ≡ decision
-- devide term-table into subtables

≤-suc : (m n : ℕ) → n ≤ m → n ≤ suc m
≤-suc m .zero z≤n = z≤n
≤-suc (suc m) (suc n) (s≤s le) = s≤s (≤-suc m n le)

term-table-split-mn : (m n : ℕ) → (v : Vec Bool n) → n ≤ m → term-table' (suc m) (Entry-term n v) ≡ decision (term-table' m (Entry-term n v)) (term-table' m (Entry-term n v))
term-table-split-mn m zero Vec.[] le = refl
term-table-split-mn (suc m) (suc n) (false Vec.∷ v) (s≤s le) = 
  begin
    Table term-table' (suc (suc m)) (Entry-term n v) AND (lit-table (suc (suc m)) (neg (suc m ∸ n)))
    ≡⟨ Eq.cong Table term-table' (suc (suc m)) (Entry-term n v) AND (Eq.cong (λ x → lit-table (suc (suc m)) (neg x)) (ℕ-∸-suc-mn m n le)) ⟩
    Table term-table' (suc (suc m)) (Entry-term n v) AND (lit-table (suc (suc m)) (neg (suc (m ∸ n))))
    ≡⟨ refl ⟩
    Table term-table' (suc (suc m)) (Entry-term n v) AND (decision (lit-table (suc m) (neg (m ∸ n))) (lit-table (suc m) (neg (m ∸ n))))
    ≡⟨ Eq.cong (λ t → Table t AND ((decision (lit-table (suc m) (neg (m ∸ n))) (lit-table (suc m) (neg (m ∸ n)))))) (term-table-split-mn (suc m) n v (≤-suc m n le)) ⟩
    Table (decision (term-table' (suc m) (Entry-term n v)) (term-table' (suc m) (Entry-term n v))) AND (decision (lit-table (suc m) (neg (m ∸ n))) (lit-table (suc m) (neg (m ∸ n))))
    ≡⟨ refl ⟩
    decision (Table (term-table' (suc m) (Entry-term n v)) AND (lit-table (suc m) (neg (m ∸ n)))) (Table term-table' (suc m) (Entry-term n v) AND (lit-table (suc m) (neg (m ∸ n))))
    ∎
term-table-split-mn (suc m) (suc n) (true Vec.∷ v) (s≤s le) = 
  begin
    Table term-table' (suc (suc m)) (Entry-term n v) AND (lit-table (suc (suc m)) (pos (suc m ∸ n)))
    ≡⟨ Eq.cong Table term-table' (suc (suc m)) (Entry-term n v) AND (Eq.cong (λ x → lit-table (suc (suc m)) (pos x)) (ℕ-∸-suc-mn m n le)) ⟩
    Table term-table' (suc (suc m)) (Entry-term n v) AND (lit-table (suc (suc m)) (pos (suc (m ∸ n))))
    ≡⟨ refl ⟩
    Table term-table' (suc (suc m)) (Entry-term n v) AND (decision (lit-table (suc m) (pos (m ∸ n))) (lit-table (suc m) (pos (m ∸ n))))
    ≡⟨ Eq.cong (λ t → Table t AND ((decision (lit-table (suc m) (pos (m ∸ n))) (lit-table (suc m) (pos (m ∸ n)))))) (term-table-split-mn (suc m) n v (≤-suc m n le)) ⟩
    Table (decision (term-table' (suc m) (Entry-term n v)) (term-table' (suc m) (Entry-term n v))) AND (decision (lit-table (suc m) (pos (m ∸ n))) (lit-table (suc m) (pos (m ∸ n))))
    ≡⟨ refl ⟩
    decision (Table (term-table' (suc m) (Entry-term n v)) AND (lit-table (suc m) (pos (m ∸ n)))) (Table term-table' (suc m) (Entry-term n v) AND (lit-table (suc m) (pos (m ∸ n))))
    ∎


-- term-table' (suc n) (Entry-term n v) ≡ decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v))
term-table-split : (n : ℕ) → (v : Vec Bool n) → term-table' (suc n) (Entry-term n v) ≡ decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v))
term-table-split n v = term-table-split-mn n n v (≤-ref n)


element-term-eq : {n : ℕ} → (v : Vec Bool n) → term-table' n (Entry-term n v) ≡ element-table (v)
element-term-eq Vec.[] = refl
element-term-eq {suc n} (false Vec.∷ v) = 
  begin
    Table term-table' (suc n) (Entry-term n v) AND (lit-table (suc n) (neg (n ∸ n)))
    ≡⟨ Eq.cong (λ t → Table t AND (lit-table (suc n) (neg (n ∸ n)))) (term-table-split n v) ⟩
    Table decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v)) AND (lit-table (suc n) (neg (n ∸ n)))
    ≡⟨ Eq.cong (Table decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v)) AND) (Eq.cong (λ x → lit-table (suc n) (neg x)) (ℕ-∸ n)) ⟩
    Table decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v)) AND (decision (const-Table n true) (const-Table n false))
    ≡⟨ refl ⟩
    decision (Table term-table' n (Entry-term n v) AND (const-Table n true)) (Table term-table' n (Entry-term n v) AND (const-Table n false))
    ≡⟨ Eq.cong (λ t → decision t (Table term-table' n (Entry-term n v) AND (const-Table n false))) (C1-Table-right-AND (term-table' n (Entry-term n v))) ⟩
    decision (term-table' n (Entry-term n v)) (Table term-table' n (Entry-term n v) AND (const-Table n false))
    ≡⟨ Eq.cong (decision (term-table' n (Entry-term n v))) (C0-Table-right-AND (term-table' n (Entry-term n v))) ⟩
    decision (term-table' n (Entry-term n v)) (const-Table n false)
    ≡⟨ Eq.cong (λ t → decision t (const-Table n false)) (element-term-eq v) ⟩
    decision (element-table v) (const-Table n false)
    ∎
element-term-eq {suc n} (true Vec.∷ v) = 
  begin
    Table term-table' (suc n) (Entry-term n v) AND (lit-table (suc n) (pos (n ∸ n)))
    ≡⟨ Eq.cong (λ t → Table t AND (lit-table (suc n) (pos (n ∸ n)))) (term-table-split n v) ⟩
    Table decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v)) AND (lit-table (suc n) (pos (n ∸ n)))
    ≡⟨ Eq.cong (Table decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v)) AND) (Eq.cong (λ x → lit-table (suc n) (pos x)) (ℕ-∸ n)) ⟩
    Table decision (term-table' n (Entry-term n v)) (term-table' n (Entry-term n v)) AND (decision (const-Table n false) (const-Table n true))
    ≡⟨ refl ⟩
    decision (Table term-table' n (Entry-term n v) AND (const-Table n false)) (Table term-table' n (Entry-term n v) AND (const-Table n true))
    ≡⟨ Eq.cong (decision (Table term-table' n (Entry-term n v) AND (const-Table n false))) (C1-Table-right-AND (term-table' n (Entry-term n v))) ⟩
    decision (Table term-table' n (Entry-term n v) AND (const-Table n false)) (term-table' n (Entry-term n v))
    ≡⟨ Eq.cong (λ t → decision t (term-table' n (Entry-term n v))) (C0-Table-right-AND (term-table' n (Entry-term n v))) ⟩
    decision (const-Table n false) (term-table' n (Entry-term n v))
    ≡⟨ Eq.cong (decision (const-Table n false)) (element-term-eq v) ⟩
    decision (const-Table n false) (element-table v)
    ∎

Entry-probe : {n : ℕ} → (v : Vec Bool n) → (t : Table n) → Table-entry (element t v) ≡ output true → Check-Const1 (Table (element-table v) IMP t) ≡ true
Entry-probe Vec.[] (output true) eq = refl
Entry-probe {suc n} (false Vec.∷ v) (decision t t₁) eq = ∧-combine (Check-Const1 (Table element-table v IMP t)) (Check-Const1 (Table const-Table n false IMP t₁)) (Entry-probe v t eq) (Const0-bottom n t₁)
Entry-probe {suc n} (true Vec.∷ v) (decision t t₁) eq = ∧-combine (Check-Const1 (Table const-Table n false IMP t)) (Check-Const1 (Table element-table v IMP t₁)) (Const0-bottom n t) (Entry-probe v t₁ eq)

clauses-cover : {n : ℕ} → (e : entries n) → Table-entry e ≡ output true → Entry-place e ∈ List-forget (Cover-Sets-P (entry-Table e))
clauses-cover {n} (element t vb) eq = List-P-filter-∈ (Entry-place (element t vb)) (clauses n) (clauses-full n (element t vb)) (Eq.subst (λ s → Check-Const1 (Table s IMP t) ≡ true) (Eq.sym (element-term-eq vb)) (Entry-probe vb t eq))

Entries-imply-false : {n : ℕ} → {s s₁ t t₁ : Table n} → ((v : Vec Bool (suc n)) → (Check-Const1 (Table (Table-entry (element (decision s s₁) v)) IMP (Table-entry (element (decision t t₁) v))) ≡ true)) → ((v₁ : Vec Bool n) → (Check-Const1 (Table (Table-entry (element s v₁)) IMP (Table-entry (element t v₁))) ≡ true))
Entries-imply-false P v₁ = P (false Vec.∷ v₁)
Entries-imply-true : {n : ℕ} → {s s₁ t t₁ : Table n} → ((v : Vec Bool (suc n)) → (Check-Const1 (Table (Table-entry (element (decision s s₁) v)) IMP (Table-entry (element (decision t t₁) v))) ≡ true)) → ((v₁ : Vec Bool n) → (Check-Const1 (Table (Table-entry (element s₁ v₁)) IMP (Table-entry (element t₁ v₁))) ≡ true))
Entries-imply-true P v₁ = P (true Vec.∷ v₁)

Entries-imply : {n : ℕ} → (s t : Table n) → ((v : Vec Bool n) → (Check-Const1 (Table (Table-entry (element s v)) IMP (Table-entry (element t v))) ≡ true)) → Check-Const1 (Table s IMP t) ≡ true
Entries-imply (decision s s₁) (decision t t₁) P = ∧-combine (Check-Const1 (Table s IMP t)) (Check-Const1 (Table s₁ IMP t₁)) (Entries-imply s t (Entries-imply-false P)) (Entries-imply s₁ t₁ (Entries-imply-true P))
Entries-imply (output x) (output x₁) P = P Vec.[]

-- Entries-imply-full : {n : ℕ} → (s t : Table n) → ((v : Vec Bool n) → (Check-Const1 (Table (Table-entry (element s v)) IMP (Table-entry (element t v))) ≡ true)) → Check-Const1 (Table s IMP t) ≡ true

exist-AND-term : {n : ℕ} → (te : term) → (l : List term) → te ∈ l → Check-Const1 (Table (term-table' n te) IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 l))) ≡ true
exist-AND-term {n} te (.te ∷ l) (here refl) = Table-IMP-OR-left' (term-table' n te)  (DNF-table n (foldr (λ te₁ C → C ＋ te₁) const0 l))
exist-AND-term {n} te (x ∷ l) (there i) = Table-IMP-OR-right (term-table' n te) (DNF-table n (foldr (λ te₁ C → C ＋ te₁) const0 l)) (term-table' n x) (exist-AND-term te l i)

Entries-cover : {n : ℕ} → (t : Table n) → (v : Vec Bool n) → Table-entry (element t v) ≡ output true → Check-Const1 (Table (element-table v) IMP (DNF-table n (Cover-DNF t))) ≡ true
Entries-cover t v eq = Entries-cover-helper t v (clauses-cover (element t v) eq)
  where
    Entries-cover-helper : {n : ℕ} → (t : Table n) → (v : Vec Bool n) → (Entry-place (element t v) ∈ List-forget (Cover-Sets-P t)) → Check-Const1 (Table (element-table v) IMP (DNF-table n (Cover-DNF t))) ≡ true
    Entries-cover-helper {n} t v i = Eq.subst (λ t' → Check-Const1 (Table t' IMP (DNF-table n (Cover-DNF t))) ≡ true) (element-term-eq v) (exist-AND-term (Entry-term n v) (List-forget (Cover-Sets-P t)) i)

-- Entries-cover-full : {n : ℕ} → (t : Table n) → (v : Vec Bool n) → Check-Const1 (Table (element-table v) IMP (DNF-table n (Cover-DNF t))) ≡ true
-- Entries-cover-full {n} t v with (Table-entry (element t v))
-- ... | output false = Const0-bottom {! n  !} {!   !}
-- ... | output true = {!   !}

truefalse : (b : Bool) → b ≡ true → b ≡ false → ⊥
truefalse false () ef
truefalse true et ()

Entry-probe-full-false : {n : ℕ} → {s s₁ t t₁ : Table n} → ((v' : Vec Bool (suc n)) → Table-entry (element (decision s s₁) v') ≡ output true → Check-Const1 (Table element-table v' IMP (decision t t₁)) ≡ true) → ((v : Vec Bool n) → Table-entry (element s v) ≡ output true → Check-Const1 (Table (element-table v) IMP t) ≡ true)
Entry-probe-full-false {n} {s} {s₁} {t} {t₁} P v eq = proj₁ (∧-split (Check-Const1 (Table (element-table v) IMP t)) (Check-Const1 (Table (const-Table n false) IMP t₁)) (P (false Vec.∷ v) eq))
Entry-probe-full-true : {n : ℕ} → {s s₁ t t₁ : Table n} → ((v' : Vec Bool (suc n)) → Table-entry (element (decision s s₁) v') ≡ output true → Check-Const1 (Table element-table v' IMP (decision t t₁)) ≡ true) → ((v : Vec Bool n) → Table-entry (element s₁ v) ≡ output true → Check-Const1 (Table (element-table v) IMP t₁) ≡ true)
Entry-probe-full-true {n} {s} {s₁} {t} {t₁} P v eq = proj₂ (∧-split (Check-Const1 (Table (const-Table n false) IMP t)) (Check-Const1 (Table (element-table v) IMP t₁)) (P (true Vec.∷ v) eq))

Entry-probe-full : {n : ℕ} → (s t : Table n) → ((v : Vec Bool n) → Table-entry (element s v) ≡ output true → Check-Const1 (Table (element-table v) IMP t) ≡ true) → Check-Const1 (Table s IMP t) ≡ true
Entry-probe-full {(suc n)} (decision s s₁) (decision t t₁) P = ∧-combine (Check-Const1 (Table s IMP t)) (Check-Const1 (Table s₁ IMP t₁)) (Entry-probe-full s t (Entry-probe-full-false P)) (Entry-probe-full s₁ t₁ (Entry-probe-full-true P))
Entry-probe-full {n} (output false) (output x₁) P = Const0-bottom n (output x₁)
Entry-probe-full (output true) (output false) P = ⊥-elim (truefalse (Check-Const1 (Table (output true) IMP (output false))) (P Vec.[] refl) refl)
Entry-probe-full (output true) (output true) P = refl

NOT-OR : (b c : Bool) → not (b ∨ c) ≡ (not b ∧ not c)
NOT-OR false c = refl
NOT-OR true c = refl

NOT-OR-Table : {n : ℕ} → (s t : Table n) → Table (Table s OR t) NOT ≡ Table (Table s NOT) AND (Table t NOT)
NOT-OR-Table (decision s s₁) (decision t t₁) = Eq.cong₂ decision (NOT-OR-Table s t) (NOT-OR-Table s₁ t₁)
NOT-OR-Table (output x) (output x₁) = Eq.cong output (NOT-OR x x₁)

∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
∧-assoc false b c = refl
∧-assoc true b c = refl

Table-AND-assoc : {n : ℕ} → (s t u : Table n) → Table (Table s AND t) AND u ≡ Table s AND (Table t AND u)
Table-AND-assoc (decision s s₁) (decision t t₁) (decision u u₁) = Eq.cong₂ decision (Table-AND-assoc s t u) (Table-AND-assoc s₁ t₁ u₁)
Table-AND-assoc (output x) (output x₁) (output x₂) = Eq.cong output (∧-assoc x x₁ x₂)

list-Table-dig : {n : ℕ} → Table n → List term → Table n
list-Table-dig {n} t l = foldr (λ te t' → Table t' AND Table (term-table' n te) NOT) t l

dig-fold : {n : ℕ} → (t : Table n) → (l : List term) → list-Table-dig t l ≡ Table t AND (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) NOT)
dig-fold {n} t [] = Eq.trans (Eq.sym (C1-Table-right-AND t)) (Eq.cong (Table_AND t) (Eq.sym (const-Table-NOT n false)))
dig-fold {n} t (x ∷ l) =
  begin
    list-Table-dig t (x ∷ l)
    ≡⟨ refl ⟩
    (foldr (λ te t' → Table t' AND Table (term-table' n te) NOT) t (x ∷ l))
    ≡⟨ refl ⟩
    Table (foldr (λ te t' → Table t' AND Table (term-table' n te) NOT) t l) AND Table (term-table' n x) NOT
    ≡⟨ refl ⟩
    Table (list-Table-dig t l) AND Table (term-table' n x) NOT
    ≡⟨ Eq.cong (λ t → Table t AND Table (term-table' n x) NOT) (dig-fold t l) ⟩
    Table (Table t AND (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) NOT)) AND (Table (term-table' n x) NOT)
    ≡⟨ Table-AND-assoc t (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) NOT) Table (term-table' n x) NOT ⟩
    Table t AND (Table (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) NOT) AND (Table (term-table' n x) NOT))
    ≡⟨ Eq.sym (Eq.cong (λ s → Table t AND s) (NOT-OR-Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) (term-table' n x))) ⟩
    Table t AND Table (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 l)) OR (term-table' n x)) NOT
    ∎

Table-AND-NOT : {n : ℕ} → (s t : Table n) → Table s AND (Table t NOT) ≡ const-Table n false → Table s IMP t ≡ const-Table n true
Table-AND-NOT {suc n} (decision s s₁) (decision t t₁) e = Eq.cong₂ decision (Table-AND-NOT s t (proj₁ (≡-split (Table s AND Table t NOT) (const-Table n false) (Table s₁ AND Table t₁ NOT) (const-Table n false) e))) (Table-AND-NOT s₁ t₁ (proj₂ (≡-split (Table s AND Table t NOT) (const-Table n false) (Table s₁ AND Table t₁ NOT) (const-Table n false) e)))
Table-AND-NOT (output x) (output x₁) e = AND-NOT-helper x x₁ e
  where 
    AND-NOT-helper : (a b : Bool) → output (a ∧ not b) ≡ output false → output (not a ∨ b) ≡ output true
    AND-NOT-helper false b e = refl
    AND-NOT-helper true true e = refl

C1-top-helper : {n : ℕ} → (s t : Table n) → t ≡ const-Table n true → Check-Const1(Table s IMP t) ≡ true
C1-top-helper {n} s .(const-Table _ true) refl = Const1-top n s

C1-righttrue-helper : {n : ℕ} → (s t : Table n) → t ≡ const-Table n true → Table s OR t ≡ const-Table n true
C1-righttrue-helper {n} s .(const-Table n true) refl = (C1-Table-right-OR s)

-- dig-full : {n : ℕ} → (t : Table n) → (l : List term) → list-Table-dig t l ≡ const-Table n false → Check-Const1 (Table t IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 (l)))) ≡ true
-- dig-full {n} .(const-Table n false) [] refl = Const0-bottom n (const-Table n false)
-- dig-full {n} t (x ∷ l) P = {!   !}
--   where
--     dig-full-helper : {n : ℕ} → (t : Table n) → list-Table-dig t (x ∷ l) ≡ const-Table n false → Check-Const1 (Table t IMP (Table DNF-table n (foldr (λ te C → C ＋ te) const0 l) OR (term-table' n x))) ≡ true
--     dig-full-helper {suc n} (decision t t₁) P = {!   !}
--     dig-full-helper (output false) P = Const0-bottom 0  (Table DNF-table 0 (foldr (λ te C → C ＋ te) const0 l) OR (term-table' 0 x))
--     dig-full-helper (output true) P = C1-top-helper (output true) ((Table DNF-table 0 (foldr (λ te C → C ＋ te) const0 l) OR (term-table' 0 x))) (C1-righttrue-helper ((DNF-table 0 (foldr (λ te C → C ＋ te) const0 l))) (term-table' 0 x) (term-table'-zero x))

dig-full : {n : ℕ} → (t : Table n) → (l : List term) → list-Table-dig t l ≡ const-Table n false → Check-Const1 (Table t IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 (l)))) ≡ true
dig-full {n} t l P = Check-Const1-case (Table t IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 (l)))) (dig-full-helper t l (Eq.trans (Eq.sym (dig-fold t l)) P))
  where 
    dig-full-helper : {n : ℕ} → (t : Table n) → (l : List term) → Table t AND (Table (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) NOT) ≡ const-Table n false → Table t IMP (DNF-table n (foldr (λ te C → C ＋ te) const0 (l))) ≡ const-Table n true
    dig-full-helper {n} t l P = Table-AND-NOT t (DNF-table n (foldr (λ te C → C ＋ te) const0 l)) P

-- Vec→term : {n : ℕ} → Vec Bool n → term
-- Vec→term Vec.[] = {!   !}
-- Vec→term (x Vec.∷ v) = {!   !}


Cover-DNF-cert-to : {n : ℕ} → (t : Table n) → Check-Const1 (Table t IMP (DNF-table n (Cover-DNF t))) ≡ true
Cover-DNF-cert-to {n} t = Entry-probe-full t (DNF-table n (Cover-DNF t)) (Entries-cover t)

Cover-DNF-cert-↔ : {n : ℕ} → (t : Table n) → t ↔ DNF-table n (Cover-DNF t)
Cover-DNF-cert-↔ t = record { to = Cover-DNF-cert-to t ; from = Cover-DNF-cert-from t }

Cover-DNF-cert : {n : ℕ} → (t : Table n) → t ≡ DNF-table n (Cover-DNF t)
Cover-DNF-cert {n} t = table-output-eq t (DNF-table n (Cover-DNF t)) (Cover-DNF-cert-↔ t)

Cover-DNF-test : translateₙ ANDfunc ≡ DNF-table 2 (Cover-DNF (translateₙ ANDfunc))
Cover-DNF-test = refl

-- create a semantics for boolean circuit 
-- consider a trivial way of transforming table into DNF
-- filter the plausible cluase and run set cover

--Set cover algorithm :

term-cost : term → ℕ
term-cost ∅ = 0 
term-cost (t ＆ x) = term-cost t + 1

-- data _<<_ : term → term → Set where
--   empty : ∅ << te
--   succ : s << t → 

take-max-term : (n : ℕ) → term → List term → term
take-max-term n te l = foldr (λ x x₁ → max-term-helper x x₁ (Check-Const1 (Table term-table' n x IMP (term-table' n x₁)))) te l
  where 
    max-term-helper : term → term → Bool → term
    max-term-helper s t false = s 
    max-term-helper s t true = t
    
Greedy-set-cover : {n : ℕ} → Table n → DNF
Greedy-set-cover {n} t = Greedy-helper n t (Cover-Sets t)
  where
    mutual
      Greedy-helper : (n : ℕ) → Table n → List term → DNF
      Greedy-helper n t [] = const0 
      Greedy-helper n t (x ∷ l) = Greedy-helper-helper n t l x (Check-Exist1 (Table (term-table' n x) IMP t))
      Greedy-helper-helper : (n : ℕ) → Table n → List term → term → Bool → DNF
      Greedy-helper-helper n t l te false = Greedy-helper n t l
      Greedy-helper-helper n t l te true = Greedy-helper n (Table t AND Table (term-table' n (take-max-term n te l)) NOT) l ＋ (take-max-term n te l)


-- take a maximal element
-- remove all element that was strictly include in the element (including itself)
    -- {-# TERMINATING #-}
-- Greedy-helper n t (x ∷ l) = (Greedy-helper n (Table t AND Table (term-table' n (take-max-term n x l)) NOT) (List-filter l (λ te → Check-Exist1 (Table ((Table t AND Table (term-table' n (take-max-term n x l)) NOT)) AND (term-table' n te))))) ＋ (take-max-term n x l)


Greedy-set-cover-test : translateₙ ORfunc ≡ DNF-table 2 (Greedy-set-cover (translateₙ ORfunc))
Greedy-set-cover-test = refl      

-- General-Set-covers : (t : Table n) → (l : List (Σ[ x ∈ term ] (Check-Const1 (Table (term-table' n x) IMP t) ≡ true))) → 

-- Cover-DNF-ex : Cover-DNF (translateₙ ANDfunc) ≡ const0
-- Cover-DNF-ex = {! refl  !}
