// .  ======================= Prop

constant symbol Prop : TYPE;

builtin "Prop" ≔ Prop;

// interpretation of propositions in TYPE

injective symbol π : Prop → TYPE; // `p

builtin "P" ≔ π;

// true

constant symbol ⊤ : Prop; // \top

constant symbol top : π ⊤;

// false

constant symbol ⊥ : Prop; // \bot

constant symbol ⊥ₑ [p: Prop] : π ⊥ → π p;

// implication

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5; // =>

rule π ($p ⇒ $q) ↪ π $p → π $q;

symbol fold_⇒ [p q: Prop] : π (p ⇒ q) → π p → π q ≔
begin
  assume p q pq h; apply pq h;
end;

// negation

symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg

// conjunction

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix left 7; // /\ or \wedge

constant symbol ∧ᵢ [p q: Prop] : π p → π q → π (p ∧ q);
symbol ∧ₑ₁ [p q: Prop] : π (p ∧ q) → π p;
symbol ∧ₑ₂ [p q: Prop ] : π (p ∧ q) → π q;

// disjunction

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix left 6; // \/ or \vee

constant symbol ∨ᵢ₁ [p q: Prop] : π p → π (p ∨ q);
constant symbol ∨ᵢ₂ [p q: Prop] : π q → π (p ∨ q);
symbol ∨ₑ [p q r : Prop] : π (p ∨ q) → (π p → π r) → (π q → π r) → π r;

// check that priorities are correctly set
assert x y z ⊢ x ∨ y ∧ z ≡ x ∨ (y ∧ z);

// equivalence

symbol ⇔ (p q: Prop) ≔ (p ⇒ q) ∧ (q ⇒ p); notation ⇔ infix right 5;

opaque symbol ⇔_refl [p: Prop] : π (p ⇔ p) ≔
begin
  assume p; apply ∧ᵢ { assume h; apply h } { assume h; apply h }
end;

opaque symbol ⇔_sym [p q: Prop] : π (p ⇔ q) → π (q ⇔ p) ≔
begin
  assume p q h; apply ∧ᵢ { apply ∧ₑ₂ h } { apply ∧ₑ₁ h };
end;

debug +t;

opaque symbol ⇔_trans (p q r: Prop) : π (p ⇔ q) → π (q ⇔ r) → π (p ⇔ r) ≔
begin
  assume p q r epq eqr; apply ∧ᵢ
    {
        assume hp;
        apply ∧ₑ₁ eqr _;
        apply ∧ₑ₁ epq hp;
    }
    { assume hr; apply ∧ₑ₂ epq _; apply ∧ₑ₂ eqr hr };
end;

// Set ====================================


// Type of set codes for quantifying over sets (polymorphism)

constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

builtin "T" ≔ τ;

// Cartesian product

constant symbol × : Set → Set → Set; notation × infix right 10; // \times

assert a b c ⊢ a × b × c ≡ a × (b × c);

symbol & [a b] : τ a → τ b → τ (a × b); notation & infix right 30;

assert a (x:τ a) b (y:τ b) c (z:τ c) ⊢ x & y & z : τ(a × b × c);
assert x y z ⊢ x & y & z ≡ x & (y & z);

symbol ₁ [a b] : τ(a × b) → τ a; notation ₁ postfix 10;

rule ($x & _)₁ ↪ $x;

symbol ₂ [a b] : τ(a × b) → τ b; notation ₂ postfix 10;

rule (_ & $x)₂ ↪ $x;

constant symbol = [a] : τ a → τ a → Prop;

notation = infix 10;

constant symbol eq_refl [a] (x:τ a) : π (x = x);
constant symbol ind_eq [a] [x y:τ a] : π (x = y) → Π p, π (p y) → π (p x);

builtin "eq"    ≔ =;
builtin "refl"  ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

symbol ≠ [a] (x y : τ a) ≔ ¬ (x = y); notation ≠ infix 10; // \neq

opaque symbol feq [a b] (f:τ a → τ b) [x x':τ a] : π(x = x') → π(f x = f x') ≔
begin
  assume a b f x x' xx'; rewrite xx'; reflexivity;
end;

opaque symbol feq2 [a b c] (f:τ a → τ b → τ c):
  Π [x x':τ a], π(x = x') → Π [y y':τ b], π(y = y') → π(f x y = f x' y') ≔
begin
  assume a b c f x x' xx' y y' yy'; rewrite xx'; rewrite yy'; reflexivity
end;

opaque symbol eq_sym [a] [x y:τ a] : π(x = y) → π(y = x) ≔
begin
  assume a x y h; symmetry; apply h
end;


// Universal quantification

constant symbol ∀ [a] : (τ a → Prop) → Prop; notation ∀ quantifier; // !! or \forall

rule π (∀ $f) ↪ Π x, π ($f x);

// Existential quantification

constant symbol ∃ [a] : (τ a → Prop) → Prop; notation ∃ quantifier; // ?? or \exists

constant symbol ∃ᵢ [a] p (x:τ a) : π (p x) → π (∃ p);
symbol ∃ₑ [a] p : π (∃ p) → Π q, (Π x:τ a, π (p x) → π q) → π q;

rule ∃ₑ _ (∃ᵢ _ $x $px) _ $f ↪ $f $x $px;


// ===========================

inductive 𝔹 : TYPE ≔ // `dB or \BbbB
| true : 𝔹
| false : 𝔹;

constant symbol bool : Set;

rule τ bool ↪ 𝔹;

// induction principle with equalities

opaque symbol case_𝔹 (b: τ bool) : π (b = true ∨ b = false) ≔
begin
  induction
  { apply ∨ᵢ₁; reflexivity; }
  { apply ∨ᵢ₂; reflexivity; }
end;

opaque symbol ind_𝔹_eq (p: τ bool → Prop) (b: τ bool) :
 (π(b = true) → π(p b)) → (π(b = false) → π(p b)) → π(p b) ≔
begin
  assume p b t f; refine ∨ₑ (case_𝔹 b) t f;
end;

// non confusion of constructors

symbol istrue : 𝔹 → Prop;

rule istrue true ↪ ⊤
with istrue false ↪ ⊥;

opaque symbol false≠true : π (false ≠ true) ≔
begin
  assume h;
  type (ind_eq h );
  refine ind_eq h istrue top
end;

opaque symbol true≠false : π (true ≠ false) ≔
begin
  assume h; apply false≠true; symmetry; apply h
end;

// not

symbol not : 𝔹 → 𝔹;

rule not true  ↪ false
with not false ↪ true;

// or

symbol or : 𝔹 → 𝔹 → 𝔹; notation or infix left 20;

rule true  or _     ↪ true
with _     or true  ↪ true
with false or $b    ↪ $b
with $b    or false ↪ $b;

opaque symbol ∨_istrue [p q] : π(istrue(p or q)) → π(istrue p ∨ istrue q) ≔
begin
  induction
  { assume q h; apply ∨ᵢ₁; apply top; }
  { assume q h; apply ∨ᵢ₂; apply h; }
end;

opaque symbol istrue_or [p q] : π(istrue p ∨ istrue q) → π(istrue(p or q)) ≔
begin
  induction
  { assume q h; apply top; }
  { assume q h; apply ∨ₑ h { assume i; apply ⊥ₑ i; } { assume i; apply i; } }
end;

opaque symbol orᵢ₁ [p] q : π (istrue p) → π (istrue (p or q)) ≔
begin
  induction
  { simplify; assume b h; apply top }
  { simplify; assume b h; apply ⊥ₑ h }
end;

opaque symbol orᵢ₂ p [q] : π (istrue q) → π (istrue (p or q)) ≔
begin
  induction
  { simplify; assume b h; apply top }
  { simplify; assume b h; apply h }
end;

opaque symbol orₑ [p q] r : π(istrue(p or q)) →
  (π(istrue p) → π(istrue r)) → (π(istrue q) → π(istrue r)) → π(istrue r) ≔
begin
  assume p q r pq pr qr;
  have h: π(istrue p ∨ istrue q) { apply @∨_istrue p q pq /*FIXME*/ };
  apply ∨ₑ h pr qr;
end;

opaque symbol orC p q : π (p or q = q or p) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

opaque symbol orA p q r : π ((p or q) or r = p or (q or r)) ≔
begin
    induction
    { reflexivity; }
    { reflexivity; }
end;

// and

symbol and : 𝔹 → 𝔹 → 𝔹; notation and infix left 7;

rule true  and $b    ↪ $b
with $b    and true  ↪ $b
with false and _     ↪ false
with _     and false ↪ false;

opaque symbol ∧_istrue [p q] : π(istrue (p and q)) → π(istrue p ∧ istrue q) ≔
begin
  induction
  { induction
    { assume h; apply ∧ᵢ { apply top } { apply top } }
    { assume h; apply ⊥ₑ h; }
  }
  { assume q h; apply ⊥ₑ h; }
end;

opaque symbol istrue_and [p q] : π(istrue p ∧ istrue q) → π(istrue (p and q)) ≔
begin
  induction
  { assume q h; apply ∧ₑ₂ h; }
  { assume q h; apply ∧ₑ₁ h; }
end;

opaque symbol andᵢ [p q] : π(istrue p) → π(istrue q) → π(istrue (p and q)) ≔
begin
  assume p q h i; //FIXME: apply istrue_and fails
  apply @istrue_and p q; apply ∧ᵢ h i;
end;

opaque symbol andₑ₁ [p q] : π (istrue (p and q)) → π (istrue p) ≔
begin
  induction
  { assume q i; apply top; }
  { assume q i; apply i; }
end;

opaque symbol andₑ₂ [p q] : π (istrue (p and q)) → π (istrue q) ≔
begin
  induction
  { assume q i; apply i; }
  { assume q i; apply ⊥ₑ i; }
end;

// if-then-else

symbol if : 𝔹 → Π [a], τ a → τ a → τ a;

rule if true  $x _ ↪ $x
with if false _ $y ↪ $y;