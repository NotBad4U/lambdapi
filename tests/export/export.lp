constant symbol Prop: TYPE;

builtin "Prop" ≔ Prop;

constant symbol Set: TYPE;

symbol arr: Set →  Set → Set;

injective symbol El: Set → TYPE;

builtin "T" ≔ El;

injective  symbol Prf: Prop → TYPE;

builtin "P" ≔ Prf;


symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 5; // =>
rule Prf ($p ⇒ $q) ↪ Prf $p → Prf $q;

symbol ⊤: Prop;

symbol trivial: Prf ⊤;

constant symbol ∀ [a] : (El a → Prop) → Prop; notation ∀ quantifier; // !! or \forall

constant symbol = [a] : El a → El a → Prop;

notation = infix 10;

constant symbol eq_refl [a] (x: El a) : Prf (x = x);
constant symbol ind_eq [a] [x y: El a] :Prf (x = y) → Π p, Prf (p y) → Prf (p x);

builtin "eq" ≔ =;
builtin "refl" ≔ eq_refl;
builtin "eqind" ≔ ind_eq;

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix left 7; // /\ or \wedge

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix left 6; // \/ or \vee

constant symbol ⊥ : Prop; // \bot

symbol ¬ p ≔ p ⇒ ⊥; // ~~ or \neg
notation ¬ prefix 35;

symbol bar: Prop → Prop;
rule bar ⊥ ↪ bar ⊤;

constant symbol ∃ [a] : (El a → Prop) → Prop; notation ∃ quantifier; // ?? or \exists

opaque symbol foo [a] (x: El a) : Prf (x = x) ≔ eq_refl x;

opaque symbol foo2 [a] (x: El a) : Prf (x = x) ≔ begin
    assume a x;
    have interm: Prf ⊤ {
        apply trivial;
    };
    reflexivity;
    //proofterm;
end;


