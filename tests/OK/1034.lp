symbol N: TYPE;

symbol 0: N;

symbol Set: TYPE;
symbol nat: Set;

symbol arr: Set → Set → Set;
injective symbol El: Set → TYPE;

rule El(arr $x $y) ↪ El $x → El $y;
rule El nat ↪ N;

symbol I [a]: N → El a;



symbol code_S : Set;
private symbol S ≔ El code_S;

private symbol a: S ≔ I 0;

// symbol 𝑰 [a]: ℕ → τ a; 
// private symbol code_S : Set;
// private symbol S ≔ τ code_S;
// private symbol a: S ≔ 𝑰 0;