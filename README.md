# Proximity-Based ProbLog Translator

Prototype translator for the proximity-based probabilistic logic programming language.
## Supported language

The translator accepts:

- function-free definite logic programs;
- ground probabilistic facts `p::q(c1,...,cn).` with `p` in `[0,1]`;
- proximity declarations `s1 ~ s2 = p.` between constants;
- ground `query(...)` declarations.


## Translation

1. `p::q(c1,...,cn).` becomes `p::q_aux(c1,...,cn).`
2. `s1 ~ s2 = p.` becomes `p::prox(s1,s2).`
3. Proximity between constants is represented by:

```prolog
equals(X,X).
equals(X,Y) :- prox(X,Y).
equals(X,Y) :- prox(Y,X).
```

4. Definitions of q/n are moved to q_aux/n, and a wrapper with the original predicate name applies equals/2 argument-wise.
5. Atoms in clause bodies keep their original predicate names.
6. Ground queries are unchanged.

For a nullary predicate such as `burglary/0`, the wrapper is:

```prolog
burglary :- burglary_aux.
```

If a source program contains no proximity declarations, it is emitted unchanged, apart from formatting.

## Files

- `translator.pl`: translator and validator
- `cli.pl`: command-line interface
- `main.pl`: interactive interface
- `examples/burglary.plp`: example with probabilistic facts, deterministic clauses, and proximity
- `examples/stress.plp`: proximity/probability example with two proximity declarations on the same constant
- `examples/no_proximity.plp`: example without proximity declarations
- `examples/person_proximity.plp`: deterministic fact with proximity
- `examples/clever_proximity.plp`: probabilistic fact with proximity
- `examples/complete_example.plp`: complete worked example combining probabilistic facts, deterministic rules, and proximity
- `examples/template.plp`: source-language template
- `examples/invalid_examples.plp`: examples of invalid inputs
- `LICENSE`: MIT license

## Requirements

- SWI-Prolog
- ProbLog (required only for probabilistic evaluation)

## Run

```bash
swipl cli.pl -- examples/burglary.plp examples/burglary.pl
python3 -m problog examples/burglary.pl
```

or interactively:

```bash
swipl main.pl
```

## Example results

| Example | Query | Probability |
|---|---|---:|
| `burglary.plp` | `calls(mary)` | 0.44 |
| `burglary.plp` | `calls(maria)` | 0.352 |
| `burglary.plp` | `calls(john)` | 0.44 |
| `no_proximity.plp` | `p(a)` | 0.5 |
| `person_proximity.plp` | `person(mary)` | 1.0 |
| `person_proximity.plp` | `person(maria)` | 0.8 |
| `clever_proximity.plp` | `clever(a)` | 0.6 |
| `clever_proximity.plp` | `clever(b)` | 0.3 |
| `stress.plp` | `smokes(b)` | 0.28 |
| `stress.plp` | `smokes(c)` | 0.32 |
| `template.plp` | `p(b)` | 0.3 |
| `complete_example.plp` | `slippery(grass)` | 0.58 |
| `complete_example.plp` | `slippery(lawn)` | 0.464 |

To run the complete example:

```bash
swipl cli.pl -- examples/complete_example.plp examples/complete_example.pl
python3 -m problog examples/complete_example.pl
```
