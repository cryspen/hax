---
weight: 103
---

# The hax→ProVerif sub-language

This page describes the Rust sub-language that the hax ProVerif backend
currently extracts, the ProVerif shape it produces, and the idiomatic
Rust patterns it does **not** accept today. It is descriptive (not
prescriptive): everything below is what the toolchain does as of Stage
2.0 (uniform-bitstring encoding) on top of the Stage 1 port to the
rust-engine architecture.

> **Disclaimer.** The ProVerif backend is experimental. See the [open
> issues](https://github.com/cryspen/hax/issues?q=is%3Aissue+state%3Aopen+label%3Aproverif)
> for known limitations.

## At a glance

Every crate produces a `lib.pvl` model file and a companion
`missingdecl.pvl` diagnostic. `lib.pvl` opens with a short comment
header and then holds one declaration per Rust item. The shared symbols
it builds on — the public channel `c`, a `construct_fail` sink,
`bitstring_default`/`bitstring_err`/`bool_default`/`bool_err`, the
`Some`/`None`/`True`/`False` constructors, the small integer constants
`nat_0 .. nat_16`, and opaque `logical_and`/`logical_or` — are declared
in the `primitives.pvl` library that ships with hax and is passed with
`-lib`. The type model is deliberately uniform:

- **Every Rust type collapses to ProVerif `bitstring`.** Integers,
  booleans, strings, tuples, vectors, arrays, slices, references,
  associated types, type parameters — they all share one ProVerif
  surface type.
- **Booleans** become the data constructors `True()` and `False()`
  declared in `primitives.pvl` (`bool` is not used as a ProVerif type).
- **Integer literals** each become their own opaque constant `nat_N`
  (`nat_neg_N` when negative); `nat_0 .. nat_16` are declared in
  `primitives.pvl` and larger values land in `missingdecl.pvl`.
- Each user-defined `struct`/`enum` gets one `fun ... : bitstring
  [data].` constructor per variant, plus per-field `reduc forall ...;`
  accessor lines. No more per-type `type`, `_to_bitstring`/
  `_from_bitstring` converters, `_default_value` const, or
  `_default`/`_err` letfun cluster — `primitives.pvl` provides universal
  `bitstring_default`/`bitstring_err`.

That uniformity is by design: a ProVerif model wants symbolic crypto
algebra, not Rust's value-level arithmetic. The trade-off is that any
Rust code which *reasons* about bytes, integers, or generics —
hashing, key derivation, length-prefixed parsing, nonce arithmetic —
extracts as opaque function symbols with no equations attached. The
[Stage 2 priorities](#stage-2-priorities) section sketches which of
these gaps the upcoming protocol DSL will plug.

## The accepted sub-language, in one figure

The grammar below is *informal BNF*: it shows what shapes round-trip
through extraction, ignoring trivia (visibility, attributes,
lifetimes, etc.) which the pipeline silently drops. A construct
labelled **`(dropped)`** is parsed, transformed away, and contributes
nothing to the output; one labelled **`(rejected)`** stops extraction
with a diagnostic.

```bnf
crate         ::= item*

item          ::= "fn" name "(" param,* ")" "->" ty "{" expr "}"          ; → letfun (every param `: bitstring`)
                | "fn" name "(" ")" "->" ty "{" expr "}"                  ; → `const f: bitstring.`
                | "#[pv_constructor]" "fn" name "(" param,* ")" "->" ty   ; → `fun NAME(bitstring,...): bitstring [data].`
                | "#[pv_handwritten]" "fn" name "(" param,* ")" "->" ty   ; body replaced by `bitstring_default()`
                | "struct" name "(" ty,* ")"                              ; tuple struct
                | "struct" name "{" field,* "}"                           ; record struct
                | "enum"   name "{" variant,* "}"
                | "#[hax_lib::opaque]" type-or-fn-item                    ; skips destructor lines
                | "type"   name "=" ty                                    ; (dropped)
                | "trait"  ...                                            ; (dropped)
                | "impl"   ... "{" impl-item* "}"                         ; (dropped)
                | "mod"    name "{" item* "}"                             ; flattened, prefixed by `name__`
                | hax_lib::proverif_{replace,before,after}!("...")        ; → verbatim ProVerif

variant       ::= name                  ; nullary
                | name "(" ty,* ")"     ; tuple variant
                | name "{" field,* "}"  ; record variant

field         ::= name ":" ty

param         ::= "_"           ":" ty  ; → wildcard
                | name          ":" ty
                | "mut" name    ":" ty  ; (mutable → SSA via Local_mutation)
                | "&" ...               ; (& dropped by Drop_references)

ty            ::= "bool"                              ; → bitstring
                | iN | uN | "usize" | "isize"         ; → bitstring
                | "()" | "(" ty,+ ")"                 ; → bitstring
                | "[" ty ";" expr "]" | "[" ty "]"    ; → bitstring
                | "Vec<" ty ">"                       ; → bitstring
                | "&str" | "String" | "char"          ; → bitstring
                | "f32" | "f64"                       ; → bitstring (floats lossy)
                | "Option<" ty ">"                    ; → bitstring (Some/None in primitives.pvl)
                | "Result<" ty "," ty ">"             ; → bitstring (Ok→inner, Err→bitstring_err())
                | path-ty "<" ty,* ">"                ; → bitstring (no per-type `type` decl)
                | "&" ty | "&mut" ty                  ; (dropped)
                | "dyn" trait-bound                   ; (rejected)
                | type-param-name                     ; → local ident (Specialize is **not** yet on)

expr          ::= literal
                | local-id | path
                | expr "(" expr,* ")"                                     ; opaque call
                | "(" expr,* ")"                                          ; (rejected: tuples are bitstring)
                | "if" expr "{" expr "}" ("else" "{" expr "}")?           ; → `let (=True()) = cond in ... else ...`
                | "match" expr "{" arm+ "}"                               ; → if-let chain
                | "let" pat ":" ty "=" expr ";" expr
                | constructor "(" expr,* ")"
                | constructor "{" field-init,* "}"
                | "Some(" expr ")" | "None"                               ; → `Some(x)` / `None()` (no `_to_bitstring` wrap)
                | "Ok("   expr ")" | "Err(" expr ")"                      ; Ok→inner, Err→`bitstring_err()`
                | expr "?"                                                ; survives via Simplify_question_marks
                | expr "&&" expr | expr "||" expr                         ; → opaque `logical_and(x,y)` / `logical_or(x,y)`
                | "&" expr | "&mut" expr | "*" expr                       ; (dropped)
                | "[" expr,* "]" | "[" expr ";" expr "]"                  ; (rejected: arrays)
                | "loop" ... | "while" ... | "for" ...                    ; (rejected)
                | "|" param,* "|" expr                                    ; (rejected: closures)
                | "break" | "continue" | "return" expr                    ; (rejected)
                | "unsafe" "{" expr "}"                                   ; (rejected)

  ; Special-cased identity passthroughs (do not appear in the output):
  ;   Clone::clone(x), <[_]>::unsize(x), Deref::deref(x), cast_op(x), Into::into(x)  → x
  ; Special-cased conversions:
  ;   rust_primitives::hax::never_to_any() → bitstring_err()

arm           ::= pat "=>" expr ("," | )                ; "if pat = scrutinee in body" joined with `else`
                | pat "if" guard "=>" expr              ; (rejected: match guards)

pat           ::= "_"                                   ; → wildcard: bitstring
                | local-id                              ; → local-id
                | local-id "@" pat                      ; (rejected: as_pattern)
                | "&" pat | "ref" pat                   ; (rejected/dropped)
                | literal                               ; → =literal (booleans become `=True()` / `=False()`)
                | "Some(" pat ")" | "None"              ; → `Some(inner)` / `None()` (inner not wrapped)
                | "Ok("   pat ")"                       ; → just inner (Result unwrapped)
                | constructor "(" pat,* ")"
                | constructor "{" field-pat,* "}"
                | pat "|" pat                           ; (rejected: or-patterns)
                | "[" pat,* "]"                         ; (rejected: array patterns)
```

### Notes on the figure

- `path` segments are joined with `__` (e.g. `mycrate__a__write_ping`).
  ProVerif reserved keywords are escaped with a leading underscore.
- `name @ pat`, or-patterns, array patterns, and match guards exist in
  Rust but the hax feature gate rejects them (`engine/backends/proverif/proverif_backend.ml:53-65`).
- `&T`, `&mut T`, blocks `{ ... }`, mutable locals, and lifetime
  annotations all *parse* but are erased by phases (`Drop_references`,
  `Drop_blocks`, `Local_mutation`); their information is lost.
- Arbitrary `loop`/`while`/`continue`/`return`/`break`/closures are
  rejected by the feature gate. Range-based `for x in 0..n` survives
  `Reconstruct_for_loops` but only inside specific shapes that yield
  to functionalization; in practice protocol code rarely uses these.

## Output shape

### The shipped `primitives.pvl` library

`lib.pvl` builds on the symbols below, declared in the `primitives.pvl`
library that ships with hax and is `-lib`'d in:

```proverif
channel c.

fun construct_fail() : bitstring
reduc construct_fail() = fail.

const empty: bitstring.
letfun bitstring_default() = empty.
letfun bitstring_err() = let x = construct_fail() in bitstring_default().

fun Some(bitstring): bitstring [data].
fun None(): bitstring [data].
letfun Option_err() = let x = construct_fail() in None().

fun True(): bitstring [data].
fun False(): bitstring [data].
letfun bool_default() = False().
letfun bool_err() = let x = construct_fail() in False().

const nat_0: bitstring.
const nat_1: bitstring.
(* ... through nat_16 ... *)

fun logical_and(bitstring, bitstring): bitstring.
fun logical_or(bitstring, bitstring): bitstring.
```

Integer literals never use ProVerif's built-in unary `nat` (which
overflows on large constants); each literal is its own opaque constant
`nat_N` sitting directly in the `bitstring` universe next to crypto
terms. `primitives.pvl` declares `nat_0 .. nat_16` so that `+ 1` / `- 1`
reduces over them (small loop and epoch counters progress); any larger
literal is auto-declared in `missingdecl.pvl`. `True()`/`False()` play
the same lifting role for booleans, and `logical_and`/`logical_or` are
declared opaque (no equations) — Rust short-circuit `&&`/`||` is treated
as an uninterpreted operator.

### Per-Rust-item rendering

| Rust | ProVerif |
|---|---|
| `fn f() -> T { e }` (empty params) | `const f: bitstring.` |
| `fn f(p1: T1, ..., pn: Tn) -> T { body }` | `letfun f(p1: bitstring, ..., pn: bitstring) = body.` |
| `#[pv_constructor] fn f(...) -> T { _ }` | `fun f(bitstring, ..., bitstring): bitstring [data].` |
| `#[pv_handwritten] fn f(...) -> T { _ }` | `letfun f(...) = bitstring_default().` with a `REPLACE` comment |
| `struct S { f1: T1, f2: T2 }` | `fun S__S(bitstring, bitstring): bitstring [data].` + two `reduc forall ...; accessor_S__S__fi(S__S(...)) = fi.` lines |
| `enum E { V1(T), V2 }` | one `fun`+`reduc` pair per variant (each returning `bitstring`) |
| `#[hax_lib::opaque]` on a type | nothing emitted |
| `mod m { ... }` | flattened; items prefixed by `m__` |
| `type T = U` / `trait`/`impl` | nothing emitted |
| `hax_lib::proverif_replace!("...")` and friends | the string spliced verbatim |

## The phase pipeline

The OCaml engine runs 20 phases before the printer sees the AST
(`engine/backends/proverif/proverif_backend.ml:95-119`). One-line
gloss:

| # | Phase | Purpose |
|---|---|---|
| 1 | `Reject.Unsafe` | rejects `unsafe { ... }` blocks |
| 2 | `Reject.RawOrMutPointer` | rejects `*const T`, `*mut T` |
| 3 | `Transform_hax_lib_inline` | rewrites `hax_lib::*!` macros (asserts, invariants, the `proverif_*` verbatim family) |
| 4 | `Simplify_question_marks` | rewrites `expr?` to an explicit match |
| 5 | `And_mut_defsite` | pushes `&mut` from call site to definition site |
| 6 | `Reconstruct_for_loops` | turns `for x in a..b { ... }` back into a fold-shaped loop |
| 7 | `Direct_and_mut` | resolves `&mut` aliasing into direct mutation |
| 8 | `Reject.Arbitrary_lhs` | rejects assignments whose LHS is more than a path |
| 9 | `Drop_blocks` | flattens `{ stmt; stmt; expr }` |
| 10 | `Drop_references` | erases `&` and `&mut` |
| 11 | `Trivialize_assign_lhs` | normalizes the remaining assignments |
| 12 | `Side_effect_utils.Hoist` | hoists side-effecting sub-expressions to `let`s |
| 13 | `Simplify_match_return` | rewrites `let pat = match { ... => return ... }` |
| 14 | `Local_mutation` | rewrites mutable locals into SSA |
| 15 | `Reject.Continue` | rejects `continue` |
| 16 | `Reject.Dyn` | rejects `dyn Trait` |
| 17 | `Reorder_fields` | sorts struct fields per `#[order(...)]` |
| 18 | `Bundle_cycles` | groups items into mutually-recursive cycles |
| 19 | `Sort_items_namespace_wise` | orders items so dependees come before dependents |
| 20 | `SubtypeToInputLanguage` | the final feature gate (see below) |

Plus, on the Rust side, `FilterUnprintableItems` drops anything still
flagged as un-extractable.

The final feature gate rejects, with a clear diagnostic, any AST node
that still mentions: `loop` / `for_loop` / `while_loop` /
`for_index_loop` / `state_passing_loop`, `continue` / `break`,
`mutable_variable` / `mutable_reference` / `mutable_pointer` /
`reference` / `raw_pointer`, `as_pattern`, `nontrivial_lhs` /
`arbitrary_lhs`, `lifetime`, `monadic_action` / `monadic_binding`,
`fold_like_loop`, `block`, `dyn`, `match_guard`, `trait_item_default`,
`unsafe` (`engine/backends/proverif/proverif_backend.ml:40-65`).

## Attribute & macro surface

### `hax_lib` attributes the printer reacts to

| Macro the user writes | Attached `AttrPayload` | Effect at print time |
|---|---|---|
| `#[hax_lib::pv_constructor]` | `PVConstructor` | the `fn` renders as `fun NAME(bitstring,...): bitstring [data].` with a `(* marked as constructor *)` comment |
| `#[hax_lib::pv_handwritten]` | `PVHandwritten` | letfun body replaced by `bitstring_default()` with a `REPLACE by handwritten model` comment |
| `#[hax_lib::process_read]` | `ProcessRead` | **parsed, not yet rendered** — reserved for the Stage 2 protocol-process model |
| `#[hax_lib::process_write]` | `ProcessWrite` | **parsed, not yet rendered** |
| `#[hax_lib::process_init]` | `ProcessInit` | **parsed, not yet rendered** |
| `#[hax_lib::protocol_messages]` | `ProtocolMessages` | **parsed, not yet rendered** — meant to mark the message enum |
| `#[hax_lib::opaque]` | `Erased` | on a `type` item, skips the destructor `fun`+`reduc` lines |

### Verbatim-injection macros

Concrete ProVerif code is spliced in via a cross-backend family of
quoting macros that expand into `ItemKind::Quote { ... }`:

- `hax_lib::proverif_replace!("...")` — replace this item's
  ProVerif extraction wholesale
- `hax_lib::proverif_replace_body!("...")` — replace just the body
- `hax_lib::proverif_before!("...")` / `hax_lib::proverif_after!("...")`
  — splice ProVerif before/after the item
- `hax_lib::proverif_expr!("...")` — splice into an expression
  position

This is currently the *only* way to import real ProVerif crypto
primitives. There is no shipped `proof-libs/proverif/` runtime
library; the `proverif-noise` example wires `enc`/`dec`/`mac`/`hash`/
DH/HKDF in by hand.

### The `hax_lib_protocol` runtime

The companion crate ships a small state-machine trait surface that
the `hax_lib_protocol_macros` proc-macros translate into the
`Process*` attributes above:

| Macro | Generates |
|---|---|
| `#[init(StateType)]` | `#[hax_lib::process_init]` + `TryFrom<Vec<u8>>` + `InitialState` impl |
| `#[init_empty(StateType)]` | `#[hax_lib::process_init]` + an `InitialState` impl that requires an empty prologue |
| `#[write(Cur, Next, Msg)]` | `#[hax_lib::process_write]` + `TryFrom<Cur>` + `WriteState` impl |
| `#[read(Cur, Next, Msg)]` | `#[hax_lib::process_read]` + `TryFrom<(Cur, Msg)>` + `ReadState<Next>` impl |

Runtime types (`hax_lib_protocol::state_machine`):

- `InitialState`: `init(prologue: Option<Vec<u8>>) -> ProtocolResult<Self>`
- `WriteState` (associated types `NextState`, `Message`):
  `write(self) -> ProtocolResult<(NextState, Message)>`
- `ReadState<NextState>` (associated type `Message`):
  `read(self, msg) -> ProtocolResult<NextState>`

Plus `ProtocolError` (`CryptoError` / `InvalidMessage` /
`InvalidPrologue`) and `ProtocolResult<T> = Result<T, ProtocolError>`.

Crypto helpers (`hax_lib_protocol::crypto`) used by
`proverif-noise`: `DHScalar`, `DHElement`, `DHGroup::X25519`,
`AEAD::ChaCha20Poly1305`, `Hash::SHA256`, `HMAC::HMACSHA256`, `HKDF`
— each wired through `proverif_replace` to ProVerif primitives.

## Idiomatic Rust *not* currently accepted

Things a working cryptographer writing a Rust protocol will reach for
and find missing. Grouped by failure mode.

### Hard rejections — feature gate refuses

Trying these will stop extraction with a diagnostic:

- Mutable variables / references / pointers (`let mut x; x = ...`,
  `&mut T`, raw pointers)
- `for x in iter`, `while`, `loop` — only `for x in start..end`
  survives, and only inside fold-shaped bodies
- `continue` / `break` / `return` with values or labels (except via
  the early-exit phase)
- Closures (`|x| ...`, `move ||`)
- `unsafe` blocks
- `dyn Trait`
- Match guards (`Some(v) if v > 0 =>`)
- As-patterns (`Foo(x @ Some(_))`)
- Or-patterns (`Foo | Bar => ...`)
- Trait item defaults (methods with default impls)

### Soft drops — transformed away silently, information lost

- `&T` → `T` (often what you want for a value model, but lossy)
- `{ stmt; stmt; expr }` flattened by `Drop_blocks`
- `let mut x; x = ...; ...` → SSA via `Local_mutation`
- `'a` lifetimes — dropped entirely

### Renders as opaque `bitstring` / opaque function symbol

- `+`, `-`, `*`, `/`, `<`, `==`, `<<`, `&`, … on integers render as
  opaque function symbols (`core__ops__arith__Add__add(x, y)` etc.)
  over `bitstring`. No algebraic equations are declared.
- All integer types collapse to `bitstring`, and each integer literal
  is its own opaque `nat_N` constant; widths and overflow semantics are
  erased.
- Tuples `(a, b)` collapse to `bitstring`, with no projection or
  destructuring.
- `[u8; N]`, `&[u8]`, `Vec<u8>` all collapse to `bitstring`; no
  `.len()`, no indexing, no `.concat()`, no `.copy_from_slice()`.
- `String`, `&str`, `char`, `f32`, `f64` all collapse to `bitstring`.
- Generics: type parameters render as their local name, but
  `Specialize` is **not** in the phase pipeline, so generic function
  calls do not get monomorphized.
- Traits are entirely dropped; method calls render as opaque function
  calls against the trait name.
- `.unwrap()`, `.map_err()`, `.and_then()` etc. become opaque calls
  — they are not resugared to ProVerif if-let or match.
- Iterator chains (`.iter().map().collect()`) depend on closures +
  traits + arithmetic; all gone.

### Protocol-idiomatic patterns this hits hard

The above translates into pain in four places that protocol code
spends most of its time:

**Byte-buffer manipulation.** Protocol code is mostly building hash
inputs and parsing message frames. `Vec<u8>::concat`,
`.extend_from_slice`, `.copy_from_slice`, slicing `&data[..32]`, fixed
arrays `[u8; 32]`, endianness conversions `u32::from_le_bytes`,
bitwise XOR for keystreams — all collapse to opaque function symbols
or refuse to extract.

**Crypto-API ergonomics.** Builder patterns (`Mac::new(key)
.update(&data).finalize()`) depend on traits; output buffers
(`&mut [u8]`) depend on mutable references; associated constants
(`Cipher::KEY_LEN`) depend on traits. All gone. The only working
pattern today is per-item `proverif_replace!` strings.

**Error tag preservation.** `?` on `Result` works syntactically, but
the resulting `Result<T, E>` collapses to its `Ok` type, with every
`Err` arm rendering as `bitstring_err()`. So a protocol that
distinguishes `InvalidMessage` from `InvalidMac` for security-relevance
reasoning loses that distinction symbolically.

**Numeric reasoning.** Every integer is a `bitstring`, and each literal
is an opaque `nat_N` constant. `+ - * /` over them is an opaque function
symbol with no axioms (only `+ 1` / `- 1` on the small `nat_0 .. nat_16`
constants reduces). A constraint like "this nonce must monotonically
increment" cannot be expressed.

## <a name="stage-2-priorities"></a>What the upcoming protocol DSL must address

Mapped to the gaps above, the rough priority for Stage 2 work is:

1. **Crypto primitives library** (`proof-libs/proverif/`) — eliminate
   the per-item `proverif_replace` ceremony for the standard set
   (`enc`/`dec`/`mac`/`hash`/`pk`/`sign`/`kdf`).
2. **First-class events and queries** — the `ProcessRead`/`Write`/
   `Init`/`ProtocolMessages` attributes are parsed today but
   unrendered; close the loop so attribute-tagged items produce real
   ProVerif `event`, `query`, and process declarations.
3. **Result-flow with preserved error tags** — let users opt in to
   keeping `Err` variants distinct so security-relevant error paths
   stay distinguishable in the model.
4. **A minimal bytestring algebra** — concatenation, length-prefixed
   parse/serialize, constant-time-equal — so that message
   serialization stops being one giant opaque blob.
5. **Generics by specialization** — `Specialize` is in the legacy
   phase set; turning it on for ProVerif unlocks `fn handshake<H:
   Hash>(...)`-style protocol code.
6. **(Deferred)** numeric-width modeling, loops, closures, traits as
   first-class objects.

## What round-trips today

The five test crates under `tests/proverif-*/` are the regression
suite. Each one has a committed `expected.pvl` baseline; the
snapshot test at `rust-engine/tests/proverif_snapshot.rs` will catch
any drift.

- **`proverif-minimal`** — one `fn add(left, right) -> usize`.
  Confirms letfun generation and the opaque-arithmetic rendering of
  `+`.
- **`proverif-basic-structs`** — a tuple struct, a multi-field record
  struct, and a single-field record struct. Confirms the `fun [data]`+
  `reduc` destructor schema (the legacy `type`/converter/default/err
  cluster is gone post-Stage-2.0).
- **`proverif-fn-to-letfun`** — several `fn`s with let-chains,
  unit-returning bodies, and wildcard parameters. Confirms `let ...
  in` chaining and `_ : ()` parameter handling.
- **`proverif-ping-pong`** — two state machines (`A0→A1→A2`,
  `B0→B1→B2`), a `protocol_messages`-tagged enum, and `init`/`read`/
  `write` macros from `hax_lib_protocol_macros`. The state-machine
  pattern extracts end-to-end, but the `Process*` attributes are not
  yet rendered specially — they extract as ordinary letfuns named for
  the state transition.
- **`proverif-noise`** — Noise KKpsk0 handshake. Real protocol
  shapes, with X25519 / ChaCha20-Poly1305 / SHA-256 / HMAC / HKDF
  primitives wired through `proverif_replace`.

To run a single example manually:

```bash
cd tests/proverif-ping-pong
cargo hax into proverif
# →  proofs/proverif/extraction/lib.pvl
```

### Scoping extraction with `-i`

hax computes item reachability from the `-i` include clauses
(`engine/lib/dependencies.ml`): `+NAME` includes an item together with
its transitive dependencies, `-NAME` excludes an item, and `+:NAME`
keeps only its signature. With **no** `-i`, every item defaults to
*included*, so nothing is pruned — every function in the crate becomes a
root and is emitted into `lib.pvl`. To get dead-code elimination (so the
model holds only the protocol under study), narrow `-i` to the entry
points and let transitivity pull in the rest:

```bash
cargo hax into -i '-** +your_crate::protocol::**' proverif
```

One gap to be aware of: the dependency graph is built over the **source**
call graph, *before* a `proverif::replace_body` rewrites a body. A helper
that the original body called stays a transitive dependency and is
emitted even when the replacement body no longer references it. Prune
such a helper with an explicit `-NAME` if it is unwanted in the model.

To run the snapshot tests (requires a full local hax toolchain):

```bash
HAX_PROVERIF_SNAPSHOT_RUN=1 \
  cargo test -p hax-rust-engine --test proverif_snapshot
```

## Pointer to source

| Claim | File |
|---|---|
| Printer (per-AST-node rendering) | [`rust-engine/src/backends/proverif.rs`](https://github.com/cryspen/hax/blob/main/rust-engine/src/backends/proverif.rs) |
| `lib.pvl` comment header | [`rust-engine/src/backends/proverif.rs` `HEADER`](https://github.com/cryspen/hax/blob/main/rust-engine/src/backends/proverif.rs) |
| Shipped library (the declarations above) | [`hax-lib/proof-libs/proverif/primitives.pvl`](https://github.com/cryspen/hax/blob/main/hax-lib/proof-libs/proverif/primitives.pvl) |
| `fn ty`, `fn pat`, `fn expr`, `fn item` | [`rust-engine/src/backends/proverif.rs`](https://github.com/cryspen/hax/blob/main/rust-engine/src/backends/proverif.rs) |
| Phase pipeline | [`rust-engine/src/backends/proverif.rs` `fn phases`](https://github.com/cryspen/hax/blob/main/rust-engine/src/backends/proverif.rs) |
| Feature gate, rejected features | [`engine/backends/proverif/proverif_backend.ml:5-19,40-65`](https://github.com/cryspen/hax/blob/main/engine/backends/proverif/proverif_backend.ml) |
| OCaml phase functor application | [`engine/backends/proverif/proverif_backend.ml:95-119`](https://github.com/cryspen/hax/blob/main/engine/backends/proverif/proverif_backend.ml#L95-L119) |
| `AttrPayload` variants the printer recognizes | [`hax-lib/macros/types/src/lib.rs:142-151`](https://github.com/cryspen/hax/blob/main/hax-lib/macros/types/src/lib.rs) |
| Protocol DSL | [`hax-lib-protocol/`](https://github.com/cryspen/hax/tree/main/hax-lib-protocol), [`hax-lib-protocol-macros/`](https://github.com/cryspen/hax/tree/main/hax-lib-protocol-macros) |
| Worked examples | [`tests/proverif-*/`](https://github.com/cryspen/hax/tree/main/tests) |
| Snapshot test + committed baselines | [`rust-engine/tests/proverif_snapshot.rs`](https://github.com/cryspen/hax/blob/main/rust-engine/tests/proverif_snapshot.rs), `tests/proverif-*/expected.pvl` |
