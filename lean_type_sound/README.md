This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# HOL4 to Lean 4 Translation: CakeML Type Soundness

Translation of the 21 HOL4 theory files in `hol4-ultramin/` (the
ultra-minimized CakeML type soundness development) into Lean 4.

## Scope

- **All definitions** are translated with their full bodies.
- **All theorem statements** are translated as `theorem name : stmt := by sorry`.
- **No proofs** are attempted; every proof is `sorry`.
- **All inductive relations** (HOL4 `Inductive`) are translated as Lean
  `inductive` types with one constructor per rule.
- Each translated item is preceded by its HOL4 source in a `/- HOL4: ... -/`
  comment block.

## Building

Requires Lean 4.27.0 (specified in `lean-toolchain`). No Mathlib dependency.

```
lake build
```

## File Inventory (21 source files + 1 prelude)

| # | Lean file | HOL4 source | Lines | Description |
|---|-----------|-------------|-------|-------------|
| 1 | `HOL4Prelude.lean` | (library shim) | 388 | HOL4 primitives not in Lean stdlib |
| 2 | `Location.lean` | `locationScript.sml` | 61 | Source locations |
| 3 | `LprefixLub.lean` | `lprefix_lubScript.sml` | 18 | Lazy list prefix LUB |
| 4 | `FpSem.lean` | `fpSemScript.sml` | 72 | Floating-point semantics |
| 5 | `Misc.lean` | `miscScript.sml` | 242 | Utility definitions |
| 6 | `Mllist.lean` | `mllistScript.sml` | 43 | List sort/nth/collate |
| 7 | `Mlstring.lean` | `mlstringScript.sml` | 289 | ML string type and operations |
| 8 | `Ffi.lean` | `ffiScript.sml` | 145 | FFI types and `call_FFI` |
| 9 | `Namespace.lean` | `namespaceScript.sml` | 212 | Hierarchical namespace type |
| 10 | `Ast.lean` | `astScript.sml` | 333 | CakeML abstract syntax |
| 11 | `SemanticPrimitives.lean` | `semanticPrimitivesScript.sml` | 597 | Values, pattern match, `do_app` |
| 12 | `Evaluate.lean` | `evaluateScript.sml` | 245 | Big-step evaluator |
| 13 | `NamespaceProps.lean` | `namespacePropsScript.sml` | 212 | Namespace lemmas |
| 14 | `SemanticPrimitivesProps.lean` | `semanticPrimitivesPropsScript.sml` | 193 | Semantic primitives lemmas |
| 15 | `EvaluateProps.lean` | `evaluatePropsScript.sml` | 127 | Evaluator lemmas |
| 16 | `TypeSystem.lean` | `typeSystemScript.sml` | 699 | Type system (typing rules) |
| 17 | `TypeSoundInvariants.lean` | `typeSoundInvariantsScript.sml` | 373 | Value typing (`type_v`) |
| 18 | `TypeSysProps.lean` | `typeSysPropsScript.sml` | 369 | Type system properties |
| 19 | `Weakening.lean` | `weakeningScript.sml` | 100 | Weakening lemmas |
| 20 | `TypeSound.lean` | `typeSoundScript.sml` | 123 | Type soundness theorems |
| 21 | `SemanticsMin.lean` | `semantics_minScript.sml` | 53 | Top-level semantics |

## Naming Conventions

| HOL4 | Lean | Reason |
|------|------|--------|
| `id` (module/name identifier) | `cml_id` | `id` is a Lean reserved word |
| `t` (semantic type) | `sem_t` | Too short/generic for Lean |
| `state` (CakeML state) | `cml_state` | `state` conflicts with Lean |
| `namespace` (type) | `«namespace»` | Lean keyword; escaped with guillemets |
| `v` (value) | `v` | Kept as-is (works as inductive name) |
| `sem_env.v` (field) | `sem_env_v` / `v_` | `.v` clashes with value type `v` |
| `fp_cmp` (function) | `fp_cmp_fun` | Clashes with `fp_cmp` datatype |
| `thunk_op` (function) | `thunk_op_fun` | Clashes with `thunk_op` datatype |

## Compromises and Deviations

### 1. Opaque types in HOL4Prelude (all operations are `sorry`)

The following HOL4 types have no Lean stdlib equivalent and are defined as
opaque types with `sorry`-implemented operations:

- **`Finmap α β`** — HOL4 `fmap`. Operations: `FLOOKUP`, `FUPDATE`, `FEMPTY`,
  `FDOM`, `FRANGE`, `FEVERY`, `FUPDATE_LIST`, `o_f`, `alist_to_fmap`,
  `SUBMAP`, `FUNION`.
- **`Sptree α`** — HOL4 `sptree$spt`. Operations: `lookup`, `insert`,
  `delete`, `fromAList`, `domain`, `toList`.
- **`LazyList α`** — HOL4 `llist`. Operations: `LPREFIX`, `fromList`, `toList`.
- **`Set α`** — Defined as `α → Prop` (Lean 4.27.0 has no `Set` without
  Mathlib). Membership, union, intersection, image, disjoint all defined.
- **Word operations** — `word8`/`word64` aliased to `UInt8`/`UInt64`;
  shift and conversion operations (`word_lsl`, `i2w`, etc.) are `sorry`.
- **IEEE 754 floating-point** — `fp64_add`, `fp64_mul`, `fp64_lessThan`, etc.
  are all `sorry` stubs.

### 2. `LIST_REL` is an inductive (not a def)

HOL4's `LIST_REL` is naturally a recursive function on lists. In Lean, it
must be an `inductive` (not `def`) because `type_v` (the value typing
relation) nests `LIST_REL (type_v ...)` in its constructors. Lean's kernel
requires nested occurrences to go through inductives for strict positivity
checking.

### 3. `BEq v` and `BEq sem_env` are `sorry` instances

The mutual inductive `v`/`sem_env` cannot derive `BEq` automatically. Since
other definitions use `==` on values (e.g., `do_eq`, pattern matching), we
provide:
```lean
instance : BEq v := ⟨fun _ _ => sorry⟩
instance : BEq sem_env := ⟨fun _ _ => sorry⟩
```

### 4. Strict positivity workarounds in `type_v`

HOL4's `type_v` inductive uses `LIST_REL (type_v ...)` and
`nsAll2 (...type_v...)` in its premises. Lean enforces strict positivity,
which disallows the datatype being defined from appearing under a non-inductive
function application.

- **`LIST_REL (type_v ...)`** in `conv_some`/`conv_none`: Replaced with
  length equality + index-wise quantification:
  ```lean
  vs.length = ts.length →
  (∀ (i : Nat), i < vs.length → type_v tvs ctMap_ tenvS vs[i]! ts[i]!) →
  ```
  This is logically equivalent but avoids nesting `type_v` inside `LIST_REL`.

- **`nsAll2 (...type_v...)` in `closure`/`recclosure`**: Replaced with
  direct universal quantification over namespace lookups:
  ```lean
  (∀ (id_ : cml_id modN varN) (val_ : v) (p : Nat × sem_t),
    nsLookup (sem_env_v env) id_ = some val_ →
    nsLookup (add_tenvE tenvE tenv.v) id_ = some p →
    type_v p.1 ctMap_ tenvS val_ p.2) →
  ```
  This is strictly weaker than `nsAll2` (it does not assert the two
  namespaces have identical structure), but captures the core typing
  condition. Strengthening to full `nsAll2` equivalence would require
  auxiliary mutual inductives.

### 5. `namespace` inductive uses `List` directly (not `alist`)

HOL4 defines `namespace` with an `alist` (association list) field. In Lean,
defining the `«namespace»` inductive with a type alias caused a kernel error
("non valid occurrence"). The fix is to inline `List (n × v)` directly in
the constructor:
```lean
inductive «namespace» (m n v : Type) where
  | Bind : List (n × v) → List (m × «namespace» m n v) → «namespace» m n v
```

### 6. Termination

Several recursive functions have complex or mutually recursive termination
arguments that are not translated. These use:
- **`partial def`**: `evaluate`, `evaluate_match`, `evaluate_decs`, `pmatch`,
  `pmatch_list`, `do_eq`, `do_eq_list`, `v_to_list`, `v_to_char_list`,
  `sort` (Mllist).
- **`decreasing_by all_goals sorry`**: `every_exp`, `check_freevars`,
  `check_freevars_ast`, `check_type_names`, `is_value`, `nsMap`,
  `nsSub_compute`, `type_name_subst`, `build_constrs`.

### 7. `autoImplicit := false` requires explicit binders

The project uses `set_option autoImplicit false` (Lean 4 default). All
inductive constructors in mutual blocks and standalone inductives must have
explicit `∀` binders for every variable. This is particularly visible in:
- `type_v` (TypeSoundInvariants.lean)
- `type_p`/`type_ps` (TypeSystem.lean)
- `type_e`/`type_es`/`type_funs` (TypeSystem.lean)
- `type_d`/`type_ds` (TypeSystem.lean)

### 8. Remaining `sorry` stubs in SemanticPrimitives

The following functions from `semanticPrimitivesScript.sml` are left
as `sorry`:
- `concrete_v`, `concrete_v_list`, `compiler_agrees`
- `do_eval`, `reset_env_generation`
- `copy_array`
- `do_app` (the main ~200-line case analysis)

`check_type`, `do_test`, `do_arith`, and `do_conversion` are fully translated.

### 9. `type_op` is a `sorry` stub

`type_op` from `typeSystemScript.sml` is a large case analysis assigning
types to each primitive operation. It is left as `def type_op ... : Prop := sorry`.

### 10. `Inhabited` not derivable for some types

`ffi_state` and `cml_state` contain function-valued fields (e.g., `oracle`)
that prevent automatic `Inhabited` derivation. These types do not derive
`Inhabited`. An explicit `Inhabited v` instance is provided (defaulting to
`Litv (IntLit 0)`).

### 11. Theorem stubs are `True` when statement was not translated

Many theorem stubs in properties files (NamespaceProps, SemanticPrimitivesProps,
EvaluateProps, TypeSysProps, Weakening, TypeSound) use `theorem name : True := by sorry`
as a placeholder. The HOL4 statement is preserved in the preceding comment
block for reference.
