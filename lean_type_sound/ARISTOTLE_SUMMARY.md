# Summary of changes for run 8209f1b8-ebc2-4665-8ea9-9987beb70de3
The last three open theorems in `LeanTypeSound/TypeSound.lean` are now proved, so every theorem in the library builds without `sorry`. The full project builds, and all three theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**What was proved**
- `decs_type_sound_no_check`: soundness for declaration lists typed with `extra_checks = false`. If `evaluate_decs st env ds = (st', r)`, the declarations are well-typed and `type_sound_invariant` holds, then `r` is never a type error. There is also an extended constructor map and store typing under which the result is well-typed and the invariant holds again.
- `decs_type_sound`: the same statement for either setting of `extra_checks`.
- `semantics_type_sound`: a well-typed program never has behaviour `Fail`.

**How**
The proof follows the HOL4 argument in `hol4-ultramin/typeSoundScript.sml`, but goes by induction on the typing derivation (`type_ds`/`type_d`) rather than on the evaluator. That makes the main lemma `decs_sound_all` hold for any value of the extra-checks flag, so both declaration theorems follow from it directly. There is one lemma per kind of declaration (`let`, `letrec`, type definitions, type abbreviations, exceptions, modules, `local` blocks), plus the empty and multi-declaration list cases. They are added to `TypeSound.lean` just before `decs_type_sound_no_check` and reuse lemmas already in the project. As a result `TypeSound.lean` is now about 1,150 lines.

**Other changes**
- I deleted `LeanTypeSound/S6.lean` and `LeanTypeSound/T1.lean`. They were not part of the library build and only held unfinished attempts with `sorry`. S6 was an attempt at the theorem now proved, and T1 at a result already proved in `TypeSoundCore.lean` (`eq_same_type_v`).
- The only remaining `sorry` text is in `Misc.lean`, inside comments around the original `tlookup_bij_suff` / `tlookup_bij_iff` statements. Earlier work showed those originals were false as translated and replaced them with corrected, proved versions.

# Summary of changes for run 99e764f8-3826-448f-9f07-d00331a3c213


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.

# Summary of changes for run 1fcc523c-f855-41f7-ac48-ff565ade4ffa


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.

# Summary of changes for run 3de119a0-914c-4b13-a97e-cf55c9732999


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.

# Summary of changes for run 9498a797-0bc1-4b95-a6d1-820dba615b28


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.