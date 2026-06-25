---
name: autoformalize
description: Lean formalization workflow for filling user-specified `sorry`s, especially in files with an AI-generated `namespace Codex` scaffolding around target declarations. Use when the user invokes `/autoformalize`, asks Codex to prove Lean sorries, continue an autoformalization, or formalize arguments from mathematical sources while preserving target theorem statements.
---

# Autoformalize

Fill `sorry`s as requested by the user, using the mathematical hints and sources indicated by the user when needed.

## Scope Rules

- Modify only the target file explicitly named by the user, or the single file clearly in scope from the conversation.
- Except for imports, modify code only inside lexical `namespace Codex ... end Codex` blocks in the target file.
- You may add or adjust imports in the target file when necessary, but imports you add must not be marked `public`. Do not turn an import into a `public import`.
- Do not refactor unrelated code, move unrelated declarations, or clean unrelated warnings.

## Declaration Rules

- Existing declarations marked `private` are AI-generated scaffolding. You may modify, replace, or delete them as needed, but only to support the requested target proof.
- Declarations not marked `private` are target declarations. Do not change their names, statements, hypotheses, visibility, attributes, namespace placement, or surrounding structure. You may however make any changes to their proofs and your task is to eventually eliminate all `sorry`s.
- Any new declaration you introduce, including definitions, abbrevs, lemmas, and theorems, must be marked `private`.

## Workflow

- Work on `sorry`s in `namespace Codex` one by one, from top to bottom, unless the user specifies a different target.
- Before proving a `private` sorry, check whether the statement is actually needed and mathematically sensible.
- If a `private` statement is false, malformed, too strong, or not useful for the target proof, revise or delete it before moving on.
- If a non-private target statement appears false or impossible under the stated assumptions, do not change it. Report the obstruction clearly.
- Keep the proof plan aligned with the mathematical argument indicated by the user or source.

## Validation

- After edits, run the appropriate Lean check for the target file.
- If the final target theorem is meant to be sorry-free, verify that it no longer depends on `sorryAx`, for example with `#print axioms` when appropriate.
- Report any remaining axioms, skipped checks, or blockers honestly.