# Starting from an empty or partial repository

Read this when the target has no working Lean project. First perform the instruction and source discovery in `SKILL.md`; a folder with only a blueprint or some Lean files is a partial project, not disposable scaffolding. Its generic file-creation, `Auto/`, single-file, namespace, and header requirements apply to bootstrapping too. The minimal project configuration files are automatically authorized under the project-configuration exception in `SKILL.md`.

## Establish a reproducible environment

1. Inspect the directory, any ancestor Git repository or worktree, and available tools (`lean`, `lake`, `elan`). If no Git repository owns the directory, initialize one with `git init`, leaving its history empty and making no initial commit or automatic staging. As part of initialization, create an empty root `README.md`, copy [../assets/LICENSE](../assets/LICENSE) to root `LICENSE`, and copy [../assets/.gitignore](../assets/.gitignore) to root `.gitignore`. These files are already authorized by the initialization rule. Preserve any existing versions instead of overwriting them; merge needed ignore patterns into an existing `.gitignore`. Identify existing `lean-toolchain`, `lakefile.toml` or `lakefile.lean`, `lake-manifest.json`, Lean sources, and source documents before generating other files. Do not initialize over or replace existing work.
2. Use Lean 4 and Mathlib unless the user or project specifies otherwise. Preserve any existing compatible pins. If pins are absent, select a mutually compatible Lean toolchain and Mathlib revision using the installed tooling and authoritative project documentation; do not hard-code a remembered latest release. Record the exact selection. A nearby warm checkout may inform the choice, but must not silently become a machine-specific dependency.
3. Determine the exact missing setup files and the single formalization file before initializing. Create the minimal project configuration files automatically under the standing exception in `SKILL.md`, without asking for file-creation approval. For other files, check the applicable authorization. Use the Mathlib project template supported by the selected Lake version only if its generated files fit that authorization and it will not create commits, after checking its help; disable automatic commits or choose manual setup when necessary. Otherwise create the minimal matching configuration by hand. The standard top-level library import file is required and already authorized; do not let a template generate other unauthorized extra Lean files. If the directory already contains files, add only the authorized missing configuration and integrate it without overwriting existing work. Keep the library root at its default whole-module name and create or maintain the corresponding top-level import file under the standing exception in `SKILL.md`. Add imports for the production modules; never set `roots` to individual proof files or use `globs` to bypass this structure. Preserve reproducible dependency pins and appropriate build/cache ignores. Git history must remain unchanged unless the user explicitly instructs otherwise; configuring a remote or publishing is separate work.
4. Fetch dependencies and the matching prebuilt Mathlib cache through the project's supported commands. Retain the dependency manifest and toolchain pins. Do not upgrade an existing environment, run repeated cache downloads, or rebuild all of Mathlib without evidence that it is necessary. Respect execution and installation permissions; do not turn a setup problem into invented proof assumptions.
5. Build the authorized formalization file importing Mathlib before substantial proof work. Include the required header and place its Lean code inside `namespace Auto ... end Auto`. Keep the verification result in the authorized continuation record. If tools or dependencies are unavailable, inspect the source and prepare the precise plan and missing-setup diagnosis; do not present uncompiled Lean as validated.

## Choose a small project structure

Use any user-provided or existing package/module name. Otherwise choose a descriptive Lean package name. The default is one Lean source file in `Auto/`, with all definitions and proofs in the namespace `Auto`. For a package whose source files live under `Project/`, a proposed minimal structure is:

```text
README.md                    # initially empty
LICENSE                      # bundled Apache 2.0 text
.gitignore                   # bundled Lean/Lake/LaTeX patterns
lean-toolchain
lakefile.toml                 # lean_lib Project; omit roots and globs
lake-manifest.json
Project.lean                  # imports Project.Auto.MainResult and other production modules
Project/
  Auto/
    MainResult.lean          # all formalization code, in namespace Auto
automation/
  instructions.md
  raw.md                     # timestamped raw prompts; ignored by Git
  Status.md
  ErrorReport.md             # when a discrepancy needs recording
sources/                     # paper input, if it needs a local home
```

This layout does not itself authorize arbitrary setup files; apply the file-creation rules and standing authorizations in `SKILL.md`. Reuse established source locations such as `blueprint/` or `blueprints/`, but the instructions, status, and error-report Markdown files must reside in `automation/`. Bring any active legacy records from `meta/` or elsewhere into `automation/`, preserving their history and updating references rather than starting competing records. A root-level `Auto/MainResult.lean` is also suitable when that matches the project's source root. Keep ordinary prerequisites and helpers in the single authorized formalization file; do not add `Basic.lean` or section modules merely for convenience. The standard top-level library import file is required under its explicit standing exception, even when there is only one formalization file. When a substantial missing general fact qualifies under `SKILL.md`'s reusable-prerequisites exception, create exactly one dedicated file directly in `Auto/`, with no subfolders or companion files, without seeking authorization again. Its theorem statement and local defining vocabulary must depend only on Mathlib and definitions local to that same file. Document the justification and work in `automation/Status.md`, and include the file in the build through the main file's imports. Do not pre-create speculative prerequisite files during setup. An `aux_` prefix or private-only helpers remain local conventions, but `Auto/`, the namespace `Auto`, the single-file default with its reusable-prerequisites exception, and the required generation notice are generic requirements.

For every Lean file in `Auto/`, follow the standard header in `SKILL.md`: line 1 is the copyright notice including the year and the copyright holder's name (the user's established name, never omitted or left as a placeholder), with the opening `/-` on that same line, line 2 is the license notice, and line 3 is exactly `This file was automatically generated by Codex.`. Close with `-/` on the next line. No blank lines or other content precede or separate those three lines. Put imports after the header and before `namespace Auto`. Use the project's actual legal notices and preserve existing attribution.

Retain original source names, labels, and version information. For online sources, record the verified URL and version/date. Prefer source TeX when available; keep paper PDFs usable without requiring TeX conversion. Never replace a supplied blueprint with a newly generated one simply to fit this layout.

## Leave enough local guidance to resume

In `automation/instructions.md` (or the existing capitalization/effort-specific name within `automation/`), record:

- The exact source(s), intended main statements, scoped prerequisites, and explicit exclusions.
- The authorized files, the main formalization file and any qualifying reusable-prerequisite files under `Auto/`, the `Auto` namespace, any user-specified exceptions, toolchain/dependency pins, and tested build commands.
- The paths to the status and error-report files within `automation/`, and their conventions.
- Any substantive interpretation of the source or local implementation choice.
- The selected next source item, required dependencies, and any real setup blocker.
- Each task-specific user prompt in distilled form with its timestamp and a pointer to its raw entry in `automation/raw.md`, as required by `SKILL.md`; record the initial request before implementing it and preserve subsequent corrections and decisions. All timestamps use the computer's local timezone with the appropriate UTC offset. The latest specific user instructions override conflicting earlier instructions and this skill.

Keep the raw prompt log in `automation/raw.md` and ensure `automation/raw.md` is included in the root `.gitignore` by default, including when resuming an existing repository. Move any embedded raw log there, preserving timestamps and wording except for required path normalization. Never write absolute filesystem paths to any files; use repository-relative or user-directory-relative paths such as `~/.codex`, including in raw prompts and saved commands.

If there is no existing agent entry point, propose a short root `AGENTS.md` pointing future agents to these instructions and the status ledger; create it only when authorized. Do not copy the entire global skill into the repository or turn tentative decisions into immutable user restrictions.

Read the target proofs and populate the ledger before implementing their steps. Put main theorem statement rows first, reusable-prerequisite sections with their justifications and work rows immediately afterward, and main-proof rows after those sections. Initial rows are `not started` unless actual source inspection and verification establish otherwise. When starting directly from a paper, this ledger and the precise statements in continuation notes provide a working proof plan; a separate publication-ready blueprint, website, dependency visualization, or submission package is unnecessary unless requested.

Once setup is complete, continue through the ledger one logical work item at a time until all scoped main results are fully proved and pass the standard-axiom and build checks. Record every source/formalization discrepancy concisely with a timestamp and resolution in `ErrorReport.md`. If resolving a discrepancy requires changing the mathematics of a main result, stop, report, and ask for the user's direction, as required in `SKILL.md`.
