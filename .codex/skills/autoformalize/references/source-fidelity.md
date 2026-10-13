# Checking that Lean proves the intended source result

Use this when translating a source statement, resuming a qualified result, or deciding whether a milestone is complete. Compilation proves the Lean proposition, which still needs to express the intended mathematics.

## Read the complete mathematical contract

Record the exact source label, theorem parts, version, and any surrounding definitions or standing assumptions. Resolve references to earlier statements; check the original cited result when the proof uses it. Use the source PDF to settle extraction errors, lost subscripts, or ambiguous displayed mathematics. If supplied blueprint and paper disagree, preserve the user-designated source and investigate the discrepancy rather than silently mixing versions.

For each target, compare:

- Objects and meanings: spaces, measures, operators, domains, normalizations, function classes, and quotient versus pointwise representatives.
- Quantifiers: order of universal/existential choices, uniformity of constants, and which data a witness or constant may depend on.
- Assumptions: parameter ranges, endpoints, dimensions, regularity, measurability, integrability, positivity, and nondegeneracy.
- Conclusion: exact identity or inequality, strict versus non-strict bounds, pointwise versus almost everywhere statements, equivalence directions, sharpness assertions, and all parts of a multi-part theorem.

An existential constant allowed to depend on the function or scale may destroy a uniform estimate. A bound proved only for smooth functions may still need a density/extension argument. A normalized or restricted model may still need a proved bridge to the actual operator. Check these obligations before declaring a source theorem complete.

## Avoid accidental statements about junk values

Lean defines operations outside the informal domain where mathematicians usually use them. Check the semantics relevant to the statement, especially:

- Division/inverses at zero and real powers or logarithms outside their intended domain.
- Integrals of nonintegrable functions and sums without summability.
- Suprema over empty or unbounded sets, and infima with analogous issues.
- `ENNReal.toReal` at infinity and finite/extended norm conversions.
- Almost-everywhere equivalence versus arbitrary representatives and pointwise assertions.

Add a side condition only when it encodes the source's intended domain or follows from its assumptions. If a convenience hypothesis restricts the source theorem, prove it from those assumptions or keep the restricted lemma as an intermediate result and discharge the missing cases. Do not assume a missing estimate, an operator identity, or the requested conclusion merely because it makes an application typecheck.

## Reuse and source mappings

Search definitions as well as theorem names. A differently named theorem may already supply the whole item; a similarly named theorem may have the wrong hypotheses. Verify the precise declaration in the pinned library, and prove any needed normalization, specialization, transport, or equivalence.

Give every scoped source definition and result an auditable Lean mapping. Several Lean declarations may realize separate parts of one source result; use clear suffixes and document what remains until every part is proved. Direct reuse of a library declaration may be the mapping when its match is explicit; a redundant wrapper is unnecessary unless a public interface or local convention needs one.

Put a faithful statement and exact source location in the corresponding source theorem's docstring. Include supplied manuscript LaTeX where useful and permitted, reformatted for the existing documentation tooling; do not insert an entire proof. A related definition or constant documents itself and refers to the source theorem. Helpers explain the specific role they play without claiming an independent source milestone.

For estimates with explicit or recursively specified constants, preserve the required values and dependencies. Named constant definitions are useful when they prevent downstream proof churn. Do not impose a harmonic-analysis-specific representation, such as raw function maps or a particular norm API, on unrelated mathematics; use the project's established representation and the best matching library interface.

## Classify discrepancies honestly

Record every source/formalization discrepancy in `ErrorReport.md`, including harmless or already resolved differences. Classification determines whether work can proceed; it does not excuse omitting the record.

- **Equivalent formalization:** A representation or convention changes but a proof or precise mathematical justification establishes the intended source claim. The source item may be complete once verified. Check edge cases; an empty-set convention is not automatically harmless.
- **Clear source typo:** Briefly record the exact location, printed expression, correction, and why that correction is forced. Preserve the intended mathematical meaning. If the repair is unambiguous and does not change the main result's mathematical content, continue; otherwise ask before adopting it.
- **Material gap or altered claim:** A stronger assumption, weaker conclusion, missing range, changed constant that the literal result needs, conditional wrapper, or unproved bridge leaves the source item incomplete. Keep any useful partial Lean result and record what is missing. Do not use `complete with qualification` to obscure an unfinished mathematical obligation.

A slightly worse bound can be useful in an intermediate step when it suffices for all consumers. It does not complete a source item specifying a sharper bound. Record the discrepancy and either close that source obligation or obtain an explicit scope revision. A revised proof that reaches the exact main theorem does not retroactively prove skipped source lemmas. If resolution requires changing the mathematical content of a main result, stop the autoformalization and ask the user what to do next; do not continue on other branches or silently adopt a changed target while awaiting direction.

Keep each `ErrorReport.md` entry very brief and to the point: timestamp in the computer's local timezone with its UTC offset, source label/page or TeX line, discrepancy, and how it was resolved (or explicitly `unresolved`). Add a timestamped resolution when an open issue is fixed, using the same local-timezone rule. Include the essential reason a correction is valid, linking to proof documentation for longer analysis rather than expanding the report. Ordinary omitted details supplied faithfully are work to do, not discrepancies by themselves. If a protected existing target appears false, preserve it and present the obstruction or counterexample; do not quietly replace it with a different theorem. When the main result must change, report the issue and wait for the user's decision before proceeding.
