/** Prelude inventory seam. Properties tested: every generated atom has an executable
 * case; omitting any whole atom's cases is reported; unrelated cases do not fill a gap.
 * This checks case coverage only. The caller executes the cases to check their results. */
export const preludeInventoryFailures = (
  atomNames: Iterable<string>,
  cases: ReadonlyArray<{ readonly atom: string }>,
): string[] => {
  const covered = new Set(cases.map(c => c.atom))
  return Array.from(atomNames).flatMap(atom => covered.has(atom) ? [] :
    [`atom ${atom} is in the profile's atom set and has no prelude self-test case`])
}
