import { readdirSync, writeFileSync } from "fs";

/* Only files that are broken *on purpose* (because they're templates
 * meant to be filled out as exercises) should be added here.
 */
const IGNORED_WIKI_FILES = new Set([
  "popl-tutorial-typed-bracket-abstraction",
  "popl-tutorial-basic-error-messages",
  "popl-tutorial-big-step-small-step",
  "popl-tutorial-exceptions-problem",
  "popl-tutorial-minml-encoding",
  "popl-tutorial-minml-preservation-theorem",
  "popl-tutorial-sequent-vs-natural-deduction",
])

/* It's always okay to add more pages here, we're just erring on the side
 * of running in safe mode.
 */
const UNSAFE_WIKI_FILES = new Set([
  "constructivesemantics",
  "double-negation-translation",
  "hereditary-substitution-with-a-zipper",
  "incremental-metatheorem-development",
  "percent-assert",
  "user-hdeyoung-monweakfoc-elf",
  "minmltominhaskell",
  "percent-thaw",
  "polarized-pcf",
  "iterated-inductive-definitions-and-defunctionalization",
]);

const WIKI_TWELF_LOC = "../wiki/src/content/twelf/";
const cfgs = [];
for (const file of readdirSync(WIKI_TWELF_LOC)) {
  if (file.endsWith(".elf")) {
    const base = file.slice(0, file.length - 4);
	 if (IGNORED_WIKI_FILES.has(base))
		continue;
    const cfg = base + ".cfg";
    writeFileSync(WIKI_TWELF_LOC + cfg, file);
    cfgs.push(
      `test${
        UNSAFE_WIKI_FILES.has(base) ? "Unsafe" : ""
      } ${WIKI_TWELF_LOC}${cfg}`
    );
  }
}

writeFileSync("regression-wiki.txt", cfgs.join("\n"));
