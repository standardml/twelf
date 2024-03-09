import { readdirSync, writeFileSync } from "fs";

const UNSAFE_WIKI_FILES = new Set(["constructivesemantics"]);

const WIKI_TWELF_LOC = "../wiki/src/content/twelf/";
const cfgs = [];
for (const file of readdirSync(WIKI_TWELF_LOC)) {
  if (file.endsWith(".elf")) {
    const base = file.slice(0, file.length - 4);
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
