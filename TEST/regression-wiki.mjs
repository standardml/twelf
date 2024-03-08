import { readdirSync, writeFileSync } from "fs";

const WIKI_TWELF_LOC = "../wiki/src/content/twelf/";
const cfgs = [];
for (const file of readdirSync(WIKI_TWELF_LOC)) {
  if (file.endsWith(".elf")) {
    const cfg = file.slice(0, file.length - 4) + ".cfg";
    writeFileSync(WIKI_TWELF_LOC + cfg, file);
    cfgs.push(`test ${WIKI_TWELF_LOC}${cfg}`);
  }
}

writeFileSync("regression-wiki.txt", cfgs.join("\n"));
