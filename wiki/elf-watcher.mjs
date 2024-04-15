import { existsSync, mkdirSync, readdirSync, watch, writeFileSync } from "fs";
import { argv } from "process";
import { elfToMdx } from "./elf-to-mdx.mjs";
import { getImportedPrelude } from "./elf-wiki-imports.mjs";

const DIR_OF_ELF = "pages";
const DIR_OF_MDX = "src/content/docs/wiki";
if (!existsSync(DIR_OF_MDX)) {
  mkdirSync("src/content/docs/wiki");
}

/**
 * Convert and store a Wiki Twelf file as MDX
 * @param {string} file
 */
async function mdxOfFile(file) {
  const elfname = `${DIR_OF_ELF}/${file}`;
  if (!file.endsWith(".elf") || !existsSync(elfname)) return;
  const base = file.slice(0, file.length - 4);
  const mdxname = `${DIR_OF_MDX}/${base}.mdx`;
  try {
    console.log(`elf->mdx transforming ${file}`);
    const prelude = getImportedPrelude(`${DIR_OF_ELF}/`, file);
    const mdxFile = await elfToMdx(
      elfname,
      prelude.map(({ file, contents }) => `%%! file: ${file}\n${contents}\n`)
    );
    writeFileSync(mdxname, mdxFile);
  } catch (e) {
    console.log(e);
    writeFileSync(
      mdxname,
      `
---
---

Error transforming ${file}

${e}
`
    );
  }
}

console.log(`elf->mdx checking existing files...`);
for (const file of readdirSync(DIR_OF_ELF)) {
  await mdxOfFile(file);
}
if (argv[2] === "--watch") {
  console.log(`elf->mdx watching ${DIR_OF_ELF} for changes.`);
  watch(DIR_OF_ELF, async (_change, file) => {
    if (file) await mdxOfFile(file);
  });
}
