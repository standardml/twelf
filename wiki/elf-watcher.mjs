import {
  existsSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  watch,
  writeFileSync,
} from "fs";
import { argv } from "process";
import { elfToMdx } from "./elf-to-mdx.mjs";

const DIR_OF_ELF = "pages";
const DIR_OF_MDX = "src/content/docs/wiki";
if (!existsSync(DIR_OF_MDX)) {
  mkdirSync("src/content/docs/wiki");
}

/**
 * Read the file's header to get all of the imported elf files
 * (in reverse order)
 *
 * @param {string} contents
 */
function getImportedFilenames(contents) {
  /**@type {string[]} */
  const importStatements = [];

  for (const line of contents.split("\n")) {
    if (!line.startsWith("%%! ")) break;
    if (line.startsWith("%%! import: ")) {
      importStatements.push(line.slice(12).trim());
    }
  }

  return importStatements;
}

/**
 * Uses a DFS traversal
 *
 * @param {Set<string>} known
 *   Avoids double-importing by tracking all the filenames ever added to `accum` in the process of this traversal
 * @param {{file: string, contents: string}[]} accum
 *   Accumulates the files, making sure that files are added after their dependencies
 * @param {string} elfname
 *   Name of an ELF file that is a dependency of the file we're trying to load
 */
function dfsAccumImportedPrelude(known, accum, elfname) {
  if (!elfname.match(/^[a-zA-Z.\-_0-9]*[.]elf*$/)) {
    throw new Error(
      `Imported path ${elfname} invalid: must include only letters, numbers, dashes, and underscores and end in .elf`
    );
  }
  const contents = readFileSync(`${DIR_OF_ELF}/${elfname}`).toString("utf-8");
  for (const importElf in getImportedFilenames(contents)) {
    if (!known.has(importElf)) {
      known.add(importElf);
      dfsAccumImportedPrelude(known, accum, importElf);
    }
  }
  accum.push({ file: elfname, contents });
}

/**
 *
 * @param {string} elfname
 */
function getImportedPrelude(elfname) {
  /**@type {Set<string>} */
  const known = new Set();

  /**@type {{file: string, contents: string}[]} */
  const dependencies = [];

  for (const file of getImportedFilenames(
    readFileSync(elfname).toString("utf-8")
  )) {
    known.add(file);
    dfsAccumImportedPrelude(known, dependencies, file);
  }

  return dependencies;
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
    const prelude = getImportedPrelude(elfname);
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
