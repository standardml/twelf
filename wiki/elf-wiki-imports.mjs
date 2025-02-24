import { readFileSync } from "fs";

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
 * @param {string} base
 *   Relative path of elf files
 * @param {Set<string>} known
 *   Avoids double-importing by tracking all the filenames ever added to `accum` in the process of this traversal
 * @param {{file: string, contents: string}[]} accum
 *   Accumulates the files, making sure that files are added after their dependencies
 * @param {string} elfname
 *   Name of an ELF file that is a dependency of the file we're trying to load
 */
function dfsAccumImportedPrelude(base, known, accum, elfname) {
  if (!elfname.match(/^[a-zA-Z.\-_0-9]*[.]elf*$/)) {
    throw new Error(
      `Imported path ${elfname} invalid: must include only letters, numbers, dashes, and underscores and end in .elf`
    );
  }
  const contents = readFileSync(`${base}${elfname}`).toString("utf-8");
  for (const importElf in getImportedFilenames(contents)) {
    if (!known.has(importElf)) {
      known.add(importElf);
      dfsAccumImportedPrelude(base, known, accum, importElf);
    }
  }
  accum.push({ file: elfname, contents });
}

/**
 *
 * @param {string} base
 *   Relative path of elf files
 * @param {string} elfname
 */
export function getImportedPrelude(base, elfname) {
  /**@type {Set<string>} */
  const known = new Set();

  /**@type {{file: string, contents: string}[]} */
  const dependencies = [];

  for (const file of getImportedFilenames(
    readFileSync(`${base}${elfname}`).toString("utf-8")
  )) {
    known.add(file);
    dfsAccumImportedPrelude(base, known, dependencies, file);
  }

  return dependencies;
}
