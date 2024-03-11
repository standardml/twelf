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

const DIR_OF_WIKI = "twelf/wiki/";
const DIR_OF_ELF = "pages";
const DIR_OF_MDX = "src/content/docs/wiki";
if (!existsSync(DIR_OF_MDX)) {
  mkdirSync("src/content/docs/wiki");
}

function mdxOfFile(file) {
  const elfname = `${DIR_OF_ELF}/${file}`;
  if (!file.endsWith(".elf") || !existsSync(elfname)) return;

  const base = file.slice(0, file.length - 4);
  const mdxname = `${DIR_OF_MDX}/${file.slice(0, file.length - 4)}.mdx`;
  console.log(`elf->mdx transforming ${file}`);
  const elfFile = readFileSync(elfname).toString("utf-8");
  const mdxFile = elfToMdx(DIR_OF_WIKI + elfname, elfFile);
  writeFileSync(mdxname, mdxFile);
}

console.log(`elf->mdx checking existing files...`);
for (const file of readdirSync(DIR_OF_ELF)) {
  mdxOfFile(file);
}
if (argv[2] === "--watch") {
  console.log(`elf->mdx watching ${DIR_OF_ELF} for changes.`);
  watch(DIR_OF_ELF, (_change, file) => {
    mdxOfFile(file);
  });
}
