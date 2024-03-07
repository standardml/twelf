import { exec } from "child_process";
import { existsSync, mkdir, mkdirSync, readdirSync, watch } from "fs";
import { argv } from "process";

const DIR_OF_ELF = "src/content/twelf";
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
  exec(`node elf-to-mdx.mjs ${elfname} ${mdxname}`, (error) => {
    if (error !== null) {
      console.log(`elf->mdx unexpected result ${error}`);
    }
  });
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
