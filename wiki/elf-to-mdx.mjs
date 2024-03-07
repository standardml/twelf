import { existsSync, readFileSync, writeFileSync } from "fs";
import { argv, exit, stderr } from "process";

const inputFile = argv[2];
const outputFile = argv[3];

if (!inputFile || !outputFile) {
  stderr.write(`Usage ${node} ${argv[1]} <input.elf> <output.mdx>\n`);
  exit(1);
}
if (!existsSync(inputFile)) {
  stderr.write(`File ${inputFile} does not exist\n`);
  stderr.write(`Usage ${node} ${argv[1]} <input.elf> <output.mdx>\n`);
  exit(1);
}

/* == Parse out header == */

const header = [];
let lineNum = 0;
const input = readFileSync(inputFile).toString("utf-8").split("\n");
while (lineNum < input.length && input[lineNum].startsWith("%%! ")) {
  header.push(input[0].slice(4) + "\n");
  lineNum += 1;
}

/* == Parse out body == */

let body = [];
let state = { type: "twelf", accum: [] };

// Precondition: state.type === "twelf"
function reduceTwelfAccum() {
  if (
    state.accum.length === 0 ||
    state.accum.every((line) => line.trim() === "")
  ) {
    // Do nothing
  } else {
    body.push(
      "",
      "<Twelf code={`" +
        state.accum.join("\n").replaceAll("\\", "\\\\").replaceAll("`", "\\`") +
        "`}/>",
      ""
    );
  }
  state.accum = [];
}

for (; lineNum < input.length; lineNum++) {
  let line = input[lineNum];
  if (state.type === "twelf") {
    if (line.startsWith("%%#") || line.startsWith("%%!")) {
      reduceTwelfAccum();
      body.push(line.slice(2));
      continue;
    }
    if (line.startsWith("%{!")) {
      reduceTwelfAccum();
      state = { type: "markdown" };
      line = line.slice(3).trimStart();
    } else {
      state.accum.push(line);
      continue;
    }
  }

  // state.type === "markdown"
  if (line.endsWith("!}%")) {
    body.push(line.slice(0, line.length - 3).trimEnd());
    state = { type: "twelf", accum: [] };
  } else {
    body.push(line);
  }
}

/* == Write to file == */

const output = `---
${header.join("")}---

import Latex from "../../../components/Latex.astro";
import Twelf from "../../../components/Twelf.astro";

{/* AUTOMATICALLY GENERATED FROM A .ELF FILE */}
{/* DO NOT EDIT */}
{/* EDIT ${inputFile} INSTEAD */}

${body.join("\n")}
`;
writeFileSync(outputFile, output);
