/*

This file parses  ./src/content/twelf/*.elf files in the directory into the
./src/content/docs/wiki/*.mdx files that are actually understood by the Astro
Starlight extension. The goal is for this to be a fairly minimal state machine
that someone could code up again in an hour or so to retarget the wiki's .elf
files to a new markdown-ish target in the future.

### High level structure of a Twelf wiki file

Here's a simple Twelf wiki file:

    %%! title: A simple Twelf wiki file

    %{! Here's code that defines the natural numbers: either zero `z`
    or `s N`, the successor of the natural number `z`. !}%
    
    nat : type.

    %%## Level two heading

    %{! !}%

A wiki Twelf file begins with a series of lines beginning with `%%!` that
directly become the frontmatter of the output file.

Then, the rest of the parser turns the file "inside out", making special
comments --- beginning with %{! at the beginning of a line and ending with
!}% at the end of a line --- into Markdown text, and turning everything else
into Twelf.

### Recognized behavior within Markdown sections

Within Markdown sections, centered math is recognized as

    ```math
    \bigvee_i \mathcal{C}_i
    ```

It's possible to display syntax-highlighted Twelf code that doesn't appear
in the regular flow of the document:

    ```twelf
    % Don't do this:
    loop : type.
    fix : loop <- loop.
    %solve x : loop.
    ```

It's also possible to display checked Twelf code that 

*/




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

/* Parse out header

A 

*/

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
  while (state.accum.length > 0 && state.accum[0].trim() === "") {
    state.accum.shift();
  }
  while (
    state.accum.length > 0 &&
    state.accum[state.accum.length - 1].trim() === ""
  ) {
    state.accum.pop();
  }
  if (state.accum.length === 0) {
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
