/*
See wiki/src/content/docs/wiki-syntax.md for an explanation of
the Wiki Twelf format that this file is parsing
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

/* Parse out header */

const header = [];
let lineNum = 0;
const input = readFileSync(inputFile).toString("utf-8").split("\n");
while (lineNum < input.length && input[lineNum].startsWith("%%! ")) {
  header.push(input[0].slice(4) + "\n");
  lineNum += 1;
}

/* Parse out body */

let body = [];
let twelfcontext = [];

/*
type State
  = { type: "twelf", subtype: null | "hidden" | "checked", accum: string list }
  | { type: "markdown-block", subtype: "math" | "twelf" | "checkedtwelf", accum: string list }
  | { type: "markdown" }
*/
let state = { type: "twelf", subtype: null, accum: [] };

function escapeBacktickEnv(twelfcode) {
  return twelfcode.replaceAll("\\", "\\\\").replaceAll("`", "\\`");
}

function mutablyTrimEmptyLines(lines) {
  while (lines.length > 0 && lines[0].trim() === "") {
    lines.shift();
  }
  while (lines.length > 0 && lines[lines.length - 1].trim() === "") {
    lines.pop();
  }
}

// Precondition: state.type === "twelf"
function reduceTwelfAccum(checked = false) {
  mutablyTrimEmptyLines(state.accum);
  if (state.accum.length === 0) {
    body.push("");
  } else {
    body.push(
      "",
      "<Twelf " +
        (checked
          ? "checked context={`" +
            escapeBacktickEnv(twelfcontext.join("\n")) +
            "`} "
          : "") +
        "code={`" +
        escapeBacktickEnv(state.accum.join("\n")) +
        "`}/>",
      ""
    );
  }
  state.accum = [];
}

for (; lineNum < input.length; lineNum++) {
  let line = input[lineNum];
  if (state.type === "twelf") {
    /* Handle recognized special behavior within Twelf sections */
    if (line.trim() === "%{!! begin hidden !!}%") {
      reduceTwelfAccum();
      if (state.subtype !== null) {
        body.push(
          "# Error line " +
            lineNum +
            ", found `begin hidden` within " +
            state.subtype
        );
      }
      state = { ...state, subtype: "hidden" };
      continue;
    }
    if (line.trim() === "%{!! end hidden !!}%") {
      if (state.subtype !== "hidden") {
        body.push("# Error line " + lineNum + ", found unmatched `end hidden`");
      }
      state = { ...state, subtype: null };
      continue;
    }
    if (line.trim() === "%{!! begin checked !!}%") {
      reduceTwelfAccum();
      if (state.subtype !== null) {
        body.push(
          "# Error line " +
            lineNum +
            ", found `begin checked` within " +
            state.subtype
        );
      }
      state = { ...state, subtype: "checked" };
      continue;
    }
    if (line.trim() === "%{!! end checked !!}%") {
      reduceTwelfAccum(true);
      if (state.subtype !== "checked") {
        body.push(
          "# Error line " + lineNum + ", found unmatched `end checked`"
        );
      }
    }

    /* Check for the end of a Twelf section */
    if (line.startsWith("%{!")) {
      reduceTwelfAccum();
      if (state.subtype !== null) {
        body.push(
          "# Error line " +
            lineNum +
            ", expected end for previous `begin " +
            state.subtype +
            "`"
        );
      }
      state = { type: "markdown" };
      line = line.slice(3).trimStart();
      // FALLTHROUGH TO MARKDOWN PROCESSING SECTION
    } else {
      twelfcontext.push(line);
      state.accum.push(line);
      continue;
    }
  }

  if (state.type === "markdown-block") {
    if (line.trimEnd() === "```") {
      if (state.subtype === "twelf") {
        reduceTwelfAccum();
      } else if (state.subtype === "checkedtwelf") {
        reduceTwelfAccum(true);
      } else {
        mutablyTrimEmptyLines(state.accum);
        body.push(
          "",
          "<KatexBlock " +
            "formula={`" +
            escapeBacktickEnv(state.accum.join("\n")) +
            "`}/>",
          ""
        );
      }
      state = { type: "markdown" };
      continue;
    } else {
      state.accum.push(line);
      continue;
    }
  }

  // state.type === "markdown"
  if (line.endsWith("!}%")) {
    body.push(line.slice(0, line.length - 3).trimEnd());
    state = { type: "twelf", subtype: null, accum: [] };
  } else if (line.trimEnd() === "```math") {
    state = { type: "markdown-block", subtype: "math", accum: [] };
  } else if (line.trimEnd() === "```twelf") {
    state = { type: "markdown-block", subtype: "twelf", accum: [] };
  } else if (line.trimEnd() === "```checkedtwelf") {
    state = { type: "markdown-block", subtype: "checkedtwelf", accum: [] };
  } else {
    body.push(line);
  }
}

if (state.type === "twelf") {
  reduceTwelfAccum();
} else {
  body.push("# Error: unclosed wiki-comment at end of file");
}

/* == Write to file == */

const output = `---
${header.join("")}---

import KatexBlock from "../../../components/Latex.astro";
import Twelf from "../../../components/Twelf.astro";
import Guide from "../../../components/Guide.astro";
import Keyword from "../../../components/Keyword.astro";

{/* AUTOMATICALLY GENERATED FROM A .ELF FILE */}
{/* DO NOT EDIT */}
{/* EDIT ${inputFile} INSTEAD */}

${body.join("\n")}
`;
writeFileSync(outputFile, output);
