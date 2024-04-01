import { mkdirSync, writeFileSync, existsSync, readFileSync } from "fs";
import { join } from "path";

/*
See wiki/src/content/docs/wiki-syntax.mdx for an explanation of
the Wiki Twelf format that this file is parsing
*/

const DIR_OF_ELF_CACHE = "tmp/contexts";
const DIR_PUBLIC_PATH = "public";
const PUBLIC_PATH_OF_HAT_CODE = "hat-code";
if (!existsSync(DIR_OF_ELF_CACHE)) {
  mkdirSync(DIR_OF_ELF_CACHE, { recursive: true });
}
if (!existsSync(join(DIR_PUBLIC_PATH, PUBLIC_PATH_OF_HAT_CODE))) {
  mkdirSync(join(DIR_PUBLIC_PATH, PUBLIC_PATH_OF_HAT_CODE), {
    recursive: true,
  });
}

/**
 * Escape a string to live within a format string in JS.
 *
 * @param {string} twelfcode
 * @returns string
 */
function escapeBacktickEnv(twelfcode) {
  return twelfcode
    .replaceAll("\\", "\\\\")
    .replaceAll("`", "\\`")
    .replaceAll("$", "\\$");
}

/**
 * Remove all the leading or trailing lines containing only whitespace
 *
 * @param {string[]} lines
 */
function mutablyTrimEmptyLines(lines) {
  while (lines[0]?.trim() === "") {
    lines.shift();
  }
  while (lines[lines.length - 1]?.trim() === "") {
    lines.pop();
  }
}

/**
 * Hash a string and return a short digest as a sequence of hex digits
 *
 * @param {string} content
 * @returns {Promise<string>}
 */
async function hashToHex(content) {
  const digest = await crypto.subtle.digest(
    "SHA-256",
    new TextEncoder().encode(content)
  );
  return Array.from(new Uint8Array(digest))
    .map((n) => n.toString(16).padStart(2, "0"))
    .join("")
    .slice(0, 10);
}

/**
 * Process in a Wiki Twelf file and generate an Astro-ready MDX file.
 *
 * @param {string} elfFilename
 *   The Elf file to process
 * @returns {Promise<string>}
 */
export async function elfToMdx(elfFilename) {
  const elfFile = readFileSync(elfFilename, "utf-8");

  /* Parse out header */
  /** @type {string[]} */
  const header = [];
  let lineNum = 0;
  const input = elfFile.split("\n");
  while (lineNum < input.length && input[lineNum]?.startsWith("%%! ")) {
    header.push(input[lineNum]?.slice(4) + "\n");
    lineNum += 1;
  }

  /* Parse out body */

  /** @type {string[]} */
  let body = [];
  /** @type {string[]} */
  let twelfcontext = [];

  /** @typedef {{ type: "twelf", subtype: null | "hidden" | "checked", accum: string[] }} TwelfState */
  /** @typedef {{ type: "markdown-block", subtype: "math" | "twelf" | "checkedtwelf", accum: string[] }} MarkdownBlockState */
  /** @typedef {{ type: "markdown" }} MarkdownState */
  /** @type {TwelfState | MarkdownState | MarkdownBlockState} */
  let state = { type: "twelf", subtype: null, accum: [] };

  // Precondition: state.type === "twelf"
  async function reduceTwelfAccum(checked = false, save = false) {
    if (
      !(
        state.type === "twelf" ||
        (state.type === "markdown-block" &&
          (state.subtype === "twelf" || state.subtype === "checkedtwelf"))
      )
    ) {
      throw new TypeError(`state ${state.type} - ${state.type !== 'markdown' ? state.subtype : 'none'}`);
    }
    mutablyTrimEmptyLines(state.accum);

    if (state.accum.length === 0) {
      body.push("");
    } else {
      /* The `context` is the additional Twelf needed to check (without output)
       * in order to display Twelf's response to the code in this Twelf component
       */
      const context = twelfcontext.join("\n");

      /* The `hatJson` is the object that the Twelf Wasm editor should load (when
       * the hat icon is clicked on) in order to allow the code to be manipulated.
       */
      /** @type {import("twelf-wasm").UrlAction} */
      const hatSetText = {
        t: "setTextAndExec",
        text: (
          context.trim() +
          "\n\n\n\n" +
          state.accum.join("\n").trim()
        ).trim(),
      };
      const hatJson = JSON.stringify(hatSetText);

      /* Because both context and hatJson can get very big in files with many
       * segments of Twelf code, we store them in files and put the URL in the
       * Twelf tag.
       *
       * The directory of the Elf cache will be accessed by the Twelf component
       * itself for server-side rendering, but the hat JSON needs to be served
       * to users.
       */
      const contextFile = join(
        DIR_OF_ELF_CACHE,
        `${await hashToHex(context)}.elf`
      );
      writeFileSync(contextFile, context);
      const hatJsonFile = join(
        PUBLIC_PATH_OF_HAT_CODE,
        `${await hashToHex(hatJson)}.json`
      );
      writeFileSync(join(DIR_PUBLIC_PATH, hatJsonFile), hatJson);
      /** @type {import("twelf-wasm").FragmentAction} */
      const getUrl = { t: "getUrl", url: "/" + hatJsonFile };

      body.push(
        "",
        "<Twelf" +
          (checked ? " checked\n" : "\n") +
          `  contextFile="${contextFile}"\n` +
          `  hatAction='${JSON.stringify(getUrl)}'\n` +
          "  code={`" +
          escapeBacktickEnv(state.accum.join("\n")) +
          "`}/>",
        ""
      );
    }
    if (save) twelfcontext.push(...state.accum);
    state.accum = [];
  }

  for (; lineNum < input.length; lineNum++) {
    let line = input[lineNum] ?? "";
    if (state.type === "twelf") {
      /* Handle recognized special behavior within Twelf sections */
      if (line.trim() === "%{!! begin hidden !!}%") {
        await reduceTwelfAccum(false, true);
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
          body.push(
            "# Error line " + lineNum + ", found unmatched `end hidden`"
          );
        }
        state = { ...state, subtype: null };
        continue;
      }
      if (line.trim() === "%{!! begin checked !!}%") {
        await reduceTwelfAccum(false, true);
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
        await reduceTwelfAccum(true, true);
        if (state.subtype !== "checked") {
          body.push(
            "# Error line " + lineNum + ", found unmatched `end checked`"
          );
        }
        state = { ...state, subtype: null };
        continue;
      }

      /* Check for the end of a Twelf section */
      if (line.startsWith("%{!")) {
        await reduceTwelfAccum(false, true);
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
        if (state.subtype !== "hidden") state.accum.push(line);
        else twelfcontext.push(line);
        continue;
      }
    }

    if (state.type === "markdown-block") {
      if (line.trimEnd() === "```") {
        if (state.subtype === "twelf") {
          await reduceTwelfAccum();
        } else if (state.subtype === "checkedtwelf") {
          await reduceTwelfAccum(true);
        } else {
          mutablyTrimEmptyLines(state.accum);
          body.push(
            "",
            "<DisplayMath " +
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
    await reduceTwelfAccum();
  } else {
    body.push("# Error: unclosed wiki-comment at end of file");
  }

  /* == Write to file == */

  const output = `---
${header.join("")}---

import DisplayMath from "../../../components/DisplayMath.astro";
import Math from "../../../components/Math.astro";
import Twelf from "../../../components/Twelf.astro";
import Guide from "../../../components/Guide.astro";
import Keyword from "../../../components/Keyword.astro";
import Todo from "../../../components/Todo.astro";

{/* AUTOMATICALLY GENERATED FROM A .ELF FILE */}
{/* DO NOT EDIT */}
{/* EDIT twelf/wiki/${elfFilename} INSTEAD */}

${body.join("\n")}
`;
  return output;
}
