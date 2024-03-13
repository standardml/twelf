import type { StreamParser, StringStream } from "./tokenizer-types";

export function spanHighlight<State, Token>(
  tokenizer: StreamParser<State, Token>,
  string: string
): { tag: string | null; contents: string }[][] {
  let outputLines: { tag: string | null; contents: string }[][] = [];
  let output: { tag: string | null; contents: string }[] = [];
  let workingTag: string | undefined = undefined;
  let workingContents: string = "";
  function reduce(newTag: string | undefined, newContents: string) {
    if (newContents === "") {
      // Do nothing
    } else if (newTag === workingTag) {
      workingContents += newContents;
    } else {
      if (workingContents !== "") {
        output.push({ tag: workingTag ?? null, contents: workingContents });
      }
      workingTag = newTag;
      workingContents = newContents;
    }
  }

  let state: State = tokenizer.startState;
  for (let [lineOffByOne, remainingLine] of string.split("\n").entries()) {
    const line = lineOffByOne + 1;
    let column = 1;

    let currentStartColumn: number;
    let currentMatch: string;
    let stream: StringStream = {
      eat: (match: string | RegExp) => {
        const peek = stream.peek(match);
        if (peek === null) return null;
        column += peek.length;
        currentMatch += peek;
        remainingLine = remainingLine.slice(peek.length);
        return peek;
      },
      peek: (match: string | RegExp): string | null => {
        if (typeof match === "string") {
          return remainingLine.startsWith(match) ? match : null;
        }
        const success = remainingLine.match(match);
        return success === null ? null : success[0];
      },
      sol: () => {
        return column === 1;
      },
      eol: () => {
        return remainingLine === "";
      },
      matchedLocation: () => ({
        start: { line, column: currentStartColumn },
        end: { line, column },
      }),
    };

    let i = 0;
    do {
      currentMatch = "";
      currentStartColumn = column;
      const response = tokenizer.advance(stream, state);
      reduce(response.tag, currentMatch);
      state = response.state;
      column = currentStartColumn;
      if (i++ > 10000) {
        throw new Error(`loop parsing line ${line}: '${remainingLine}'`);
      }
    } while (remainingLine !== "");

    if (workingContents !== "") {
      output.push({ tag: workingTag ?? null, contents: workingContents });
      workingContents = "";
    }
    outputLines.push(output);
    output = [];
  }

  return outputLines;
}
