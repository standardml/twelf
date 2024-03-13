import type { ParserResponse, StreamParser } from "./tokenizer-types";

const IDCHARS = /^[_!&$^+/<=>?@~|#*`;,\-\\a-zA-Z0-9'\u{80}-\u{10FFFF}]+/u;

type State =
  | { type: "Toplevel" }
  | { type: "Eolcomment" }
  | { type: "Multilinecomment"; stack: number };

export const twelfTokenizer: StreamParser<State, null> = {
  startState: { type: "Toplevel" },

  handleEof: () => null,

  advance: (stream, state): ParserResponse<State, null> => {
    let tok: string | null;

    if (stream.eol()) {
      // Ignore possible errors
      return { state };
    }

    if (state.type === "Eolcomment") {
      if (stream.eat(/^.+/)) {
        return { state, tag: "comment" };
      }
      return { state };
    }

    if (state.type === "Multilinecomment") {
      if (stream.eat("}")) {
        if (stream.eat("%")) {
          return {
            state:
              state.stack === 1
                ? { type: "Toplevel" }
                : { type: "Multilinecomment", stack: state.stack - 1 },
            tag: "comment",
          };
        }
      }
      if (stream.eat("%")) {
        if (stream.eat("{")) {
          return { state: { ...state, stack: state.stack + 1 } };
        }
      }
      stream.eat(/^[^}%]*/);
      return { state, tag: "comment" };
    }

    if (stream.eat(/^\s+/)) {
      return { state };
    }

    if ((tok = stream.eat(/^[:.()\[\]{}]/))) {
      return {
        state,
        tag: "punctuation",
      };
    }

    if (stream.eat("%")) {
      if (stream.eat(".")) {
        return { state: { type: "Eolcomment" }, tag: "comment" };
      }
      if (stream.eat("{")) {
        return {
          state: { type: "Multilinecomment", stack: 1 },
          tag: "comment",
        };
      }
      if (stream.eat(/^[\s%].*/) || stream.eol()) {
        return { state, tag: "comment" };
      }
      if (stream.eat(IDCHARS)) {
        return { state, tag: "keyword" };
      }
      stream.eat("/^./");
      return { state, tag: "invalid" };
    }

    if (stream.eat('"')) {
      if (stream.eat(/^[^"]+"/)) {
        return { state, tag: "literal" };
      }
      stream.eat(/^.*/);
      return { state, tag: "invalid" };
    }

    if ((tok = stream.eat(IDCHARS))) {
      switch (tok) {
        case "<-":
          return { state, tag: "punctuation" };
        case "->":
          return { state, tag: "punctuation" };
        case "_":
          return { state, tag: "punctuation" };
        case "=":
          return { state, tag: "punctuation" };
        case "type":
          return { state, tag: "keyword" };
        default:
          return {
            state,
            tag: tok.match(/^[A-Z_]/) ? "variableName" : "atom",
          };
      }
    }

    stream.eat(/^./);
    return { state, tag: "invalid" };
  },
};
