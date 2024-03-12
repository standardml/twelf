import type { ParserResponse, SourceLocation, StreamParser } from "./tokenizer-types";

const punct = ['.', ':', '(', ')', '[', ']', '{', '}', '<-', '->', '=', '_'] as const;
type PUNCT = (typeof punct)[number];
const IDCHARS = /^[_!&$^+/<=>?@~|#*`;,\-\\a-zA-Z0-9'\u{80}-\u{10FFFF}]+/u;

const directive = [
  'infix',
  'prefix',
  'postfix',
  'name',
  'define',
  'solve',
  'query',
  'fquery',
  'compile',
  'querytabled',
  'mode',
  'unique',
  'covers',
  'total',
  'terminates',
  'block',
  'worlds',
  'reduces',
  'tabled',
  'keepTable',
  'theorem',
  'prove',
  'establish',
  'assert',
  'abbrev',
  'trustme',
  'freeze',
  'thaw',
  'subord',
  'deterministic',
  'clause',
  'sig',
  'struct',
  'where',
  'include',
  'open',
  'use',
];
type DIRECTIVE = (typeof directive)[number];

export type Token =
  | { loc: SourceLocation; type: PUNCT }
  | { loc: SourceLocation; type: 'pathsep' }
  | { loc: SourceLocation; type: 'type' }
  | { loc: SourceLocation; type: 'id'; case: 'Upper' | 'Lower' | 'Bound'; value: string }
  | { loc: SourceLocation; type: 'directive'; value: DIRECTIVE }
  | { loc: SourceLocation; type: 'string'; value: string };

type State =
  | { type: 'Toplevel' }
  | { type: 'Eolcomment' }
  | { type: 'Multilinecomment'; stack: number };

export const twelfTokenizer: StreamParser<State, Token> = {
  startState: { type: 'Toplevel' },

  handleEof: () => null,

  advance: (stream, state): ParserResponse<State, Token> => {
    let tok: string | null;

    if (stream.eol()) {
      // Ignore possible errors
      return { state };
    }

    if (state.type === 'Eolcomment') {
      if (stream.eat(/^.+/)) {
        return { state, tag: 'comment' };
      }
      return { state };
    }

    if (state.type === 'Multilinecomment') {
      if (stream.eat('}')) {
        if (stream.eat('%')) {
          return {
            state:
              state.stack === 1
                ? { type: 'Toplevel' }
                : { type: 'Multilinecomment', stack: state.stack - 1 },
            tag: 'comment',
          };
        }
      }
      stream.eat('/^[^}]*/');
      return { state, tag: 'comment' };
    }

    if (stream.eat(/^\s+/)) {
      return { state };
    }

    if ((tok = stream.eat(/^[:.()\[\]{}]/))) {
      return {
        state,
        tag: 'punctuation',
        tree: { type: tok as PUNCT, loc: stream.matchedLocation() },
      };
    }

    if (stream.eat('%')) {
      if (stream.eat('.')) {
        return { state: { type: 'Eolcomment' }, tag: 'comment' };
      }
      if (stream.eat('{')) {
        return { state: { type: 'Multilinecomment', stack: 1 }, tag: 'comment' };
      }
      if (stream.eat(/^[\s%].*/) || stream.eol()) {
        return { state, tag: 'comment' };
      }
      if (stream.eat(IDCHARS)) {
        return { state, tag: 'meta' };
      }
      stream.eat('/^./');
      return { state, tag: 'invalid' };
    }

    if (stream.eat('"')) {
      if (stream.eat(/^[^"]+"/)) {
        return { state, tag: 'literal' };
      }
      stream.eat(/^.*/);
      return { state, tag: 'invalid' };
    }

    if ((tok = stream.eat(IDCHARS))) {
      switch (tok) {
        case '<-':
          return { state, tag: 'punctuation' };
        case '->':
          return { state, tag: 'punctuation' };
        case '_':
          return { state, tag: 'punctuation' };
        case '=':
          return { state, tag: 'punctuation' };
        case 'type':
          return { state, tag: 'keyword' };
        default:
          return { state, tag: 'variableName' };
      }
    }

    stream.eat(/^./);
    return { state, tag: 'invalid' };
  },
};
