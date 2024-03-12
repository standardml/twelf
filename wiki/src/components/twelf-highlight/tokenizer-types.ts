export interface SourcePosition {
  line: number; // >= 1
  column: number; // >= 1
}

export interface SourceLocation {
  start: SourcePosition;
  end: SourcePosition;
}

export interface StringStream {
  /** Matches a string or a regexp (which must start with ^ to only
   * match the start of the string) and advances the current position
   * if found. Returns a non-empty matched string, or null.
   */
  eat(match: string | RegExp): string | null;

  /** Same as eat(), but doesn't advance the current position. */
  peek(match: string | RegExp): string | null;

  /** True if at the start of a line. */
  sol(): boolean;

  /** True if at the end of a line. */
  eol(): boolean;

  /** Returns the SourceLocation covered since the streamstring
   * was initialized (which, in the stream parser, always happens
   * immediately before advance() is called).
   */
  matchedLocation(): SourceLocation;
}

export type Tag = string;

export interface Issue {
  type: "Issue";
  msg: string;
  loc?: SourceLocation;
}

export interface ParserResponse<State, Tree> {
  state: State;
  tag?: Tag;
  tree?: Tree;
  issues?: Issue[];
}

export interface StreamParser<State, Tree> {
  startState: State;

  /** Called to advance the stream state and the parser state. It is
   * okay to return a zero-length token, but only if the state
   * changes (otherwise this is definitely an infinite loop).
   *
   * Will be called exactly once on an empty line. Except in that
   * case, stream.eol() will never be true when this function is
   * initially called: if you advance to the end of the line, the
   * next call will be advance() on the subsequent line, or will be
   * handleEof().
   */
  advance(stream: StringStream, state: State): ParserResponse<State, Tree>;

  /** Once the end of the file is reached, this function is called
   * repeatedly until it returns null in order for any cleanup
   * needed to happen.
   */
  handleEof(state: State): null | ParserResponse<State, Tree>;
}
