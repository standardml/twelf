---
title: Syntax for Wiki Twelf pages
---

This website runs off of the [Astro Starlight](https://starlight.astro.build/)
static site generator, which builds the website from markdown files (`.md`)
and [extended markdown](https://mdxjs.com/) files (`.mdx`).

All the files under the `/wiki/` prefix on this website are written as
Wiki Twelf files, which are also valid Twelf files with the `.elf` extension,
in the `/wiki/src/content/twelf/` directory of the Twelf repository. When
building the website, the converter script `/wiki/elf-to-mdx.mjs` takes these
Wiki Twelf files and creates files in the `/wiki/src/content/docs/wiki/*.mdx`
directory that are actually what the static site generator sees.

The goal is for the converter to be a fairly minimal state machine that
someone could code up again in an hour or so to retarget the wiki's `.elf`
files to some other markdown-ish target in the future.

## High level structure of a Twelf wiki file

Here's a simple Twelf wiki file:

    %%! title: A simple Twelf wiki file

    %{! Here's code that defines the natural numbers: either zero `z`
    or `s N`, the successor of the natural number `z`. !}%

    nat : type.
    z : nat.
    s : nat -> nat.

    %{! ## Level two heading !}%

    %{! The [`%freeze`](/wiki/percent-freeze) declaration freezes. !}%
    %freeze nat.

This will get turned by the `/wiki/elf-to-mdx.mjs` script into the following
extended markdown file that the Astro Starlight SSG understands.

    ---
    title: A simple Twelf wiki file
    ---
    import Twelf from "../../../components/Twelf.astro";

    Here's code that defines the natural numbers: either zero `z`
    or `s N`, the successor of the natural number `z`.

    <Twelf code={`nat : type.
    z : nat.
    s : nat -> nat.`}/>

    ## Level two heading
    The [`%freeze`](/wiki/percent-freeze) declaration freezes.

A wiki Twelf file begins with a series of lines beginning with `%%!` that
directly become the frontmatter of the output file.

Then, the rest of the parser turns the file "inside out", making special
comments --- beginning with `%{!` at the beginning of a line and ending with
`!}%` at the end of a line, possibly the same line --- into Markdown text, and
turning everything else into Twelf.

An empty section of Twelf between two markup sections will be ignored. An
empty section of Markdown between two Twelf sections will cause a break
in the Twelf.

## Recognized behavior within Twelf sections

Within a Twelf section, code within `%{!! begin checked !!}%` and
`%{!! end checked !!}%` lines will be displayed on the wiki along with
the Twelf output of running that code in context.

    %{!! begin checked !!}%
    three : nat : s (s (s z)).
    %{!! end checked !!}%

This code will be checked in the context of the Twelf code in the page up to
that point.

Within a Twelf section, code within `%{!! begin hidden !!}%` and
`%{!! end hidden !!}%` lines will be omitted from the wiki, while remaining
part of the overall Twelf document.

    %{!! begin hidden !!}%
    % These declarations are necessary but would interrupt
    % the flow of the page if we showed them in the wiki text:
    nat : type.
    times : nat -> nat -> nat.
    %{!! end hidden !!}%

## Recognized behavior within Markdown sections

Within Markdown sections, centered math in non indented ` ```math `
blocks is recognized:

    ```math
    \bigvee_i \mathcal{C}_i
    ```

It's possible to display syntax-highlighted Twelf code that doesn't appear
in the regular flow of the document:

    ```twelf
    % Don't do this, it will run forever:
    loop : type.
    fix : loop <- loop.
    %solve x : loop.
    ```

It's also possible to display checked Twelf code that shows its response:

    ```checkedtwelf
    % This won't work at all.
    nat : type.
    %trustme nat -> nat = nat -> nat.
    ```

These commands are important because they allow the wiki page itself to work
as a complete Twelf file that loads correctly in Twelf, while still being
able to contain, in what are effectively Twelf comments, non-running
code examples.