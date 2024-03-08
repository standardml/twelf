import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";
import starlightLinksValidator from "starlight-links-validator";
import wikiRedirects from "./wiki-redirects.json";

const KATEX_JS = {
  type: "module",
  src: "https://www.unpkg.com/katex@0.16.9/dist/katex.mjs",
  integrity:
    "sha384-7fmyl+/3I3Ui7bqCZncRrFsdDyWE2XV3w1RJEiXtHOiyP78x1Rk6YzcRO1I0Vohl",
  crossorigin: "anonymous",
};
const KATEX_CSS = {
  rel: "stylesheet",
  href: "https://www.unpkg.com/katex@0.16.9/dist/katex.css",
  integrity:
    "sha384-OH8qNTHoMMVNVcKdKewlipV4SErXqccxxlg6HC9Cwjr5oZu2AdBej1TndeCirael",
  crossorigin: "anonymous",
};
const IMPORT_MAP = JSON.stringify({ imports: { katex: KATEX_JS.src } });

// https://astro.build/config
export default defineConfig({
  redirects: wikiRedirects,
  integrations: [
    starlight({
      title: "The Twelf Project",
      logo: { src: "./src/assets/mediumelf.png" },
      plugins: [starlightLinksValidator()],
      description: "Home of the Twelf programming language",
      social: {
        github: "https://github.com/standardml/twelf",
      },
      // editLink: { baseUrl: 'TODO' },
      head: [
        { tag: "script", attrs: { type: "importmap" }, content: IMPORT_MAP },
        { tag: "script", attrs: KATEX_JS },
        { tag: "link", attrs: KATEX_CSS },
        { tag: "script", attrs: { type: "module", src: "/math.mjs" } },
      ],
      sidebar: [
        { label: "Home", link: "/" } /*,
        { label: "The Twelf Project" },
        { label: "Download" },
        {
          label: "Documentation",
          items: [
            { label: "Introductions" },
            { label: "Tutorials" },
            { label: "Case studies" },
            { label: "Glossary" },
          ],
        },
        {
          label: "Reference",
          items: [
            { label: "LF Bibliography" },
            { label: "Research with Twelf" },
          ],
        }, */,
      ],
    }),
  ],
});
