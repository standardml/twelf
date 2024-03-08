import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";
import starlightLinksValidator from "starlight-links-validator";

const KATEX_CSS = {
  rel: "stylesheet",
  href: "https://www.unpkg.com/katex@0.16.9/dist/katex.css",
  integrity:
    "sha384-OH8qNTHoMMVNVcKdKewlipV4SErXqccxxlg6HC9Cwjr5oZu2AdBej1TndeCirael",
  crossorigin: "anonymous",
};

// https://astro.build/config
export default defineConfig({
  integrations: [
    starlight({
      title: "Twelf",
      logo: { src: "./src/assets/mediumelf.png" },
      plugins: [starlightLinksValidator()],
      description: "Home of the Twelf programming language",
      social: {
        github: "https://github.com/standardml/twelf",
      },
      // editLink: { baseUrl: 'TODO' },
      head: [{ tag: "link", attrs: KATEX_CSS }],
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
