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
      favicon: "/favicon.ico",
      social: {
        github: "https://github.com/standardml/twelf",
      },
      // editLink: { baseUrl: 'TODO' },
      head: [{ tag: "link", attrs: KATEX_CSS }],
      components: { Footer: "./src/components/Footer.astro" },
      customCss: ["./src/styles/syntax.css", "./src/styles/wiki.css"],
      sidebar: [
        { label: "About", link: "/wiki/about-the-twelf-project/" },
        { label: "Download", link: "/download/" },
        {
          label: "Learn Twelf",
          items: [
            { label: "Introductions", link: "/wiki/introductions-to-twelf/" },
            { label: "Tutorials", link: "/wiki/tutorials/" },
            { label: "Language reference", link: "/wiki/users-guide/" },
            { label: "Twelf glossary", link: "/wiki/glossary/" },
            { label: "Style guide", link: "/wiki/twelf-style-guide/" },
          ],
        },
        {
          label: "Case Studies",
          link: "/wiki/case-studies",
        },
        {
          label: "Contributing",
          link: "/contributing/",
        },
        {
          label: "Reference",
          items: [
            { label: "LF bibliography", link: "/bibliography/" },
            {
              label: "Research with Twelf",
              link: "/wiki/research-projects-using-twelf/",
            },
            { label: "External documentation", link: "/wiki/documentation/" },
          ],
        },

        /*,
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
        }, */
      ],
    }),
  ],
});
