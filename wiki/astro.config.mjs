import { defineConfig } from "astro/config";
import starlight from "@astrojs/starlight";
import starlightLinksValidator from "starlight-links-validator";

// https://astro.build/config
export default defineConfig({
  site: "https://twelf.org",
  redirects: import.meta.env.DEV
    ? {
        "/twelf-wasm/": "https://jcreedcmu.github.io/twelf-wasm/",
      }
    : {},
  trailingSlash: "always",
  integrations: [
    starlight({
      title: "Twelf",
      logo: { src: "./src/assets/mediumelf.png" },
      description: "Home of the Twelf programming language",
      favicon: "/favicon.ico",
      social: {
        github: "https://github.com/standardml/twelf",
      },
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
          ],
        },
      ],
      plugins: [starlightLinksValidator()],
      components: {
        Head: "./src/components/Head.astro",
        Footer: "./src/components/Footer.astro",
      },
      customCss: [
        "./node_modules/katex/dist/katex.css",
        "./src/styles/syntax.css",
        "./src/styles/wiki.css",
      ],
    }),
  ],
});
