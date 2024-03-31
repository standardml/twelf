export function getStaticPaths() {
  /*
   * On render.com, all these rewrites are handled by a generic Apache-style
   * URL rewriting scheme that proxies /twelf-wasm/whatever to
   * <https://jcreedcmu.github.io/twelf-wasm/whatever>. This list only has
   * to be right in order for the local development server to work correctly.
   * That means it's likely to fix if Jason changes something about
   * twelf-wasm, but only for local development, and it should be easy to fix
   * (just figure out which files aren't being found and add them to the
   * static paths).
   */
  return [
    { params: { path: "assets/bundle.js" } },
    { params: { path: "assets/twelf.wasm" } },
    { params: { path: "assets/twelf-icon.png" } },
    { params: { path: "assets/worker.js" } },
    { params: { path: "css/style.css" } },
    { params: { path: "index.html" } },
  ];
}

import type { APIRoute } from "astro";

export const prerender = false;
export const GET: APIRoute = async ({ url }) => {
  return new Response(
    await fetch(`https://jcreedcmu.github.io${url.pathname}`).then((response) =>
      response.blob()
    )
  );
};
