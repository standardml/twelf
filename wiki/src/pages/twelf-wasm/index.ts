export const prerender = false;
export const GET = async () => {
  return new Response(
    await fetch(`https://jcreedcmu.github.io/twelf-wasm/`).then((response) =>
      response.blob()
    )
  );
};
