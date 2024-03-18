/* This code taken from the encoder/decoder pair in Jason Reed's Twelf
WASM prototype; only the encoding half of the pair is needed here.

https://github.com/jcreedcmu/twelf-wasm/blob/eef7b12b9/src/encoding.ts
*/

function bytesOfString(str: string): Uint8Array {
  return new TextEncoder().encode(str);
}

function concatenateUint8Arrays(arrays: Uint8Array[]) {
  if (arrays.length == 0) return new Uint8Array([]);
  const totalLength = arrays.map((arr) => arr.length).reduce((a, b) => a + b);
  const result = new Uint8Array(totalLength);
  let offset = 0;
  for (const arr of arrays) {
    result.set(arr, offset);
    offset += arr.length;
  }
  return result;
}

async function bytesOfStream(
  readableStream: ReadableStream
): Promise<Uint8Array> {
  const reader = readableStream.getReader();
  let result: Uint8Array[] = [];
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    result.push(value);
  }
  return concatenateUint8Arrays(result);
}

export async function getTwelfLiveLink(context: string, code: string) {
  const uncompressedBytes = bytesOfString(
    `${context.trim()}\n\n\n\n${code.trim()}`.trim()
  );
  const compressedBytes = await bytesOfStream(
    new Blob([uncompressedBytes])
      .stream()
      .pipeThrough(new CompressionStream("gzip"))
  );
  return (
    "https://jcreedcmu.github.io/twelf-wasm/#v2/" +
    encodeURIComponent(btoa(String.fromCodePoint(...compressedBytes)))
  );
}
