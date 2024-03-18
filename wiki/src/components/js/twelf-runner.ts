import { tmpdir } from "os";
import { join } from "path";
import { writeFile } from "fs/promises";
import { exec } from "child_process";

export async function twelfExec(prelude: string, code: string) {
  const preludeFN = join(tmpdir(), `twelf-${crypto.randomUUID()}.elf`);
  const codeFN = join(tmpdir(), `twelf-${crypto.randomUUID()}.elf`);
  await writeFile(preludeFN, prelude);
  await writeFile(codeFN, code);
  return await new Promise((resolve) =>
    exec(
      `echo "set chatter 0\\nloadFile ${preludeFN}\\nset chatter 3\\nloadFile ${codeFN}" | ../bin/twelf-server`,
      { timeout: 2500 },
      (err, stdout) => {
        if (err) {
          resolve(`Error during Twelf execution:\n${err}\n${stdout}`);
        } else {
          const lines = stdout.split("\n");
          if (
            lines.length <= 5 ||
            !lines[0]?.startsWith("Twelf") ||
            lines[1] !== "%% OK %%" ||
            lines[2] !== "%% OK %%" ||
            lines[3] !== "%% OK %%" ||
            lines[4] !== "%% OK %%" ||
            !lines[5]?.startsWith("[Opening file")
          ) {
            resolve(`Unexpected output from Twelf:\n${lines.join("\n")}`);
          }
          resolve(
            lines
              .slice(6)
              .filter(
                (line) =>
                  !line.startsWith("[Closing file") &&
                  line.trim() !== "" &&
                  !line.startsWith(preludeFN)
              )
              .map((line) =>
                line.startsWith(codeFN)
                  ? "input.elf" + line.slice(codeFN.length)
                  : line
              )
              .join("\n")
          );
        }
      }
    )
  );
}
