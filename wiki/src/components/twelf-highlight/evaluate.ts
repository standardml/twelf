import { exec } from "child_process";

export const response = new Promise((resolve) => {
  exec("rustc", (_, stdout) => resolve(stdout));
});
