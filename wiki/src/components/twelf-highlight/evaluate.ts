import { exec } from "child_process";

export const response = new Promise((resolve) => {
  exec("rustc", (error, stdout) => resolve(stdout));
});
