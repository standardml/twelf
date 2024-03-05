import katex from "katex";

class InlineKatex extends HTMLElement {
  connectedCallback() {
    console.log(this.nodeName);
    console.log(this);
    this.innerHTML = katex.renderToString(this.innerText, {
      throwOnError: false,
    });
  }
}

customElements.define("inline-math", InlineKatex);
