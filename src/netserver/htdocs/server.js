// a small chunk of my standard js utilities
function ce(type) { return document.createElement(type) }
function ctn(text) { return document.createTextNode(text) }
Array.prototype.last = function() {return this[this.length - 1]}
Node.prototype.ac = function(c) { return this.appendChild(c) }
Node.prototype.rc = function(c) { return this.removeChild(c) }
Node.prototype.ace = function(type) { return this.appendChild(document.createElement(type))  }
Node.prototype.actn = function(text) { return this.appendChild(document.createTextNode(text)); }
Node.prototype.removeChildren = function () {
  while (this.childNodes.length > 0) {
    this.removeChild(this.firstChild);
  }
}
Node.prototype.setText = function (x) {
  this.removeChildren();
  this.actn(x);	
}

function shower (tip, txt, tt) {
  return function (e) { tip.className = "tip"; tip.setText(txt + ":" + tt);
  tip.style.left = e.pageX + 25;
  tip.style.top = e.pageY - 12;
  }
}

Node.prototype.setRichText = function (x) {
  this.removeChildren();
  var r = /\{([^:]*):([^\}]*)\}/g;
  types = {};
  var info;
  while (info = r.exec(x)) {
    types[info[1]] = info[2];
  }
  var buf = x;
  var t;
  for (t in types) {
    buf = buf.replace(new RegExp(t, "g"), "%;%span: " + t + "%;");
  }

  var a = buf.split(/%;/);
  for (var i = 0; i < a.length; i++) {
    var r = /%span: /;
    if (a[i].match(r)) {
      var s = this.ace("span");
      var txt = a[i].replace(r, "");
      var tt = types[txt];
      s.className = "bvar";
      var tip = gebid("tip");
      s.onmouseover = shower(tip, txt, tt);
      s.onmouseout = function () { tip.className = "invisible"; };
      s.actn(txt);
    }
    else {
      this.actn(a[i]);
    }
  }


}

function gebid(id) { return document.getElementById(id); }

function twelfCmd(cmd, args) {
  var r = new XMLHttpRequest();

  r.open("POST", "/", true);

  r.onreadystatechange=function() {
    if (r.readyState==4) {
      //     gebid("output").setRichText(r.responseText);
     gebid("output").setText(r.responseText);
    }
  };

  r.send(cmd + " " + args);
}

function btnReadDecl() {
 twelfCmd("readDecl", gebid("input").value);
}

function btnDecl() {
 twelfCmd("decl", gebid("input").value);
}

function btnExample() {
 twelfCmd("example", gebid("exampleSelect").value);
}

function btnChatter() {
 twelfCmd("set chatter", gebid("chatterSelect").value);
}

function btnQuit() {
  twelfCmd("quit", "");
}

