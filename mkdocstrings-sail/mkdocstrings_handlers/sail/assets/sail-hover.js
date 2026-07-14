/* IDE-style hover cards for mkdocstrings-sail.
 * Links rendered with data-sail-hover="<anchor>" reveal the matching
 * <template class="sail-hovercard" data-anchor="<anchor>"> as a fixed-
 * position card, viewport-aware, dismissed on mouse-out or scroll. */
(function () {
  "use strict";
  var card = null;

  function hide() {
    if (card) {
      card.remove();
      card = null;
    }
  }

  document.addEventListener("mouseover", function (event) {
    if (card && card.contains(event.target)) return; // allow hovering the card
    var target = event.target.closest("[data-sail-hover]");
    if (!target) {
      hide();
      return;
    }
    var key = target.getAttribute("data-sail-hover");
    if (card && card.dataset.for === key) return;
    hide();
    var template = document.querySelector(
      'template.sail-hovercard[data-anchor="' + (window.CSS ? CSS.escape(key) : key) + '"]'
    );
    if (!template) return;
    card = document.createElement("div");
    card.className = "sail-hovercard-float";
    card.dataset.for = key;
    card.appendChild(template.content.cloneNode(true));
    document.body.appendChild(card);
    var rect = target.getBoundingClientRect();
    var top = rect.bottom + 6;
    if (top + card.offsetHeight > window.innerHeight - 8) {
      top = Math.max(8, rect.top - card.offsetHeight - 6);
    }
    var left = Math.min(rect.left, window.innerWidth - card.offsetWidth - 12);
    card.style.top = top + "px";
    card.style.left = Math.max(8, left) + "px";
    if (key.indexOf("eip-") === 0) liveEip(key.slice(4), card);
  });

  /* Live EIP content: fetch the EIP's current Markdown from ethereum/EIPs
   * master at hover time and render it in full (scrollable), so upstream
   * edits appear without rebuilding the spec. The baked summary card is
   * the instant/offline fallback. All text is inserted as text nodes; only
   * http(s) links are emitted. */
  var eipCache = {};

  function inline(text, parent) {
    // minimal inline rendering: `code` spans and [text](url) links
    var parts = text.split(/(`[^`]*`)/);
    for (var i = 0; i < parts.length; i++) {
      if (i % 2) {
        var code = document.createElement("code");
        code.textContent = parts[i].slice(1, -1);
        parent.appendChild(code);
        continue;
      }
      var rest = parts[i].replace(/!\[[^\]]*\]\([^)]*\)/g, "");
      var re = /\[([^\]]+)\]\(([^)\s]+)\)/g;
      var last = 0, m;
      while ((m = re.exec(rest))) {
        parent.appendChild(document.createTextNode(rest.slice(last, m.index)));
        if (/^https?:\/\//.test(m[2])) {
          var a = document.createElement("a");
          a.href = m[2];
          a.target = "_blank";
          a.rel = "noopener";
          a.textContent = m[1];
          parent.appendChild(a);
        } else {
          parent.appendChild(document.createTextNode(m[1]));
        }
        last = m.index + m[0].length;
      }
      parent.appendChild(document.createTextNode(rest.slice(last)));
    }
  }

  function renderMarkdown(md, container) {
    var lines = md.split("\n");
    var i = 0, para = [];
    function flush() {
      if (!para.length) return;
      var pEl = document.createElement("p");
      inline(para.join(" "), pEl);
      container.appendChild(pEl);
      para = [];
    }
    while (i < lines.length) {
      var line = lines[i];
      var fence = line.match(/^```/);
      if (fence) {
        flush();
        var buf = [];
        i++;
        while (i < lines.length && !/^```/.test(lines[i])) buf.push(lines[i++]);
        i++;
        var pre = document.createElement("pre");
        var code = document.createElement("code");
        code.textContent = buf.join("\n");
        pre.appendChild(code);
        container.appendChild(pre);
        continue;
      }
      var h = line.match(/^(#{1,6})\s+(.*)$/);
      if (h) {
        flush();
        var hEl = document.createElement("h" + Math.min(6, h[1].length + 2));
        inline(h[2], hEl);
        container.appendChild(hEl);
        i++;
        continue;
      }
      var li = line.match(/^\s*(?:[-*+]|\d+\.)\s+(.*)$/);
      if (li) {
        flush();
        var ul = container.lastChild && container.lastChild.tagName === "UL"
          ? container.lastChild : container.appendChild(document.createElement("ul"));
        var liEl = document.createElement("li");
        inline(li[1], liEl);
        ul.appendChild(liEl);
        i++;
        continue;
      }
      if (!line.trim()) {
        flush();
        i++;
        continue;
      }
      para.push(line.trim());
      i++;
    }
    flush();
  }

  function liveEip(n, target) {
    function render(eip) {
      if (!card || card !== target || card.dataset.for !== "eip-" + n) return;
      card.classList.add("sail-hovercard-eip");
      var doc = card.querySelector(".sail-hovercard-doc") || card;
      doc.textContent = "";
      var head = document.createElement("strong");
      head.textContent = "EIP-" + n + ": " + eip.title;
      var status = document.createElement("small");
      status.textContent = eip.status ? " (" + eip.status + ", live)" : " (live)";
      doc.appendChild(head);
      doc.appendChild(status);
      renderMarkdown(eip.body, doc);
    }
    if (eipCache[n]) {
      if (eipCache[n] !== "pending" && eipCache[n] !== "failed") render(eipCache[n]);
      return;
    }
    eipCache[n] = "pending";
    fetch("https://raw.githubusercontent.com/ethereum/EIPs/master/EIPS/eip-" + n + ".md")
      .then(function (r) { if (!r.ok) throw new Error(r.status); return r.text(); })
      .then(function (text) {
        var meta = {};
        if (text.indexOf("---") === 0) {
          var end = text.indexOf("\n---", 3);
          text.slice(3, end).split("\n").forEach(function (line) {
            var j = line.indexOf(":");
            if (j > 0) meta[line.slice(0, j).trim()] = line.slice(j + 1).trim();
          });
          text = text.slice(end + 4);
        }
        eipCache[n] = { title: meta.title || "EIP-" + n, status: meta.status || "", body: text };
        render(eipCache[n]);
      })
      .catch(function () { eipCache[n] = "failed"; });
  }

  document.addEventListener(
    "scroll",
    function (event) {
      // scrolling inside the card keeps it open
      if (card && card.contains(event.target)) return;
      hide();
    },
    true
  );
})();
