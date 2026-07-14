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
   * master at hover time, so upstream edits appear without rebuilding the
   * spec. The baked card is the instant/offline fallback. */
  var eipCache = {};
  function liveEip(n, target) {
    function render(eip) {
      if (!card || card !== target || card.dataset.for !== "eip-" + n) return;
      var doc = card.querySelector(".sail-hovercard-doc") || card;
      doc.textContent = "";
      var head = document.createElement("strong");
      head.textContent = "EIP-" + n + ": " + eip.title;
      var status = document.createElement("small");
      status.textContent = eip.status ? " (" + eip.status + ", live)" : " (live)";
      var body = document.createElement("p");
      body.textContent = eip.summary;
      doc.appendChild(head);
      doc.appendChild(status);
      doc.appendChild(body);
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
            var i = line.indexOf(":");
            if (i > 0) meta[line.slice(0, i).trim()] = line.slice(i + 1).trim();
          });
          text = text.slice(end + 4);
        }
        var summary = "";
        var sections = text.split(/^## +/m).slice(1);
        for (var i = 0; i < sections.length; i++) {
          var nl = sections[i].indexOf("\n");
          var heading = sections[i].slice(0, nl).trim().toLowerCase();
          if (heading === "simple summary" || heading === "abstract") {
            summary = sections[i].slice(nl + 1).trim();
            break;
          }
        }
        if (!summary && sections.length) summary = sections[0].slice(sections[0].indexOf("\n") + 1).trim();
        summary = summary
          .replace(/\[([^\]]*)\]\([^)]*\)/g, "$1")
          .replace(/`/g, "")
          .split(/\n\n+/).slice(0, 2).join(" ")
          .replace(/\s+/g, " ");
        if (summary.length > 600) summary = summary.slice(0, 600) + "…";
        eipCache[n] = { title: meta.title || "EIP-" + n, status: meta.status || "", summary: summary };
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
