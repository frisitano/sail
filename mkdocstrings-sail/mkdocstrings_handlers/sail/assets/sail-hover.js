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
  });

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
