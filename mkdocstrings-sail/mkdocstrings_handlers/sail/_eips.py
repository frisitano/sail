"""EIP reference linking and hover cards.

``EIP-N`` mentions in specification prose become links to
``https://eips.ethereum.org/EIPS/eip-N``; when a local checkout of the
`ethereum/EIPs <https://github.com/ethereum/EIPs>`_ repository is
configured, each reference also carries a hover card with the EIP's title,
status, and summary, extracted from the EIP's own Markdown.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional

from markupsafe import escape

_EIP_REF = re.compile(r"(?<![\w\[`-])EIP-(\d+)\b(?!\]|[\w-])")
_CODE_SPLIT = re.compile(r"(```.*?```|`[^`]*`)", re.S)
_MD_LINK = re.compile(r"\[([^\]]*)\]\([^)]*\)")
_HEADING = re.compile(r"^##\s+(.+)$", re.M)

EIP_URL = "https://eips.ethereum.org/EIPS/eip-{n}"


class EipIndex:
    """Lazily loads EIP metadata from a local ethereum/EIPs checkout."""

    def __init__(self, eips_dir: Optional[str | Path]):
        self._dir = Path(eips_dir) if eips_dir else None
        self._cache: dict[int, Optional[dict]] = {}

    def lookup(self, number: int) -> Optional[dict]:
        if self._dir is None:
            return None
        if number not in self._cache:
            self._cache[number] = self._load(number)
        return self._cache[number]

    def _load(self, number: int) -> Optional[dict]:
        path = self._dir / f"eip-{number}.md"
        if not path.exists():
            return None
        text = path.read_text(errors="replace")
        meta = {}
        if text.startswith("---"):
            end = text.find("\n---", 3)
            for line in text[3:end].strip().splitlines():
                key, _, value = line.partition(":")
                meta[key.strip()] = value.strip()
            text = text[end + 4 :]
        summary = self._summary(text)
        return {
            "number": number,
            "title": meta.get("title", f"EIP-{number}"),
            "status": meta.get("status", ""),
            "summary": summary,
        }

    @staticmethod
    def _summary(body: str) -> str:
        """The first Simple Summary / Abstract paragraphs, as plain text."""
        sections = re.split(r"^##\s+", body, flags=re.M)
        chosen = ""
        for section in sections[1:]:
            heading, _, content = section.partition("\n")
            if heading.strip().lower() in ("simple summary", "abstract"):
                chosen = content.strip()
                break
        if not chosen and len(sections) > 1:
            chosen = sections[1].partition("\n")[2].strip()
        text = _MD_LINK.sub(r"\1", chosen).replace("`", "")
        paragraphs = [p.strip() for p in text.split("\n\n") if p.strip()]
        out = " ".join(" ".join(paragraphs[:2]).split())
        return out[:600] + ("…" if len(out) > 600 else "")

    def render_full_html(self, number: int) -> Optional[str]:
        """The complete EIP rendered to HTML (tables, highlighted code),
        for on-demand hover fragments. Uses the site's pygments classes so
        the page stylesheet applies."""
        import markdown

        if self._dir is None:
            return None
        path = self._dir / f"eip-{number}.md"
        if not path.exists():
            return None
        text = path.read_text(errors="replace")
        meta = {}
        if text.startswith("---"):
            end = text.find("\n---", 3)
            for line in text[3:end].strip().splitlines():
                key, _, value = line.partition(":")
                meta[key.strip()] = value.strip()
            text = text[end + 4 :]
        # EIP specification code is Python by convention (EIP-1); default
        # untagged fences to it — pygments' guesser misfires on pseudocode.
        lines = text.split("\n")
        inside = False
        for i, line in enumerate(lines):
            stripped = line.strip()
            if stripped.startswith("```"):
                if not inside and stripped == "```":
                    lines[i] = line.replace("```", "```python", 1)
                inside = not inside
        text = "\n".join(lines)
        body = markdown.markdown(
            text,
            extensions=["extra", "codehilite", "sane_lists"],
            extension_configs={"codehilite": {"css_class": "highlight", "guess_lang": True}},
        )
        title = escape(meta.get("title", f"EIP-{number}"))
        status = f' <small>({escape(meta["status"])})</small>' if meta.get("status") else ""
        return f"<h2>EIP-{number}: {title}{status}</h2>\n{body}"

    def card_html(self, number: int) -> Optional[str]:
        eip = self.lookup(number)
        if eip is None:
            return None
        status = f' <small>({escape(eip["status"])})</small>' if eip["status"] else ""
        return (
            f'<template class="sail-hovercard" data-anchor="eip-{number}">'
            f'<div class="sail-hovercard-doc"><strong>EIP-{number}: {escape(eip["title"])}</strong>{status}'
            f"<p>{escape(eip['summary'])}</p></div></template>"
        )


def link_eip_references(markdown: str, seen: set[int], *, hover: bool) -> str:
    """Wrap bare ``EIP-N`` mentions in links (skipping code spans/fences).

    With ``hover`` set, links carry a ``data-sail-hover`` attribute keyed
    ``eip-N`` (via ``attr_list``) so the hover script reveals the EIP card.
    Numbers substituted are added to ``seen``.
    """

    def replace(match: re.Match) -> str:
        n = int(match.group(1))
        seen.add(n)
        attrs = f'{{: data-sail-hover="eip-{n}" .sail-eip }}' if hover else ""
        return f"[EIP-{n}]({EIP_URL.format(n=n)}){attrs}"

    parts = _CODE_SPLIT.split(markdown)
    return "".join(part if i % 2 else _EIP_REF.sub(replace, part) for i, part in enumerate(parts))
