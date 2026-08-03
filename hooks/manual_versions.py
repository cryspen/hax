"""MkDocs hook powering the Manual version switcher.

The Manual is built twice as two subsections of the Manual (see
``docs/default.nix``): "Branch main" from the current commit (served under
``manual/main/``) and "Version <x>" from the latest hax release (served under
``manual/<version>/``, e.g. ``manual/v0.3.7/``). This hook computes, for every
Manual page, the URL of the same page in the *other* version so that
``docs/overrides/main.html`` can render a switcher above the content. When a page
only exists in one version (the two trees may diverge), the switcher falls back
to that version's Manual landing page instead of a dead link.

Configuration lives under ``extra.manual_versions`` in ``mkdocs.yml``.
"""

from mkdocs.utils import get_relative_url

# Maps every documentation page's source path to its built URL. Populated in
# ``on_files`` (which has access to the full file list) and consumed in
# ``on_page_context`` (which does not).
_page_urls: dict[str, str] = {}


def on_files(files, config):
    _page_urls.clear()
    for file in files:
        if file.is_documentation_page():
            _page_urls[file.src_uri] = file.url
    return files


def on_page_context(context, page, config, nav):
    cfg = (config.extra or {}).get("manual_versions") or {}
    main_dir = cfg.get("main_dir", "manual")
    release_dir = cfg.get("release_dir")
    release_label = cfg.get("release_label", "release")
    if not release_dir:
        return context

    src = page.file.src_uri
    if src.startswith(main_dir + "/"):
        current, rest = "main", src[len(main_dir) + 1:]
    elif src.startswith(release_dir + "/"):
        current, rest = "release", src[len(release_dir) + 1:]
    else:
        return context

    def resolve(version_dir):
        """URL of `rest` within `version_dir`, or that version's home as fallback."""
        candidate = version_dir + "/" + rest if rest else version_dir + "/index.md"
        if candidate in _page_urls:
            return _page_urls[candidate], True
        home = _page_urls.get(version_dir + "/index.md", version_dir + "/")
        return home, False

    main_url, main_exists = resolve(main_dir)
    release_url, release_exists = resolve(release_dir)

    context["manual_versions"] = {
        "current": current,
        "release_label": release_label,
        "main_href": get_relative_url(main_url, page.url),
        "main_exists": main_exists,
        "release_href": get_relative_url(release_url, page.url),
        "release_exists": release_exists,
    }
    return context
