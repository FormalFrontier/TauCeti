"""Shared visual language for SVG charts on the Tau Ceti statistics page."""

BG = "#101936"
PANEL = "#1b2547"
BAR_BG = "#27335a"
GRID = "rgba(255,255,255,0.08)"
AXIS = "rgba(255,255,255,0.18)"
TEXT = "#eef2fb"
MUTED = "#9aa6c9"
# Deliberately concrete, and deliberately not `system-ui`/`ui-sans-serif`. These
# charts are served as `<img src="...svg">`, so each SVG is an isolated document
# with no page CSS and no webfont: the family is whatever the host OS resolves.
# One Mac viewing the statistics page rendered every chart title as overlapping
# accented-Latin nonsense while the subtitle and axis labels in the same file
# stayed clean, a split that follows a size boundary near 20px. Two factors set
# the rendered size: css_px below turns a 19-unit title into 19 * viewBox_width
# / 980 user units, and fitting that viewBox to the page column multiplies by
# column_width / viewBox_width. The statistics column is at most --max (1100px),
# so titles land just above 20 CSS px there, barely clearing the boundary,
# whatever a card's viewBox width, while the 13-unit subtitle and 12-unit ticks
# stay in the mid-teens. A few figures sit well above it (participation's
# 42-unit total, the rolling-history card's 24-unit latest values); on the front
# page, where the growth chart is capped at 760px, nothing reaches it. That
# boundary is where macOS has historically switched between optical variants of
# its system font whose glyph IDs disagree, so text shaped against one and drawn
# with the other comes out scrambled; Chromium documents the failure and its
# own fix for it in
# https://web.dev/blog/more-variable-font-options-in-chromium-83 . Whether a
# current macOS and browser still reach that path is not something this
# repository can establish, and naming real faces avoids the question.
FONT_FAMILY = "'Helvetica Neue',Helvetica,Arial,'Liberation Sans',sans-serif"

# The participation card established the site's chart typography at this native width.
# Scale design-space font sizes with each SVG's viewBox so all cards have the same
# perceived type size when CSS fits them to the page column.
REFERENCE_WIDTH = 980

# Distinct on the navy background; tools may assign these by order or stable hash.
PALETTE = [
    "#5eead4", "#ff9d4d", "#60a5fa", "#fb7185", "#c084fc", "#4ade80",
    "#fde047", "#22d3ee", "#f472b6", "#a3e635", "#818cf8", "#fb923c",
    "#38bdf8", "#f87171", "#2dd4bf", "#e879f9",
]

def css_px(width: int, size: float) -> str:
    """A design-space font size that renders consistently across viewBox widths."""
    return f"{size * width / REFERENCE_WIDTH:.1f}px"


def svg_unit(width: int, size: float) -> str:
    """A design-space length that renders consistently across viewBox widths."""
    return f"{size * width / REFERENCE_WIDTH:.1f}"


def base_css(width: int) -> str:
    """Shared typography, ticks, grid, and axes for one chart width."""
    return (
        f"text{{font-family:{FONT_FAMILY};fill:{TEXT}}}"
        f".title{{font-size:{css_px(width, 19)};font-weight:600}}"
        f".subtitle{{font-size:{css_px(width, 13)};fill:{MUTED}}}"
        f".tick{{font-size:{css_px(width, 12)};fill:{MUTED}}}"
        f".grid{{stroke:{GRID};stroke-width:{svg_unit(width, 1)}}}"
        f".axis{{stroke:{AXIS};stroke-width:{svg_unit(width, 1)}}}"
    )


def card_rect(width: int, height: int) -> str:
    """The common rounded chart background and border."""
    return (
        f'<rect x="0.5" y="0.5" width="{width-1}" height="{height-1}" '
        f'rx="{svg_unit(width, 12)}" fill="{BG}" stroke="{PANEL}" '
        f'stroke-width="{svg_unit(width, 1)}"/>'
    )
