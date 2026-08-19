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
# with no page CSS and no webfont, and the stack is resolved by the host OS. On
# macOS that means San Francisco, which is split into SF Text and SF Display with
# a switch near 20px and glyph IDs that are out of sync between the two; at least
# one Mac renders the chart titles, the text that crosses that boundary, as
# overlapping nonsense while the smaller subtitles and ticks beside them are fine.
# Named faces sidestep the question and narrow how much the cards vary between
# platforms, which the hand-tuned label spacing in these scripts likes.
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
