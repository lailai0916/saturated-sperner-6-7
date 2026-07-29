from scripts.p0054_size54_system_search import (
    CERTIFIED_LAYER_MINIMA,
    SAFE_LAYER_UPPER_BOUNDS,
)


def test_safe_layer_upper_bounds_follow_from_two_total_slack_units() -> None:
    assert CERTIFIED_LAYER_MINIMA == (1, 6, 12, 14, 12, 6, 1)
    assert sum(CERTIFIED_LAYER_MINIMA) == 52
    assert SAFE_LAYER_UPPER_BOUNDS == (3, 8, 14, 16, 14, 8, 3)
