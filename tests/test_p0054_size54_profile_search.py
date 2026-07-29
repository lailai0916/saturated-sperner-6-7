import itertools

from scripts.p0054_size54_profile_search import two_slack_profiles
from scripts.p0054_size54_system_search import CERTIFIED_LAYER_MINIMA


def test_two_slack_profiles_are_complete_and_unique() -> None:
    profiles = two_slack_profiles()
    assert len(profiles) == 28
    assert len(set(profiles)) == 28
    assert all(sum(profile) == 54 for profile in profiles)


def test_every_actual_slack_vector_of_sum_at_most_two_is_covered() -> None:
    profiles = two_slack_profiles()
    actual_slacks = [
        values
        for values in itertools.product(range(3), repeat=7)
        if sum(values) <= 2
    ]
    for actual in actual_slacks:
        actual_sizes = tuple(
            minimum + extra
            for minimum, extra in zip(
                CERTIFIED_LAYER_MINIMA, actual, strict=True
            )
        )
        assert any(
            all(value <= bound for value, bound in zip(actual_sizes, profile, strict=True))
            for profile in profiles
        )
