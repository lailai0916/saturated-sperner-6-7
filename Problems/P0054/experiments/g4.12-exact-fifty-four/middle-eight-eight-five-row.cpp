#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

constexpr int ROWS = 5;
constexpr int FULL = 31;
constexpr int MAX_ROW_SIZE = 8;
constexpr int MAX_BLOCKERS = 8;
constexpr int MAX_PAIR_BLOCKERS = 3;

struct Cover {
	std::uint32_t mask;
	int size;
};

std::vector<int> supports;
std::vector<Cover> covers;
std::array<int, 32> multiplicity{};
std::array<int, ROWS> degree{};
std::uint64_t active_masks_checked = 0;
std::uint64_t support_feasible_masks = 0;
std::uint64_t multiplicity_vectors = 0;
std::map<std::pair<int, int>, std::uint64_t> blocker_histogram;
std::set<std::string> canonical_classes;

bool is_minimal_cover(const std::vector<int> &chosen)
{
	int united = 0;
	for (int index : chosen) united |= supports[index];
	if (united != FULL) return false;
	for (int omitted : chosen) {
		int without = 0;
		for (int index : chosen) {
			if (index != omitted) without |= supports[index];
		}
		if (without == FULL) return false;
	}
	return true;
}

void enumerate_covers(int target_size, int next, std::vector<int> &chosen)
{
	if (static_cast<int>(chosen.size()) == target_size) {
		if (!is_minimal_cover(chosen)) return;
		std::uint32_t mask = 0;
		for (int index : chosen) mask |= std::uint32_t{1} << index;
		covers.push_back({mask, target_size});
		return;
	}
	for (int index = next; index < static_cast<int>(supports.size()); ++index) {
		chosen.push_back(index);
		enumerate_covers(target_size, index + 1, chosen);
		chosen.pop_back();
	}
}

bool is_clutter(std::uint32_t active)
{
	for (int left = 0; left < ROWS; ++left) {
		for (int right = 0; right < ROWS; ++right) {
			if (left == right) continue;
			bool subset = true;
			for (int index = 0; index < static_cast<int>(supports.size()); ++index) {
				if (!(active & (std::uint32_t{1} << index))) continue;
				const int support = supports[index];
				if ((support & (1 << left)) && !(support & (1 << right))) {
					subset = false;
					break;
				}
			}
			if (subset) return false;
		}
	}
	return true;
}

std::pair<int, int> weighted_counts(const std::vector<int> &active_covers)
{
	int total = 0;
	int pairs = 0;
	for (int cover_index : active_covers) {
		const Cover &cover = covers[cover_index];
		int choices = 1;
		for (int index = 0; index < static_cast<int>(supports.size()); ++index) {
			if (cover.mask & (std::uint32_t{1} << index)) {
				choices *= multiplicity[supports[index]];
			}
		}
		total += choices;
		if (cover.size == 2) pairs += choices;
		if (total > MAX_BLOCKERS || pairs > MAX_PAIR_BLOCKERS) break;
	}
	return {total, pairs};
}

std::string canonical_key(int total, int pairs)
{
	std::vector<std::pair<int, int>> best;
	bool has_best = false;
	std::array<int, ROWS> permutation{0, 1, 2, 3, 4};
	do {
		std::vector<std::pair<int, int>> transformed;
		for (int support : supports) {
			if (!multiplicity[support]) continue;
			int image = 0;
			for (int row = 0; row < ROWS; ++row) {
				if (support & (1 << row)) image |= 1 << permutation[row];
			}
			transformed.push_back({image, multiplicity[support]});
		}
		std::sort(transformed.begin(), transformed.end());
		if (!has_best || transformed < best) {
			best = transformed;
			has_best = true;
		}
	} while (std::next_permutation(permutation.begin(), permutation.end()));
	std::ostringstream output;
	for (const auto &[support, value] : best) output << support << ':' << value << ',';
	return output.str() + "|b:" + std::to_string(total) + "|p:" + std::to_string(pairs);
}

void enumerate_multiplicities(
	const std::vector<int> &active_supports,
	const std::vector<int> &active_covers,
	int position
)
{
	if (position == static_cast<int>(active_supports.size())) {
		for (int row = 0; row < ROWS; ++row) {
			if (degree[row] < 3 || degree[row] > MAX_ROW_SIZE) return;
		}
		const auto [total, pairs] = weighted_counts(active_covers);
		if (total > MAX_BLOCKERS || pairs > MAX_PAIR_BLOCKERS) return;
		++multiplicity_vectors;
		++blocker_histogram[{total, pairs}];
		canonical_classes.insert(canonical_key(total, pairs));
		return;
	}

	const int support = active_supports[position];
	int capacity = MAX_ROW_SIZE;
	for (int row = 0; row < ROWS; ++row) {
		if (support & (1 << row)) {
			capacity = std::min(capacity, MAX_ROW_SIZE - degree[row]);
		}
	}
	for (int value = 1; value <= capacity; ++value) {
		multiplicity[support] = value;
		for (int row = 0; row < ROWS; ++row) {
			if (support & (1 << row)) degree[row] += value;
		}
		const auto [total, pairs] = weighted_counts(active_covers);
		if (total <= MAX_BLOCKERS && pairs <= MAX_PAIR_BLOCKERS) {
			bool can_reach = true;
			for (int row = 0; row < ROWS; ++row) {
				if (degree[row] >= 3) continue;
				bool can_grow = false;
				for (int later = position + 1;
					later < static_cast<int>(active_supports.size()); ++later) {
					if (active_supports[later] & (1 << row)) can_grow = true;
				}
				if (!can_grow) can_reach = false;
			}
			if (can_reach) {
				enumerate_multiplicities(active_supports, active_covers, position + 1);
			}
		}
		for (int row = 0; row < ROWS; ++row) {
			if (support & (1 << row)) degree[row] -= value;
		}
	}
	multiplicity[support] = 0;
}

int main(int argc, char **argv)
{
	if (argc != 2) {
		std::cerr << "usage: middle-eight-eight-five-row OUTPUT\n";
		return 2;
	}
	for (int support = 1; support <= FULL; ++support) {
		if (std::popcount(static_cast<unsigned>(support)) <= 3) {
			supports.push_back(support);
		}
	}
	std::sort(supports.begin(), supports.end());
	std::vector<int> chosen;
	for (int size = 2; size <= ROWS; ++size) enumerate_covers(size, 0, chosen);

	const std::uint32_t limit = std::uint32_t{1} << supports.size();
	for (std::uint32_t active = 1; active < limit; ++active) {
		++active_masks_checked;
		std::array<int, ROWS> support_degrees{};
		for (int index = 0; index < static_cast<int>(supports.size()); ++index) {
			if (!(active & (std::uint32_t{1} << index))) continue;
			for (int row = 0; row < ROWS; ++row) {
				if (supports[index] & (1 << row)) ++support_degrees[row];
			}
		}
		bool feasible = true;
		for (int row = 0; row < ROWS; ++row) {
			if (support_degrees[row] > MAX_ROW_SIZE || support_degrees[row] == 0) {
				feasible = false;
			}
		}
		if (!feasible || !is_clutter(active)) continue;

		std::vector<int> active_covers;
		std::uint32_t used = 0;
		int pair_covers = 0;
		for (int index = 0; index < static_cast<int>(covers.size()); ++index) {
			if ((covers[index].mask & active) != covers[index].mask) continue;
			active_covers.push_back(index);
			used |= covers[index].mask;
			if (covers[index].size == 2) ++pair_covers;
			if (active_covers.size() > MAX_BLOCKERS || pair_covers > MAX_PAIR_BLOCKERS) {
				break;
			}
		}
		if (active_covers.empty() || active_covers.size() > MAX_BLOCKERS) continue;
		if (pair_covers > MAX_PAIR_BLOCKERS || (used & active) != active) continue;
		++support_feasible_masks;

		std::vector<int> active_supports;
		for (int index = 0; index < static_cast<int>(supports.size()); ++index) {
			if (active & (std::uint32_t{1} << index)) {
				active_supports.push_back(supports[index]);
			}
		}
		degree.fill(0);
		enumerate_multiplicities(active_supports, active_covers, 0);
	}

	std::ofstream output(argv[1]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "schema=p0054.g4.12.middle-eight-eight-five-row.v1\n";
	output << "supports=" << supports.size() << '\n';
	output << "minimal_support_covers=" << covers.size() << '\n';
	output << "active_masks_checked=" << active_masks_checked << '\n';
	output << "support_feasible_masks=" << support_feasible_masks << '\n';
	output << "multiplicity_vectors=" << multiplicity_vectors << '\n';
	for (const auto &[profile, count] : blocker_histogram) {
		output << "blockers_" << profile.first << "_pairs_" << profile.second
			<< '=' << count << '\n';
	}
	output << "row_permutation_classes=" << canonical_classes.size() << '\n';
	int class_index = 0;
	for (const std::string &key : canonical_classes) {
		output << "class_" << ++class_index << '=' << key << '\n';
	}
	std::cout << "output=" << argv[1] << '\n';
	return 0;
}
