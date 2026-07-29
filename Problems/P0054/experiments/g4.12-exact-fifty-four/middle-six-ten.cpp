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

using SupportMask = std::uint16_t;
using PointMask = std::uint32_t;

struct Cover {
	SupportMask mask;
	int size;
};

constexpr int ROWS = 4;
constexpr int SUPPORTS = 14;
constexpr int FULL = 15;

std::vector<Cover> covers;
std::array<int, SUPPORTS> multiplicity{};
std::array<int, ROWS> degree{};
std::uint64_t multiplicity_vectors = 0;
std::uint64_t compatible_extensions = 0;
std::map<std::pair<int, int>, std::uint64_t> blocker_histogram;
std::set<std::string> canonical_classes;

int support_value(int index)
{
	return index + 1;
}

bool is_minimal_cover(SupportMask chosen)
{
	int united = 0;
	for (int index = 0; index < SUPPORTS; ++index) {
		if (chosen & (SupportMask{1} << index)) united |= support_value(index);
	}
	if (united != FULL) return false;
	for (int omitted = 0; omitted < SUPPORTS; ++omitted) {
		if (!(chosen & (SupportMask{1} << omitted))) continue;
		int without = 0;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (index != omitted && (chosen & (SupportMask{1} << index))) {
				without |= support_value(index);
			}
		}
		if (without == FULL) return false;
	}
	return true;
}

bool is_clutter(SupportMask active)
{
	for (int left = 0; left < ROWS; ++left) {
		for (int right = 0; right < ROWS; ++right) {
			if (left == right) continue;
			bool subset = true;
			for (int index = 0; index < SUPPORTS; ++index) {
				if (!(active & (SupportMask{1} << index))) continue;
				const int support = support_value(index);
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

std::pair<int, int> weighted_counts(const std::vector<Cover> &active_covers)
{
	int total = 0;
	int pairs = 0;
	for (const Cover &cover : active_covers) {
		int choices = 1;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (!(cover.mask & (SupportMask{1} << index))) continue;
			choices *= std::max(1, multiplicity[index]);
		}
		total += choices;
		if (cover.size == 2) pairs += choices;
	}
	return {total, pairs};
}

void expand_cover(
	const std::vector<int> &support_indices,
	const std::array<std::vector<int>, SUPPORTS> &points_by_support,
	int position,
	PointMask current,
	std::set<PointMask> &result
)
{
	if (position == static_cast<int>(support_indices.size())) {
		result.insert(current);
		return;
	}
	for (int point : points_by_support[support_indices[position]]) {
		expand_cover(
			support_indices,
			points_by_support,
			position + 1,
			current | (PointMask{1} << point),
			result
		);
	}
}

bool compatible_with_kernel_a(
	const std::vector<Cover> &active_covers,
	const std::array<std::vector<int>, SUPPORTS> &points_by_support,
	int point_count
)
{
	std::array<PointMask, ROWS> rows{};
	for (int index = 0; index < SUPPORTS; ++index) {
		const int support = support_value(index);
		for (int point : points_by_support[index]) {
			for (int row = 0; row < ROWS; ++row) {
				if (support & (1 << row)) rows[row] |= PointMask{1} << point;
			}
		}
	}

	std::set<PointMask> blocker_rows;
	for (const Cover &cover : active_covers) {
		std::vector<int> support_indices;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (cover.mask & (SupportMask{1} << index)) support_indices.push_back(index);
		}
		expand_cover(support_indices, points_by_support, 0, 0, blocker_rows);
	}
	const int required_fixed_rows = std::max(0, static_cast<int>(blocker_rows.size()) - 3);

	for (PointMask row : rows) {
		if (std::popcount(row) != 3) continue;
		std::array<int, 3> labelled{};
		int next = 0;
		for (int point = 0; point < point_count; ++point) {
			if (row & (PointMask{1} << point)) labelled[next++] = point;
		}
		std::sort(labelled.begin(), labelled.end());
		do {
			for (int u = 0; u < point_count; ++u) {
				if (row & (PointMask{1} << u)) continue;
				for (int v = 0; v < point_count; ++v) {
					if (v == u || (row & (PointMask{1} << v))) continue;
					for (int w = 0; w < point_count; ++w) {
						if (w == u || w == v || (row & (PointMask{1} << w))) continue;
						const std::array<PointMask, 3> fixed{{
							(PointMask{1} << labelled[0]) | (PointMask{1} << u) |
								(PointMask{1} << v),
							(PointMask{1} << labelled[1]) | (PointMask{1} << u) |
								(PointMask{1} << w),
							(PointMask{1} << labelled[2]) | (PointMask{1} << v) |
								(PointMask{1} << w),
						}};
						int present = 0;
						for (PointMask candidate : fixed) {
							if (blocker_rows.contains(candidate)) ++present;
						}
						if (present >= required_fixed_rows) return true;
					}
				}
			}
		} while (std::next_permutation(labelled.begin(), labelled.end()));
	}
	return false;
}

std::string canonical_key()
{
	std::vector<std::pair<int, int>> best;
	bool has_best = false;
	std::array<int, ROWS> permutation{0, 1, 2, 3};
	do {
		std::vector<std::pair<int, int>> transformed;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (!multiplicity[index]) continue;
			int image = 0;
			for (int row = 0; row < ROWS; ++row) {
				if (support_value(index) & (1 << row)) image |= 1 << permutation[row];
			}
			transformed.push_back({image, multiplicity[index]});
		}
		std::sort(transformed.begin(), transformed.end());
		if (!has_best || transformed < best) {
			best = transformed;
			has_best = true;
		}
	} while (std::next_permutation(permutation.begin(), permutation.end()));
	std::ostringstream output;
	for (const auto &[support, value] : best) output << support << ':' << value << ',';
	return output.str();
}

void enumerate_multiplicities(
	const std::vector<int> &active_supports,
	const std::vector<Cover> &active_covers,
	int position
)
{
	if (position == static_cast<int>(active_supports.size())) {
		if (*std::min_element(degree.begin(), degree.end()) < 3) return;
		if (std::find(degree.begin(), degree.end(), 3) == degree.end()) return;
		const auto [total, pairs] = weighted_counts(active_covers);
		if (total > 6) return;
		++multiplicity_vectors;
		++blocker_histogram[{total, pairs}];
		canonical_classes.insert(canonical_key());

		std::array<std::vector<int>, SUPPORTS> points_by_support;
		int point_count = 0;
		for (int index = 0; index < SUPPORTS; ++index) {
			for (int copy = 0; copy < multiplicity[index]; ++copy) {
				points_by_support[index].push_back(point_count++);
			}
		}
		if (compatible_with_kernel_a(active_covers, points_by_support, point_count)) {
			++compatible_extensions;
		}
		return;
	}

	const int index = active_supports[position];
	const int support = support_value(index);
	int capacity = 6;
	for (int row = 0; row < ROWS; ++row) {
		if (support & (1 << row)) capacity = std::min(capacity, 6 - degree[row]);
	}
	for (int value = 1; value <= capacity; ++value) {
		multiplicity[index] = value;
		for (int row = 0; row < ROWS; ++row) {
			if (support & (1 << row)) degree[row] += value;
		}
		if (weighted_counts(active_covers).first <= 6) {
			enumerate_multiplicities(active_supports, active_covers, position + 1);
		}
		for (int row = 0; row < ROWS; ++row) {
			if (support & (1 << row)) degree[row] -= value;
		}
	}
	multiplicity[index] = 0;
}

int main(int argc, char **argv)
{
	if (argc != 2) {
		std::cerr << "usage: middle-six-ten OUTPUT\n";
		return 2;
	}
	for (SupportMask chosen = 1; chosen < (SupportMask{1} << SUPPORTS); ++chosen) {
		const int chosen_size = std::popcount(chosen);
		if (chosen_size < 2 || chosen_size > ROWS || !is_minimal_cover(chosen)) continue;
		covers.push_back({chosen, chosen_size});
	}

	std::uint64_t support_feasible_masks = 0;
	for (SupportMask active = 1; active < (SupportMask{1} << SUPPORTS); ++active) {
		std::array<int, ROWS> support_degrees{};
		for (int index = 0; index < SUPPORTS; ++index) {
			if (!(active & (SupportMask{1} << index))) continue;
			for (int row = 0; row < ROWS; ++row) {
				if (support_value(index) & (1 << row)) ++support_degrees[row];
			}
		}
		if (*std::min_element(support_degrees.begin(), support_degrees.end()) == 0) continue;
		if (*std::max_element(support_degrees.begin(), support_degrees.end()) > 6) continue;
		if (!is_clutter(active)) continue;

		std::vector<Cover> active_covers;
		SupportMask used = 0;
		for (const Cover &cover : covers) {
			if ((cover.mask & active) != cover.mask) continue;
			active_covers.push_back(cover);
			used |= cover.mask;
		}
		if (active_covers.empty() || active_covers.size() > 6 || used != active) continue;
		++support_feasible_masks;

		std::vector<int> active_supports;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (active & (SupportMask{1} << index)) active_supports.push_back(index);
		}
		degree.fill(0);
		enumerate_multiplicities(active_supports, active_covers, 0);
	}

	std::ofstream output(argv[1]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "schema=p0054.g4.12.middle-six-ten.v1\n";
	output << "supports=" << SUPPORTS << '\n';
	output << "minimal_support_covers=" << covers.size() << '\n';
	output << "active_masks_checked=" << ((1 << SUPPORTS) - 1) << '\n';
	output << "support_feasible_masks=" << support_feasible_masks << '\n';
	output << "multiplicity_vectors=" << multiplicity_vectors << '\n';
	for (const auto &[profile, frequency] : blocker_histogram) {
		output << "blockers_" << profile.first << "_pairs_" << profile.second
			<< '=' << frequency << '\n';
	}
	output << "row_permutation_classes=" << canonical_classes.size() << '\n';
	int class_index = 0;
	for (const std::string &key : canonical_classes) {
		output << "class_" << ++class_index << '=' << key << '\n';
	}
	output << "compatible_extensions=" << compatible_extensions << '\n';
	std::cout << "output=" << argv[1] << '\n';
	return 0;
}
