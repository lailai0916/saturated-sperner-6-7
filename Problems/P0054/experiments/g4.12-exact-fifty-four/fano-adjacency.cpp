#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>

using Mask = std::uint16_t;

constexpr std::array<std::array<int, 3>, 7> LINES{{
	{{0, 1, 2}},
	{{0, 3, 4}},
	{{0, 5, 6}},
	{{1, 3, 5}},
	{{1, 4, 6}},
	{{2, 3, 6}},
	{{2, 4, 5}},
}};

int size(Mask mask)
{
	return std::popcount(mask);
}

Mask selected_edge(const std::array<int, 3> &line, int choice)
{
	constexpr std::array<std::array<int, 2>, 3> pairs{{
		{{0, 1}},
		{{0, 2}},
		{{1, 2}},
	}};
	return static_cast<Mask>((Mask{1} << line[pairs[choice][0]]) |
		(Mask{1} << line[pairs[choice][1]]));
}

bool hits_all(Mask candidate, const std::vector<Mask> &rows)
{
	for (Mask row : rows) {
		if (!(candidate & row)) return false;
	}
	return true;
}

std::vector<Mask> blockers(const std::vector<Mask> &rows, int point_count)
{
	std::vector<Mask> result;
	for (Mask candidate = 1; candidate < (Mask{1} << point_count); ++candidate) {
		if (!hits_all(candidate, rows)) continue;
		bool minimal = true;
		for (int point = 0; point < point_count; ++point) {
			if (!(candidate & (Mask{1} << point))) continue;
			if (hits_all(candidate ^ (Mask{1} << point), rows)) {
				minimal = false;
				break;
			}
		}
		if (minimal) result.push_back(candidate);
	}
	return result;
}

std::vector<Mask> extended_blockers(
	const std::vector<Mask> &base_blockers,
	Mask active_part,
	int outside_count
)
{
	std::set<Mask> candidates;
	for (Mask cover : base_blockers) {
		if (cover & active_part) {
			candidates.insert(cover);
			continue;
		}
		for (int point = 0; point < 7; ++point) {
			if (active_part & (Mask{1} << point)) {
				candidates.insert(static_cast<Mask>(cover | (Mask{1} << point)));
			}
		}
		for (int point = 0; point < outside_count; ++point) {
			candidates.insert(static_cast<Mask>(cover | (Mask{1} << (7 + point))));
		}
	}

	std::vector<Mask> ordered(candidates.begin(), candidates.end());
	std::sort(ordered.begin(), ordered.end(), [](Mask left, Mask right) {
		return std::pair{size(left), left} < std::pair{size(right), right};
	});
	std::vector<Mask> result;
	for (Mask candidate : ordered) {
		bool minimal = true;
		for (Mask accepted : result) {
			if ((accepted & candidate) == accepted) {
				minimal = false;
				break;
			}
		}
		if (minimal) result.push_back(candidate);
	}
	return result;
}

int minimum_size(const std::vector<Mask> &rows)
{
	int result = 100;
	for (Mask row : rows) result = std::min(result, size(row));
	return result;
}

int main(int argc, char **argv)
{
	if (argc != 2) {
		std::cerr << "usage: fano-adjacency OUTPUT\n";
		return 2;
	}

	std::uint64_t graph_count = 0;
	std::uint64_t split_7_6_admissible = 0;
	std::map<int, std::uint64_t> split_7_6_histogram;
	std::uint64_t split_8_5_candidates = 0;
	std::uint64_t split_8_5_five_blockers = 0;
	std::map<int, std::uint64_t> split_8_5_five_minimum_sizes;
	std::uint64_t split_8_5_admissible = 0;
	std::map<int, std::uint64_t> split_8_5_histogram;

	constexpr int graph_limit = 2187;
	for (int code = 0; code < graph_limit; ++code) {
		int remaining = code;
		std::vector<Mask> edges;
		for (const auto &line : LINES) {
			edges.push_back(selected_edge(line, remaining % 3));
			remaining /= 3;
		}
		if (std::set<Mask>(edges.begin(), edges.end()).size() != 7) return 3;
		++graph_count;

		const std::vector<Mask> base_blockers = blockers(edges, 7);
		if (minimum_size(base_blockers) >= 4) {
			++split_7_6_admissible;
			++split_7_6_histogram[static_cast<int>(base_blockers.size())];
		}

		for (Mask active_part = 0; active_part < (Mask{1} << 7); ++active_part) {
			bool independent = true;
			for (Mask edge : edges) {
				if ((edge & active_part) == edge) independent = false;
			}
			if (!independent) continue;
			for (int outside_count = 0; outside_count + size(active_part) <= 5;
				++outside_count) {
				const int row_size = size(active_part) + outside_count;
				if (row_size < 2) continue;
				++split_8_5_candidates;
				const std::vector<Mask> current = extended_blockers(
					base_blockers,
					active_part,
					outside_count
				);
				const int current_minimum = minimum_size(current);
				if (current.size() == 5) {
					++split_8_5_five_blockers;
					++split_8_5_five_minimum_sizes[current_minimum];
				}
				if (current_minimum >= 4) {
					++split_8_5_admissible;
					++split_8_5_histogram[static_cast<int>(current.size())];
				}
			}
		}
	}

	std::ofstream output(argv[1]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "schema=p0054.g4.12.fano-adjacency.v1\n";
	output << "fano_graphs=" << graph_count << '\n';
	output << "split_7_6_admissible=" << split_7_6_admissible << '\n';
	for (const auto &[count, frequency] : split_7_6_histogram) {
		output << "split_7_6_blockers_" << count << '=' << frequency << '\n';
	}
	output << "split_7_6_target_hits=" << split_7_6_histogram[6] << '\n';
	output << "split_8_5_candidates=" << split_8_5_candidates << '\n';
	output << "split_8_5_five_blockers=" << split_8_5_five_blockers << '\n';
	for (const auto &[minimum, frequency] : split_8_5_five_minimum_sizes) {
		output << "split_8_5_five_minimum_" << minimum << '=' << frequency << '\n';
	}
	output << "split_8_5_admissible=" << split_8_5_admissible << '\n';
	for (const auto &[count, frequency] : split_8_5_histogram) {
		output << "split_8_5_blockers_" << count << '=' << frequency << '\n';
	}
	output << "split_8_5_target_hits=" << split_8_5_histogram[5] << '\n';
	std::cout << "output=" << argv[1] << '\n';
	return 0;
}
