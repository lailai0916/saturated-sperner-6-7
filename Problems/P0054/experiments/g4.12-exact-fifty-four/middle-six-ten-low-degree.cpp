#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

using SupportSet = std::uint32_t;

struct Cover {
	SupportSet supports;
	int size;
};

struct BranchSummary {
	std::uint64_t degree_vectors = 0;
	std::uint64_t clutter_vectors = 0;
	std::array<std::uint64_t, 4> core_matching_histogram{};
	std::array<std::uint64_t, 4> core_minimum_blockers{};
	std::array<std::uint64_t, 4> clutter_matching_histogram{};
	std::array<std::uint64_t, 4> clutter_minimum_blockers{};
	std::uint64_t target_kernels = 0;
};

constexpr int VERTICES = 6;
constexpr int SUPPORTS = 21;
constexpr int FULL = (1 << VERTICES) - 1;

std::array<int, SUPPORTS> support_masks{};
std::array<int, SUPPORTS> multiplicity{};
std::array<int, VERTICES> degree{};
std::vector<Cover> covers;

void initialize_supports()
{
	int next = 0;
	for (int vertex = 0; vertex < VERTICES; ++vertex) {
		support_masks[next++] = 1 << vertex;
	}
	for (int left = 0; left < VERTICES; ++left) {
		for (int right = left + 1; right < VERTICES; ++right) {
			support_masks[next++] = (1 << left) | (1 << right);
		}
	}
}

bool is_minimal_cover(SupportSet chosen)
{
	int united = 0;
	for (int index = 0; index < SUPPORTS; ++index) {
		if (chosen & (SupportSet{1} << index)) united |= support_masks[index];
	}
	if (united != FULL) return false;
	for (int omitted = 0; omitted < SUPPORTS; ++omitted) {
		if (!(chosen & (SupportSet{1} << omitted))) continue;
		int without = 0;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (index != omitted && (chosen & (SupportSet{1} << index))) {
				without |= support_masks[index];
			}
		}
		if (without == FULL) return false;
	}
	return true;
}

void initialize_covers()
{
	for (SupportSet chosen = 1; chosen < (SupportSet{1} << SUPPORTS); ++chosen) {
		if (is_minimal_cover(chosen)) {
			covers.push_back({chosen, std::popcount(chosen)});
		}
	}
}

bool is_clutter()
{
	for (int left = 0; left < VERTICES; ++left) {
		for (int right = 0; right < VERTICES; ++right) {
			if (left == right) continue;
			bool subset = true;
			for (int index = 0; index < SUPPORTS; ++index) {
				if (!multiplicity[index]) continue;
				if ((support_masks[index] & (1 << left)) &&
					!(support_masks[index] & (1 << right))) {
					subset = false;
					break;
				}
			}
			if (subset) return false;
		}
	}
	return true;
}

int matching_number()
{
	std::vector<int> edges;
	for (int index = 0; index < SUPPORTS; ++index) {
		if (multiplicity[index] && std::popcount(static_cast<unsigned>(support_masks[index])) == 2) {
			edges.push_back(support_masks[index]);
		}
	}
	for (int i = 0; i < static_cast<int>(edges.size()); ++i) {
		for (int j = i + 1; j < static_cast<int>(edges.size()); ++j) {
			if (edges[i] & edges[j]) continue;
			for (int k = j + 1; k < static_cast<int>(edges.size()); ++k) {
				if (!(edges[i] & edges[k]) && !(edges[j] & edges[k])) return 3;
			}
		}
	}
	for (int i = 0; i < static_cast<int>(edges.size()); ++i) {
		for (int j = i + 1; j < static_cast<int>(edges.size()); ++j) {
			if (!(edges[i] & edges[j])) return 2;
		}
	}
	return edges.empty() ? 0 : 1;
}

std::pair<std::uint64_t, std::uint64_t> blocker_counts()
{
	std::uint64_t total = 0;
	std::uint64_t triples = 0;
	for (const Cover &cover : covers) {
		std::uint64_t choices = 1;
		for (int index = 0; index < SUPPORTS; ++index) {
			if (cover.supports & (SupportSet{1} << index)) choices *= multiplicity[index];
		}
		total += choices;
		if (cover.size == 3) triples += choices;
	}
	return {total, triples};
}

void enumerate_branch(
	int low_count,
	const std::vector<int> &allowed,
	int position,
	BranchSummary &summary
)
{
	if (position == static_cast<int>(allowed.size())) {
		for (int vertex = 0; vertex < low_count; ++vertex) {
			if (degree[vertex] != 3) return;
		}
		for (int vertex = low_count; vertex < VERTICES; ++vertex) {
			if (degree[vertex] < 4) return;
		}
		++summary.degree_vectors;
		const int matching = matching_number();
		const auto [blockers, triples] = blocker_counts();
		++summary.core_matching_histogram[matching];
		summary.core_minimum_blockers[matching] =
			std::min(summary.core_minimum_blockers[matching], blockers);
		if (!is_clutter()) return;
		++summary.clutter_vectors;
		++summary.clutter_matching_histogram[matching];
		summary.clutter_minimum_blockers[matching] =
			std::min(summary.clutter_minimum_blockers[matching], blockers);
		if (matching == 2 && blockers == 10 && triples == 0) ++summary.target_kernels;
		return;
	}

	const int index = allowed[position];
	int capacity = 3;
	for (int vertex = 0; vertex < low_count; ++vertex) {
		if (support_masks[index] & (1 << vertex)) {
			capacity = std::min(capacity, 3 - degree[vertex]);
		}
	}
	for (int value = 0; value <= capacity; ++value) {
		multiplicity[index] = value;
		for (int vertex = 0; vertex < VERTICES; ++vertex) {
			if (support_masks[index] & (1 << vertex)) degree[vertex] += value;
		}
		enumerate_branch(low_count, allowed, position + 1, summary);
		for (int vertex = 0; vertex < VERTICES; ++vertex) {
			if (support_masks[index] & (1 << vertex)) degree[vertex] -= value;
		}
	}
	multiplicity[index] = 0;
}

BranchSummary run_branch(int low_count)
{
	std::vector<int> allowed;
	const int low_mask = (1 << low_count) - 1;
	for (int index = 0; index < SUPPORTS; ++index) {
		if (support_masks[index] & low_mask) allowed.push_back(index);
	}
	degree.fill(0);
	multiplicity.fill(0);
	BranchSummary summary;
	summary.core_minimum_blockers.fill(std::numeric_limits<std::uint64_t>::max());
	summary.clutter_minimum_blockers.fill(std::numeric_limits<std::uint64_t>::max());
	enumerate_branch(low_count, allowed, 0, summary);
	return summary;
}

int main(int argc, char **argv)
{
	if (argc != 2) {
		std::cerr << "usage: middle-six-ten-low-degree OUTPUT\n";
		return 2;
	}
	initialize_supports();
	initialize_covers();
	std::array<BranchSummary, 3> summaries;
	for (int low_count = 4; low_count <= 6; ++low_count) {
		summaries[low_count - 4] = run_branch(low_count);
	}

	std::ofstream output(argv[1]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "schema=p0054.g4.12.middle-six-ten-low-degree.v1\n";
	output << "supports=" << SUPPORTS << '\n';
	output << "minimal_support_covers=" << covers.size() << '\n';
	for (int low_count = 4; low_count <= 6; ++low_count) {
		const BranchSummary &summary = summaries[low_count - 4];
		const std::string prefix = "low_" + std::to_string(low_count) + '_';
		output << prefix << "degree_vectors=" << summary.degree_vectors << '\n';
		output << prefix << "clutter_vectors=" << summary.clutter_vectors << '\n';
		for (const std::string kind : {"core", "clutter"}) {
			const auto &histogram = kind == "core" ? summary.core_matching_histogram
				: summary.clutter_matching_histogram;
			const auto &minima = kind == "core" ? summary.core_minimum_blockers
				: summary.clutter_minimum_blockers;
			for (int matching = 0; matching <= 3; ++matching) {
				if (!histogram[matching]) continue;
				output << prefix << kind << "_matching_" << matching << "_vectors="
					<< histogram[matching] << '\n';
				output << prefix << kind << "_matching_" << matching
					<< "_minimum_blockers=" << minima[matching] << '\n';
			}
		}
		output << prefix << "target_ten_blocker_kernels=" << summary.target_kernels << '\n';
	}
	std::cout << "output=" << argv[1] << '\n';
	return 0;
}
