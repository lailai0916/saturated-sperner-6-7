#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

using Vector = std::array<int, 15>;

std::array<int, 14> supports{};
Vector multiplicity{};
std::array<int, 4> degree{};
std::uint64_t degree_feasible_vectors = 0;
std::uint64_t valid_clutters = 0;
std::map<int, std::uint64_t> blocker_histogram;
std::map<std::string, std::uint64_t> equality_classes;
std::set<std::string> low_classes;

bool is_clutter() {
	for (int left = 0; left < 4; ++left) {
		for (int right = 0; right < 4; ++right) {
			if (left == right) continue;
			bool subset = true;
			for (int support : supports) {
				if (multiplicity[support] && (support & (1 << left)) && !(support & (1 << right))) {
					subset = false;
					break;
				}
			}
			if (subset) return false;
		}
	}
	return true;
}

std::pair<int, std::map<int, int>> blocker_data() {
	std::vector<int> active;
	for (int support : supports) {
		if (multiplicity[support]) active.push_back(support);
	}
	int total = 0;
	std::map<int, int> sizes;
	for (int chosen = 1; chosen < (1 << active.size()); ++chosen) {
		int cover = 0;
		for (int index = 0; index < static_cast<int>(active.size()); ++index) {
			if (chosen & (1 << index)) cover |= active[index];
		}
		if (cover != 15) continue;
		bool minimal = true;
		for (int index = 0; index < static_cast<int>(active.size()); ++index) {
			if (!(chosen & (1 << index))) continue;
			int without = 0;
			for (int other = 0; other < static_cast<int>(active.size()); ++other) {
				if (other != index && (chosen & (1 << other))) without |= active[other];
			}
			if (without == 15) {
				minimal = false;
				break;
			}
		}
		if (!minimal) continue;
		int choices = 1;
		int size = 0;
		for (int index = 0; index < static_cast<int>(active.size()); ++index) {
			if (chosen & (1 << index)) {
				choices *= multiplicity[active[index]];
				++size;
			}
		}
		total += choices;
		sizes[size] += choices;
		if (total > 7) return {total, sizes};
	}
	return {total, sizes};
}

std::string canonical_key(const std::map<int, int>& sizes) {
	std::string best;
	std::array<int, 4> permutation{0, 1, 2, 3};
	do {
		std::vector<std::pair<int, int>> transformed;
		for (int support = 1; support < 15; ++support) {
			if (!multiplicity[support]) continue;
			int image = 0;
			for (int row = 0; row < 4; ++row) {
				if (support & (1 << row)) image |= 1 << permutation[row];
			}
			transformed.push_back({image, multiplicity[support]});
		}
		std::sort(transformed.begin(), transformed.end());
		std::ostringstream out;
		for (auto [image, value] : transformed) out << image << ':' << value << ',';
		if (best.empty() || out.str() < best) best = out.str();
	} while (std::next_permutation(permutation.begin(), permutation.end()));
	std::ostringstream suffix;
	for (auto [size, count] : sizes) suffix << '|' << size << ':' << count;
	return best + suffix.str();
}

void visit(int position) {
	if (position == 14) {
		for (int row = 0; row < 4; ++row) {
			if (degree[row] < 3 || degree[row] > 7) return;
		}
		++degree_feasible_vectors;
		if (!is_clutter()) return;
		++valid_clutters;
		auto [count, sizes] = blocker_data();
		if (count <= 7) ++blocker_histogram[count];
		if (count <= 6) low_classes.insert(canonical_key(sizes));
		if (count == 7) ++equality_classes[canonical_key(sizes)];
		return;
	}

	int support = supports[position];
	int capacity = 7;
	for (int row = 0; row < 4; ++row) {
		if (support & (1 << row)) capacity = std::min(capacity, 7 - degree[row]);
	}
	for (int value = 0; value <= capacity; ++value) {
		multiplicity[support] = value;
		for (int row = 0; row < 4; ++row) {
			if (support & (1 << row)) degree[row] += value;
		}
		bool feasible = true;
		for (int row = 0; row < 4; ++row) {
			if (degree[row] >= 3) continue;
			bool can_grow = false;
			for (int later = position + 1; later < 14; ++later) {
				if (supports[later] & (1 << row)) can_grow = true;
			}
			if (!can_grow) feasible = false;
		}
		if (feasible) visit(position + 1);
		for (int row = 0; row < 4; ++row) {
			if (support & (1 << row)) degree[row] -= value;
		}
	}
	multiplicity[support] = 0;
}

int main(int argc, char** argv) {
	if (argc != 2) {
		std::cerr << "usage: four-row-kernel OUTPUT\n";
		return 2;
	}
	std::vector<int> ordered;
	for (int support = 1; support < 15; ++support) ordered.push_back(support);
	std::sort(ordered.begin(), ordered.end(), [](int left, int right) {
		return std::make_pair(__builtin_popcount(static_cast<unsigned>(left)), left)
			> std::make_pair(__builtin_popcount(static_cast<unsigned>(right)), right);
	});
	std::copy(ordered.begin(), ordered.end(), supports.begin());
	visit(0);

	std::ofstream output(argv[1]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "degree_feasible_vectors=" << degree_feasible_vectors << '\n';
	output << "valid_clutters=" << valid_clutters << '\n';
	for (auto [count, vectors] : blocker_histogram) {
		output << "blocker_count=" << count << " vectors=" << vectors << '\n';
	}
	output << "low_isomorphism_classes=" << low_classes.size() << '\n';
	output << "equality_isomorphism_classes=" << equality_classes.size() << '\n';
	for (const auto& key : low_classes) output << "low_key=" << key << '\n';
	for (const auto& [key, hits] : equality_classes) {
		output << "equality_key=" << key << " orbit_hits=" << hits << '\n';
	}
	std::cout << "output=" << argv[1] << '\n';
	std::cout << "kernel_classes=" << low_classes.size() + equality_classes.size() << '\n';
}
