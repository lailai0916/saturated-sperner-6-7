#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

constexpr int N = 7;
constexpr int FULL = 127;
constexpr int X_SUPPORT = 112;

std::vector<int> rank3_supports;
std::array<int, 128> support_index{};
std::array<int, 128> multiplicity{};
std::array<int, N> degree{};
std::unordered_map<std::uint64_t, std::vector<std::uint64_t>> cover_cache;
std::set<std::string> valid_vectors;
std::set<std::string> non_fano_vectors;
std::uint64_t class_nodes = 0;
std::uint64_t new_point_nodes = 0;
std::uint64_t blocker_prunes = 0;

std::vector<std::uint64_t> minimalize(std::vector<std::uint64_t> values) {
	std::sort(values.begin(), values.end(), [](auto left, auto right) {
		return std::make_pair(__builtin_popcountll(left), left)
			< std::make_pair(__builtin_popcountll(right), right);
	});
	values.erase(std::unique(values.begin(), values.end()), values.end());
	std::vector<std::uint64_t> result;
	for (auto value : values) {
		if (std::none_of(result.begin(), result.end(), [&](auto old) {
			return (old & value) == old;
		})) {
			result.push_back(value);
		}
	}
	return result;
}

std::pair<int, std::vector<std::uint64_t>> blocker_data() {
	std::uint64_t active = 0;
	for (int mask : rank3_supports) {
		if (multiplicity[mask]) active |= std::uint64_t{1} << support_index[mask];
	}
	auto found = cover_cache.find(active);
	std::vector<std::uint64_t> covers;
	if (found != cover_cache.end()) {
		covers = found->second;
	} else {
		covers = {0};
		for (int row = 0; row < N; ++row) {
			std::vector<std::uint64_t> expanded;
			for (auto cover : covers) {
				int united = 0;
				for (int mask : rank3_supports) {
					if (cover & (std::uint64_t{1} << support_index[mask])) united |= mask;
				}
				if (united & (1 << row)) {
					expanded.push_back(cover);
				} else {
					for (int mask : rank3_supports) {
						std::uint64_t bit = std::uint64_t{1} << support_index[mask];
						if ((active & bit) && (mask & (1 << row))) expanded.push_back(cover | bit);
					}
				}
			}
			covers = minimalize(std::move(expanded));
		}
		if (cover_cache.size() < 1000000) cover_cache.emplace(active, covers);
	}
	int total = 0;
	for (auto cover : covers) {
		int choices = 1;
		for (int mask : rank3_supports) {
			if (cover & (std::uint64_t{1} << support_index[mask])) choices *= multiplicity[mask];
		}
		total += choices;
		if (total > 7) break;
	}
	return {total, covers};
}

bool is_clutter() {
	for (int left = 0; left < N; ++left) {
		for (int right = 0; right < N; ++right) {
			if (left == right) continue;
			bool subset = true;
			for (int mask : rank3_supports) {
				if (multiplicity[mask] && (mask & (1 << left)) && !(mask & (1 << right))) {
					subset = false;
					break;
				}
			}
			if (subset) return false;
		}
	}
	return true;
}

bool is_fano() {
	int points = 0;
	for (int mask : rank3_supports) {
		points += multiplicity[mask];
		if (multiplicity[mask]
			&& (multiplicity[mask] != 1 || __builtin_popcount(static_cast<unsigned>(mask)) != 3)) {
			return false;
		}
	}
	if (points != 7) return false;
	for (int row = 0; row < N; ++row) {
		if (degree[row] != 3) return false;
	}
	for (int left = 0; left < N; ++left) {
		for (int right = left + 1; right < N; ++right) {
			int intersection = 0;
			for (int mask : rank3_supports) {
				if ((mask & (1 << left)) && (mask & (1 << right))) {
					intersection += multiplicity[mask];
				}
			}
			if (intersection != 1) return false;
		}
	}
	return true;
}

std::string vector_key() {
	std::ostringstream out;
	for (int mask : rank3_supports) {
		if (multiplicity[mask]) out << mask << ':' << multiplicity[mask] << ',';
	}
	return out.str();
}

void enumerate_new_points(int position, const std::array<int, 7>& new_masks) {
	++new_point_nodes;
	if (position == 7) {
		for (int row = 4; row < N; ++row) {
			if (degree[row] < 3 || degree[row] > 7) return;
		}
		if (!is_clutter()) return;
		auto [count, covers] = blocker_data();
		if (count != 7) return;
		bool has_triple_blocker = false;
		for (auto cover : covers) {
			if (__builtin_popcountll(cover) == 3) has_triple_blocker = true;
		}
		if (!has_triple_blocker) return;
		std::string key = vector_key();
		valid_vectors.insert(key);
		if (!is_fano()) non_fano_vectors.insert(key);
		return;
	}

	int mask = new_masks[position];
	int capacity = 7;
	for (int row = 4; row < N; ++row) {
		if (mask & (1 << row)) capacity = std::min(capacity, 7 - degree[row]);
	}
	int original = multiplicity[mask];
	for (int added = 0; added <= capacity; ++added) {
		multiplicity[mask] = original + added;
		for (int row = 4; row < N; ++row) {
			if (mask & (1 << row)) degree[row] += added;
		}
		bool recurse = true;
		if (added) {
			auto [count, ignored] = blocker_data();
			if (count > 7) {
				recurse = false;
				++blocker_prunes;
			}
		}
		if (recurse) enumerate_new_points(position + 1, new_masks);
		for (int row = 4; row < N; ++row) {
			if (mask & (1 << row)) degree[row] -= added;
		}
	}
	multiplicity[mask] = original;
}

void distribute_class(
	const std::vector<std::pair<int, int>>& classes,
	int position,
	const std::array<int, 7>& new_masks
) {
	++class_nodes;
	if (position == static_cast<int>(classes.size())) {
		auto [count, ignored] = blocker_data();
		if (count > 7) {
			++blocker_prunes;
			return;
		}
		enumerate_new_points(0, new_masks);
		return;
	}

	int kernel_mask = classes[position].first;
	int total = classes[position].second;
	int allowance = 3 - __builtin_popcount(static_cast<unsigned>(kernel_mask));
	std::vector<int> options;
	for (int suffix = 0; suffix < 8; ++suffix) {
		if (__builtin_popcount(static_cast<unsigned>(suffix)) <= allowance) options.push_back(suffix);
	}
	std::vector<int> assigned(options.size());
	std::function<void(int, int)> fill = [&](int option, int remaining) {
		if (option + 1 == static_cast<int>(options.size())) {
			assigned[option] = remaining;
			for (int index = 0; index < static_cast<int>(options.size()); ++index) {
				int full_mask = kernel_mask | (options[index] << 4);
				multiplicity[full_mask] += assigned[index];
				for (int row = 0; row < N; ++row) {
					if (full_mask & (1 << row)) degree[row] += assigned[index];
				}
			}
			bool feasible = true;
			for (int row = 4; row < N; ++row) {
				if (degree[row] > 7) feasible = false;
			}
			if (feasible) distribute_class(classes, position + 1, new_masks);
			for (int index = 0; index < static_cast<int>(options.size()); ++index) {
				int full_mask = kernel_mask | (options[index] << 4);
				multiplicity[full_mask] -= assigned[index];
				for (int row = 0; row < N; ++row) {
					if (full_mask & (1 << row)) degree[row] -= assigned[index];
				}
			}
			return;
		}
		for (int value = 0; value <= remaining; ++value) {
			assigned[option] = value;
			fill(option + 1, remaining - value);
		}
	};
	fill(0, total);
}

std::vector<std::vector<std::pair<int, int>>> read_kernels(const std::string& path) {
	std::ifstream input(path);
	if (!input) throw std::runtime_error("cannot open kernel report");
	std::set<std::string> keys;
	std::string line;
	while (std::getline(input, line)) {
		std::string prefix;
		if (line.rfind("low_key=", 0) == 0) prefix = "low_key=";
		if (line.rfind("equality_key=", 0) == 0) prefix = "equality_key=";
		if (prefix.empty()) continue;
		std::string key = line.substr(prefix.size());
		key = key.substr(0, key.find('|'));
		keys.insert(key);
	}
	std::vector<std::vector<std::pair<int, int>>> kernels;
	for (const auto& key : keys) {
		std::vector<std::pair<int, int>> kernel;
		std::stringstream row(key);
		std::string term;
		while (std::getline(row, term, ',')) {
			if (term.empty()) continue;
			auto colon = term.find(':');
			kernel.push_back({std::stoi(term.substr(0, colon)), std::stoi(term.substr(colon + 1))});
		}
		kernels.push_back(kernel);
	}
	if (kernels.size() != 41) throw std::runtime_error("expected 41 kernel classes");
	return kernels;
}

int main(int argc, char** argv) {
	if (argc != 3) {
		std::cerr << "usage: seven-row-extension FOUR_ROW_REPORT OUTPUT\n";
		return 2;
	}
	support_index.fill(-1);
	for (int mask = 1; mask <= FULL; ++mask) {
		if (__builtin_popcount(static_cast<unsigned>(mask)) <= 3) {
			support_index[mask] = rank3_supports.size();
			rank3_supports.push_back(mask);
		}
	}
	const std::array<int, 7> new_masks{16, 32, 64, 48, 80, 96, 112};
	auto kernels = read_kernels(argv[1]);
	for (const auto& kernel : kernels) {
		multiplicity.fill(0);
		degree.fill(0);
		multiplicity[X_SUPPORT] = 1;
		for (int row = 4; row < N; ++row) degree[row] = 1;
		distribute_class(kernel, 0, new_masks);
	}
	std::ofstream output(argv[2]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "kernels=" << kernels.size() << '\n';
	output << "class_nodes=" << class_nodes << '\n';
	output << "new_point_nodes=" << new_point_nodes << '\n';
	output << "blocker_prunes=" << blocker_prunes << '\n';
	output << "valid_vectors=" << valid_vectors.size() << '\n';
	output << "non_fano_vectors=" << non_fano_vectors.size() << '\n';
	for (const auto& key : valid_vectors) output << "valid=" << key << '\n';
	for (const auto& key : non_fano_vectors) output << "non_fano=" << key << '\n';
	std::cout << "output=" << argv[2] << '\n';
	std::cout << "valid_vectors=" << valid_vectors.size() << '\n';
	std::cout << "non_fano_vectors=" << non_fano_vectors.size() << '\n';
}
