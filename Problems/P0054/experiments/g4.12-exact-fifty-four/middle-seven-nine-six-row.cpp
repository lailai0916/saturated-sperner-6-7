#include <algorithm>
#include <array>
#include <bit>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

constexpr int FULL = 63;

using Profile = std::vector<int>;

int transform(int support, const std::array<int, 3> &permutation)
{
	int image = 0;
	for (int row = 0; row < 3; ++row) {
		if (support & (1 << row)) image |= 1 << permutation[row];
	}
	return image;
}

Profile canonical_profile(const std::array<int, 7> &multiplicity)
{
	Profile best;
	bool has_best = false;
	std::array<int, 3> permutation{0, 1, 2};
	do {
		Profile current;
		for (int support = 1; support < 7; ++support) {
			for (int copy = 0; copy < multiplicity[support]; ++copy) {
				current.push_back(transform(support, permutation));
			}
		}
		std::sort(current.begin(), current.end());
		if (!has_best || current < best) {
			best = current;
			has_best = true;
		}
	} while (std::next_permutation(permutation.begin(), permutation.end()));
	return best;
}

std::string profile_key(const Profile &profile)
{
	std::ostringstream output;
	for (int support = 1; support < 7; ++support) {
		int count = std::count(profile.begin(), profile.end(), support);
		if (count) output << support << ':' << count << ',';
	}
	return output.str();
}

int pair_blockers(const Profile &supports)
{
	int count = 0;
	for (int left = 0; left < static_cast<int>(supports.size()); ++left) {
		for (int right = left + 1; right < static_cast<int>(supports.size()); ++right) {
			if ((supports[left] | supports[right]) == FULL) ++count;
		}
	}
	return count;
}

void enumerate_matchings(
	const Profile &left,
	const Profile &right,
	int position,
	std::vector<bool> &used,
	Profile &combined,
	std::map<int, std::uint64_t> &histogram
)
{
	if (position == static_cast<int>(left.size())) {
		Profile supports{7, 56};
		supports.insert(supports.end(), combined.begin(), combined.end());
		for (int index = 0; index < static_cast<int>(right.size()); ++index) {
			if (!used[index]) supports.push_back(right[index] << 3);
		}
		++histogram[pair_blockers(supports)];
		return;
	}

	combined.push_back(left[position]);
	enumerate_matchings(left, right, position + 1, used, combined, histogram);
	combined.pop_back();

	for (int index = 0; index < static_cast<int>(right.size()); ++index) {
		if (used[index]) continue;
		if (std::popcount(static_cast<unsigned>(left[position]))
			+ std::popcount(static_cast<unsigned>(right[index])) > 4) {
			continue;
		}
		used[index] = true;
		combined.push_back(left[position] | (right[index] << 3));
		enumerate_matchings(left, right, position + 1, used, combined, histogram);
		combined.pop_back();
		used[index] = false;
	}
}

int main(int argc, char **argv)
{
	if (argc != 2) {
		std::cerr << "usage: middle-seven-nine-six-row OUTPUT\n";
		return 2;
	}

	std::set<Profile> profiles;
	std::uint64_t labelled_solutions = 0;
	for (int p = 0; p <= 5; ++p) {
		for (int q = 0; q <= 5; ++q) {
			for (int r = 0; r <= 5; ++r) {
				for (int x = 0; x <= 5; ++x) {
					for (int y = 0; y <= 5; ++y) {
						for (int z = 0; z <= 5; ++z) {
							std::array<int, 3> sizes{p + x + y, q + x + z, r + y + z};
							if (std::ranges::any_of(sizes, [](int size) {
								return size < 2 || size > 5;
							})) continue;
							if (!(p + y) || !(q + z) || !(p + x) || !(r + z)
								|| !(q + x) || !(r + y)) {
								continue;
							}
							int pairs = x * y + x * z + y * z + x * r + y * q + z * p;
							int triples = p * q * r;
							if (pairs + triples > 4) continue;
							++labelled_solutions;
							std::array<int, 7> multiplicity{};
							multiplicity[1] = p;
							multiplicity[2] = q;
							multiplicity[4] = r;
							multiplicity[3] = x;
							multiplicity[5] = y;
							multiplicity[6] = z;
							profiles.insert(canonical_profile(multiplicity));
						}
					}
				}
			}
		}
	}

	std::map<int, std::uint64_t> histogram;
	for (Profile left : profiles) {
		left.push_back(7);
		for (Profile right : profiles) {
			right.push_back(7);
			std::vector<bool> used(right.size());
			Profile combined;
			enumerate_matchings(left, right, 0, used, combined, histogram);
		}
	}

	std::ofstream output(argv[1]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "schema=p0054.g4.12.middle-seven-nine-six-row.v1\n";
	output << "marginal_labelled_solutions=" << labelled_solutions << '\n';
	output << "marginal_row_permutation_classes=" << profiles.size() << '\n';
	int class_index = 0;
	for (const Profile &profile : profiles) {
		output << "class_" << ++class_index << '=' << profile_key(profile) << '\n';
	}
	std::uint64_t couplings = 0;
	for (const auto &[pairs, count] : histogram) {
		output << "pair_blockers_" << pairs << '=' << count << '\n';
		couplings += count;
	}
	output << "labelled_couplings=" << couplings << '\n';
	output << "minimum_pair_blockers=" << histogram.begin()->first << '\n';
	std::cout << "output=" << argv[1] << '\n';
	return 0;
}
