#include <algorithm>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Mask = std::uint64_t;

struct Summary {
	std::uint64_t candidates = 0;
	std::uint64_t valid = 0;
};

int size(Mask mask)
{
	return std::popcount(mask);
}

std::vector<Mask> minimize(std::vector<Mask> rows)
{
	std::sort(rows.begin(), rows.end(), [](Mask left, Mask right) {
		return std::make_pair(size(left), left) < std::make_pair(size(right), right);
	});
	rows.erase(std::unique(rows.begin(), rows.end()), rows.end());
	std::vector<Mask> result;
	for (Mask row : rows) {
		bool dominated = false;
		for (Mask previous : result) {
			if ((previous & row) == previous) {
				dominated = true;
				break;
			}
		}
		if (!dominated) result.push_back(row);
	}
	return result;
}

std::vector<Mask> blockers(const std::vector<Mask> &rows)
{
	std::vector<Mask> candidates{0};
	for (Mask row : rows) {
		std::vector<Mask> expanded;
		for (Mask candidate : candidates) {
			if (candidate & row) {
				expanded.push_back(candidate);
				continue;
			}
			for (int point = 0; point < 64; ++point) {
				if (row & (Mask{1} << point)) {
					expanded.push_back(candidate | (Mask{1} << point));
				}
			}
		}
		candidates = minimize(std::move(expanded));
	}
	return candidates;
}

bool is_clutter(const std::vector<Mask> &rows)
{
	for (int left = 0; left < static_cast<int>(rows.size()); ++left) {
		for (int right = 0; right < static_cast<int>(rows.size()); ++right) {
			if (left != right && (rows[left] & rows[right]) == rows[left]) return false;
		}
	}
	return true;
}

std::vector<int> degrees(const std::vector<Mask> &rows, int point_count)
{
	std::vector<int> result(point_count);
	for (Mask row : rows) {
		for (int point = 0; point < point_count; ++point) {
			if (row & (Mask{1} << point)) ++result[point];
		}
	}
	return result;
}

bool contains_all(const std::vector<Mask> &rows, const std::vector<Mask> &kernel)
{
	for (Mask row : kernel) {
		if (std::find(rows.begin(), rows.end(), row) == rows.end()) return false;
	}
	return true;
}

std::vector<int> points(Mask row)
{
	std::vector<int> result;
	for (int point = 0; point < 64; ++point) {
		if (row & (Mask{1} << point)) result.push_back(point);
	}
	return result;
}

bool valid_extension(
	const std::vector<Mask> &rows,
	const std::vector<Mask> &kernel,
	int point_count,
	int x
)
{
	if (rows.size() != 9 || !is_clutter(rows)) return false;
	for (Mask row : rows) {
		if (size(row) < 3 || size(row) > 7) return false;
	}
	const std::vector<int> row_degrees = degrees(rows, point_count);
	if (*std::max_element(row_degrees.begin(), row_degrees.end()) > 4) return false;
	const std::vector<Mask> dual = blockers(rows);
	if (dual.size() != 7 || !contains_all(dual, kernel)) return false;
	for (Mask row : dual) {
		if (size(row) < 3 || size(row) > 9) return false;
	}
	const std::vector<int> dual_degrees = degrees(dual, point_count);
	if (*std::max_element(dual_degrees.begin(), dual_degrees.end()) > 3) return false;
	return dual_degrees[x] == 3;
}

void test_candidate(
	const std::vector<Mask> &rows,
	const std::vector<Mask> &kernel,
	int point_count,
	int x,
	Summary &summary
)
{
	if (!is_clutter(rows)) return;
	++summary.candidates;
	if (valid_extension(rows, kernel, point_count, x)) ++summary.valid;
}

void enumerate_one_row(
	const std::vector<Mask> &base,
	const std::vector<Mask> &kernel,
	int x,
	Summary &summary
)
{
	const std::vector<int> base_degrees = degrees(base, x + 1);
	std::vector<int> eligible;
	for (int point = 0; point <= x; ++point) {
		if (base_degrees[point] < 4) eligible.push_back(point);
	}
	for (std::uint64_t chosen = 0;
		chosen < (std::uint64_t{1} << eligible.size()); ++chosen) {
		Mask row = 0;
		for (int index = 0; index < static_cast<int>(eligible.size()); ++index) {
			if (chosen & (std::uint64_t{1} << index)) {
				row |= Mask{1} << eligible[index];
			}
		}
		for (int fresh = 0; size(row) + fresh <= 7; ++fresh) {
			if (size(row) + fresh < 3) continue;
			Mask extra = row;
			for (int index = 0; index < fresh; ++index) {
				extra |= Mask{1} << (x + 1 + index);
			}
			std::vector<Mask> rows = base;
			rows.push_back(extra);
			test_candidate(rows, kernel, x + 1 + fresh, x, summary);
		}
	}
}

void enumerate_two_row_patterns(
	const std::vector<Mask> &base,
	const std::vector<Mask> &kernel,
	const std::vector<int> &base_degrees,
	int x,
	int point,
	Mask first,
	Mask second,
	Summary &summary
)
{
	if (point <= x) {
		for (int pattern = 0; pattern < 4; ++pattern) {
			int added = bool(pattern & 1) + bool(pattern & 2);
			if (base_degrees[point] + added > 4) continue;
			enumerate_two_row_patterns(
				base,
				kernel,
				base_degrees,
				x,
				point + 1,
				first | ((pattern & 1) ? Mask{1} << point : 0),
				second | ((pattern & 2) ? Mask{1} << point : 0),
				summary
			);
		}
		return;
	}

	for (int first_private = 0; size(first) + first_private <= 7;
		++first_private) {
		for (int second_private = 0; size(second) + second_private <= 7;
			++second_private) {
			int max_shared = std::min(
				7 - size(first) - first_private,
				7 - size(second) - second_private
			);
			for (int shared = 0; shared <= max_shared; ++shared) {
				if (size(first) + first_private + shared < 3) continue;
				if (size(second) + second_private + shared < 3) continue;
				int next = x + 1;
				Mask first_row = first;
				for (int index = 0; index < first_private; ++index) {
					first_row |= Mask{1} << next++;
				}
				Mask second_row = second;
				for (int index = 0; index < second_private; ++index) {
					second_row |= Mask{1} << next++;
				}
				for (int index = 0; index < shared; ++index) {
					first_row |= Mask{1} << next;
					second_row |= Mask{1} << next++;
				}
				const std::vector<int> first_points = points(first_row);
				const std::vector<int> second_points = points(second_row);
				if (std::lexicographical_compare(
					second_points.begin(),
					second_points.end(),
					first_points.begin(),
					first_points.end()
				)) continue;
				std::vector<Mask> rows = base;
				rows.push_back(first_row);
				rows.push_back(second_row);
				test_candidate(rows, kernel, next, x, summary);
			}
		}
	}
}

std::vector<std::string> read_classes(const std::string &path)
{
	std::ifstream input(path);
	if (!input) throw std::runtime_error("cannot open kernel results");
	std::vector<std::string> result;
	std::string line;
	while (std::getline(input, line)) {
		if (line.rfind("class_", 0) == 0) {
			result.push_back(line.substr(line.find('=') + 1));
		}
	}
	return result;
}

std::pair<std::vector<Mask>, int> kernel_from_key(const std::string &key)
{
	std::vector<int> supports;
	std::size_t position = 0;
	const std::size_t end = key.find('|');
	while (position < end) {
		const std::size_t colon = key.find(':', position);
		const std::size_t comma = key.find(',', colon);
		const std::size_t next = std::min(comma, end);
		int support = std::stoi(key.substr(position, colon - position));
		int count = std::stoi(key.substr(colon + 1, next - colon - 1));
		for (int copy = 0; copy < count; ++copy) supports.push_back(support);
		position = next + 1;
	}
	std::vector<Mask> rows(4);
	for (int point = 0; point < static_cast<int>(supports.size()); ++point) {
		for (int row = 0; row < 4; ++row) {
			if (supports[point] & (1 << row)) rows[row] |= Mask{1} << point;
		}
	}
	return {rows, supports.size()};
}

Summary check_class(const std::string &key)
{
	const auto [kernel, old_points] = kernel_from_key(key);
	const std::vector<Mask> kernel_blockers = blockers(kernel);
	const int x = old_points;
	std::vector<Mask> pairs;
	std::vector<Mask> others;
	for (Mask row : kernel_blockers) {
		if (size(row) == 2) pairs.push_back(row);
		else others.push_back(row);
	}
	if (pairs.size() != 3 && pairs.size() != 4) {
		throw std::runtime_error("unexpected pair-blocker count");
	}

	Summary summary;
	int first_added = -1;
	int last_added = pairs.size() == 3 ? static_cast<int>(others.size()) - 1 : -1;
	for (int added = first_added; added <= last_added; ++added) {
		std::vector<Mask> base;
		for (Mask row : pairs) base.push_back(row | (Mask{1} << x));
		for (int index = 0; index < static_cast<int>(others.size()); ++index) {
			base.push_back(others[index] | (index == added ? Mask{1} << x : 0));
		}
		int extras = 9 - base.size();
		if (extras == 0) {
			test_candidate(base, kernel, x + 1, x, summary);
		} else if (extras == 1) {
			enumerate_one_row(base, kernel, x, summary);
		} else if (extras == 2) {
			const std::vector<int> base_degrees = degrees(base, x + 1);
			enumerate_two_row_patterns(
				base, kernel, base_degrees, x, 0, 0, 0, summary
			);
		} else {
			throw std::runtime_error("unexpected kernel blocker count");
		}
	}
	return summary;
}

int main(int argc, char **argv)
{
	if (argc != 3) {
		std::cerr << "usage: middle-seven-nine-extension KERNEL_RESULTS OUTPUT\n";
		return 2;
	}
	const std::vector<std::string> classes = read_classes(argv[1]);
	if (classes.size() != 11) throw std::runtime_error("expected eleven classes");
	std::ofstream output(argv[2]);
	if (!output) {
		std::cerr << "cannot open output\n";
		return 2;
	}
	output << "schema=p0054.g4.12.middle-seven-nine-extension-cpp.v1\n";
	output << "kernel_classes=" << classes.size() << '\n';
	std::uint64_t candidates = 0;
	std::uint64_t valid = 0;
	for (int index = 0; index < static_cast<int>(classes.size()); ++index) {
		const Summary summary = check_class(classes[index]);
		output << "class_" << index + 1 << "_extension_candidates="
			<< summary.candidates << '\n';
		output << "class_" << index + 1 << "_valid_extensions="
			<< summary.valid << '\n';
		candidates += summary.candidates;
		valid += summary.valid;
	}
	output << "extension_candidates=" << candidates << '\n';
	output << "valid_extensions=" << valid << '\n';
	std::cout << "output=" << argv[2] << '\n';
	return 0;
}
