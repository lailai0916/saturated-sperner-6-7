'use strict';

const ENDPOINTS = 6;
const FULL_ROWS = 31;
const BASE_ROWS = [21, 41, 38, 26, 42];
const FIXED_PAIRS = new Set([3, 12, 48]);

function popcount(value) {
  let count = 0;
  while (value) {
    count += value & 1;
    value >>= 1;
  }
  return count;
}

function blockers(rows, pointCount) {
  const result = [];
  for (let candidate = 1; candidate < (1 << pointCount); candidate += 1) {
    if (!rows.every((row) => row & candidate)) continue;
    const minimal = [...Array(pointCount).keys()]
      .filter((point) => candidate & (1 << point))
      .every((point) => !rows.every((row) => row & (candidate ^ (1 << point))));
    if (minimal) result.push(candidate);
  }
  return result;
}

function addOutsideSupports(supports) {
  return BASE_ROWS.map((row, rowIndex) => {
    let extended = row;
    supports.forEach((support, point) => {
      if (support & (1 << rowIndex)) extended |= 1 << (ENDPOINTS + point);
    });
    return extended;
  });
}

function endpointDegrees(blockerList) {
  return [...Array(ENDPOINTS).keys()].map(
    (point) => blockerList.filter((blocker) => blocker & (1 << point)).length,
  );
}

function individuallyAdmissible(support) {
  const dual = blockers(addOutsideSupports([support]), ENDPOINTS + 1);
  const pairBlockers = new Set(
    dual.filter((blocker) => popcount(blocker) === 2),
  );
  return [...pairBlockers].every((pair) => FIXED_PAIRS.has(pair))
    && pairBlockers.size === FIXED_PAIRS.size
    && Math.max(...endpointDegrees(dual)) <= 3;
}

function cycleSupport(support, shift) {
  let result = support & 17;
  for (let row = 1; row <= 3; row += 1) {
    if (support & (1 << row)) result |= 1 << (1 + ((row - 1 + shift) % 3));
  }
  return result;
}

function supportOrbitRepresentative(support) {
  return Math.min(...[0, 1, 2].map((shift) => cycleSupport(support, shift)));
}

function permutations(values) {
  if (values.length === 0) return [[]];
  const result = [];
  for (let index = 0; index < values.length; index += 1) {
    const rest = values.slice(0, index).concat(values.slice(index + 1));
    for (const tail of permutations(rest)) result.push([values[index], ...tail]);
  }
  return result;
}

const coordinatePermutations = permutations([0, 1, 2]);

function transformWord(word, permutation, flips) {
  let result = 0;
  for (let coordinate = 0; coordinate < 3; coordinate += 1) {
    const bit = ((word >> coordinate) & 1) ^ ((flips >> coordinate) & 1);
    result |= bit << permutation[coordinate];
  }
  return result;
}

function canonicalMultiset(words) {
  let best = null;
  for (const permutation of coordinatePermutations) {
    for (let flips = 0; flips < 8; flips += 1) {
      const key = words
        .map((word) => transformWord(word, permutation, flips))
        .sort((left, right) => left - right)
        .join('');
      if (best === null || key < best) best = key;
    }
  }
  return best;
}

function fiveWordMultisets() {
  const result = [];
  function visit(start, words) {
    if (words.length === 5) {
      result.push(words);
      return;
    }
    for (let word = start; word < 8; word += 1) visit(word, [...words, word]);
  }
  visit(0, []);
  return result;
}

function isAllDProjection(words) {
  for (let coordinate = 0; coordinate < 3; coordinate += 1) {
    const ones = words.filter((word) => word & (1 << coordinate)).length;
    if (ones !== 2 && ones !== 3) return false;
  }
  for (let first = 0; first < 3; first += 1) {
    for (let second = first + 1; second < 3; second += 1) {
      const pairs = new Set(
        words.map((word) => ((word >> first) & 1) | (((word >> second) & 1) << 1)),
      );
      if (pairs.size !== 4) return false;
    }
  }
  return true;
}

const allDRows = fiveWordMultisets().filter(isAllDProjection);
const allDOrbits = new Set(allDRows.map(canonicalMultiset));
const supports = [...Array(FULL_ROWS).keys()]
  .map((value) => value + 1)
  .filter((support) => popcount(support) <= 3);
const admissibleSupports = supports.filter(individuallyAdmissible);
const onePointDual = blockers(addOutsideSupports([16]), ENDPOINTS + 1);
const twoPointDual = blockers(addOutsideSupports([16, 16]), ENDPOINTS + 2);
const r4OrbitRepresentatives = [...new Set(
  supports
    .filter((support) => support & 16)
    .map(supportOrbitRepresentative),
)].sort((left, right) => left - right);
const expectedBlockers = new Map([
  [16, 85],
  [17, 74],
  [18, 70],
  [19, 66],
  [22, 80],
]);
const explicitBlockers = [...expectedBlockers].map(([support, blocker]) => ({
  support,
  blocker,
  verified: blockers(addOutsideSupports([support]), ENDPOINTS + 1).includes(blocker),
}));

const result = {
  schema: 'p0054.g4.13.3k2-all-d-audit.v1',
  epistemic_label: 'COMPUTED_EXACT_CROSSCHECK',
  all_d_labeled_row_multisets: allDRows.length,
  all_d_cube_orbits: allDOrbits.size,
  all_d_orbit_keys: [...allDOrbits].sort(),
  rank_at_most_three_supports: supports.length,
  supports_missing_r4: supports.filter((support) => !(support & 16)).length,
  supports_containing_r4: supports.filter((support) => support & 16).length,
  support_orbit_representatives_containing_r4: r4OrbitRepresentatives,
  explicit_blockers: explicitBlockers,
  individually_admissible_supports: admissibleSupports,
  one_r4_point: {
    blockers: onePointDual.length,
    endpoint_degrees: endpointDegrees(onePointDual),
  },
  two_r4_points: {
    blockers: twoPointDual.length,
    endpoint_degrees: endpointDegrees(twoPointDual),
  },
};

if (result.all_d_cube_orbits !== 2) throw new Error('all-D orbit mismatch');
if (supports.length !== 25) throw new Error('support count mismatch');
if (result.supports_missing_r4 !== 14 || result.supports_containing_r4 !== 11) {
  throw new Error('R4 support split mismatch');
}
if (r4OrbitRepresentatives.join(',') !== '16,17,18,19,22') {
  throw new Error('R4 support orbit mismatch');
}
if (explicitBlockers.some((entry) => !entry.verified)) {
  throw new Error('explicit blocker mismatch');
}
if (admissibleSupports.length !== 1 || admissibleSupports[0] !== 16) {
  throw new Error('admissible support mismatch');
}
if (onePointDual.length !== 7 || Math.max(...endpointDegrees(onePointDual)) !== 3) {
  throw new Error('one-point kernel mismatch');
}
if (twoPointDual.length !== 8 || Math.max(...endpointDegrees(twoPointDual)) !== 4) {
  throw new Error('two-point obstruction mismatch');
}

process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
