'use strict';

const FULL = 31;
const NOTE_REPRESENTATIVES = [
  [20, 11, 20, 7, 24],
  [22, 11, 20, 7, 24],
  [22, 9, 22, 7, 24],
  [22, 13, 22, 7, 24],
  [10, 21, 10, 19, 28],
  [26, 21, 10, 19, 28],
  [26, 5, 26, 19, 28],
  [26, 21, 26, 19, 28],
  [14, 21, 26, 3, 28],
];

function popcount(value) {
  let count = 0;
  while (value) {
    count += value & 1;
    value >>= 1;
  }
  return count;
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

function permuteMask(mask, permutation) {
  let result = 0;
  for (let row = 0; row < 5; row += 1) {
    if (mask & (1 << row)) result |= 1 << permutation[row];
  }
  return result;
}

function graphAutomorphisms(tuple) {
  const [a, p, q, u, v] = tuple;
  return [
    [a, p, q, u, v],
    [q, p, a, u, v],
    [a, p, q, v, u],
    [q, p, a, v, u],
  ];
}

const rowPermutations = permutations([0, 1, 2, 3, 4]);

function canonicalKey(tuple) {
  let best = null;
  for (const relabeled of graphAutomorphisms(tuple)) {
    for (const permutation of rowPermutations) {
      const key = relabeled
        .map((mask) => permuteMask(mask, permutation))
        .map((mask) => String(mask).padStart(2, '0'))
        .join(',');
      if (best === null || key < best) best = key;
    }
  }
  return best;
}

function rowMasks(tuple) {
  const result = [];
  for (let row = 0; row < 5; row += 1) {
    let mask = 0;
    tuple.forEach((support, endpoint) => {
      if (support & (1 << row)) mask |= 1 << endpoint;
    });
    result.push(mask);
  }
  return result;
}

const supports = [];
for (let mask = 1; mask < FULL; mask += 1) {
  if ([2, 3].includes(popcount(mask))) supports.push(mask);
}

const partners = new Map(
  supports.map((support) => [
    support,
    supports.filter((candidate) => (support | candidate) === FULL),
  ]),
);

const assignments = [];
for (const p of supports) {
  for (const a of partners.get(p)) {
    for (const q of partners.get(p)) {
      if ((a | q) === FULL) continue;
      for (const u of supports) {
        if ((a | u) === FULL || (p | u) === FULL || (q | u) === FULL) continue;
        for (const v of partners.get(u)) {
          if ((a | v) === FULL || (p | v) === FULL || (q | v) === FULL) continue;
          assignments.push([a, p, q, u, v]);
        }
      }
    }
  }
}

const orbitSizes = new Map();
for (const assignment of assignments) {
  const key = canonicalKey(assignment);
  orbitSizes.set(key, (orbitSizes.get(key) || 0) + 1);
}

const representativeKeys = NOTE_REPRESENTATIVES.map(canonicalKey);
const orbitKeys = [...orbitSizes.keys()].sort();
const missingHandRepresentatives = orbitKeys.filter(
  (key) => !representativeKeys.includes(key),
);
const extraHandRepresentatives = representativeKeys.filter(
  (key) => !orbitSizes.has(key),
);

const result = {
  schema: 'p0054.g4.13.p3k2-projection-orbit-audit.v1',
  epistemic_label: 'COMPUTED_EXACT_ORBIT_CROSSCHECK',
  support_candidates: supports.length,
  labeled_legal_support_tuples: assignments.length,
  orbit_count: orbitSizes.size,
  orbit_sizes: orbitKeys.map((key) => orbitSizes.get(key)).sort((a, b) => a - b),
  distinct_hand_representatives: new Set(representativeKeys).size,
  missing_hand_representatives: missingHandRepresentatives,
  extra_hand_representatives: extraHandRepresentatives,
  classes: NOTE_REPRESENTATIVES.map((tuple, index) => ({
    class: index + 1,
    support_masks: tuple,
    row_masks: rowMasks(tuple),
    orbit_size: orbitSizes.get(canonicalKey(tuple)),
  })),
};

if (result.support_candidates !== 20) throw new Error('support candidate mismatch');
if (result.labeled_legal_support_tuples !== 1800) throw new Error('tuple count mismatch');
if (result.orbit_count !== 9) throw new Error('orbit count mismatch');
if (result.distinct_hand_representatives !== 9) throw new Error('duplicate hand orbit');
if (missingHandRepresentatives.length || extraHandRepresentatives.length) {
  throw new Error('hand/enumerated orbit mismatch');
}

process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
