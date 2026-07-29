'use strict';

const A = 1;
const P = 2;
const Q = 4;

const REPRESENTATIVES = [
  [10, 10, 13, 18, 21],
  [10, 11, 13, 18, 21],
  [10, 13, 13, 18, 21],
  [10, 13, 15, 18, 21],
  [10, 13, 18, 21, 26],
  [10, 13, 18, 21, 27],
  [10, 13, 18, 21, 29],
  [10, 13, 18, 21, 31],
  [10, 13, 19, 21, 22],
];

const EXPECTED_EXCLUDED = [2, 3, 4, 6, 7, 8, 9];

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function lemmaRows(rows, endpoint) {
  const missing = rows
    .map((row, index) => ({ row, index }))
    .filter(({ row }) => (row & endpoint) === 0);

  if (missing.length !== 2) return null;
  if (missing.some(({ row }) => (row & P) === 0)) return null;
  if ((missing[0].row & missing[1].row) !== P) return null;
  return missing.map(({ index }) => index);
}

const audit = REPRESENTATIVES.map((rows, index) => ({
  class: index + 1,
  a_missing_rows: lemmaRows(rows, A),
  q_missing_rows: lemmaRows(rows, Q),
}));

const excluded = audit
  .filter((entry) => entry.a_missing_rows !== null || entry.q_missing_rows !== null)
  .map((entry) => entry.class);

assert(
  JSON.stringify(excluded) === JSON.stringify(EXPECTED_EXCLUDED),
  `unexpected excluded classes: ${JSON.stringify(excluded)}`,
);
assert(
  audit.filter((entry) => EXPECTED_EXCLUDED.includes(entry.class))
    .every((entry) => entry.a_missing_rows !== null),
  'the advertised endpoint a does not certify every excluded class',
);

console.log(JSON.stringify({
  schema: 'p0054.g4.13.p3k2-upstream-lemma-audit.v1',
  epistemic_label: 'PROVED_CANDIDATE_REPAIRED_LEMMA_PLUS_COMPUTED_EXACT_MAP',
  representatives: audit,
  excluded_classes: excluded,
  surviving_classes: audit
    .filter((entry) => !excluded.includes(entry.class))
    .map((entry) => entry.class),
  mismatches: 0,
}, null, 2));
